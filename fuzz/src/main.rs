use std::io::Write;
use std::ops::Range;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

fn main() {
    let matches = clap::Command::new("ppc750cl-fuzz")
        .version("0.2.0")
        .about("Complete \"fuzzer\" for ppc750cl disassembler")
        .arg(
            clap::Arg::new("threads")
                .short('t')
                .long("threads")
                .help("Number of threads to use (default num CPUs)"),
        )
        .get_matches();

    let threads = match matches.get_one::<String>("threads") {
        Some(t) => t.parse().expect("invalid threads flag"),
        None => num_cpus::get() as u32,
    };
    let start = Instant::now();
    let fuzzer = MultiFuzzer::new(threads);
    let avg = fuzzer.run();
    println!("Finished in {:.2}s (avg {}/s)", start.elapsed().as_secs_f32(), avg);
}

#[derive(Clone)]
struct MultiFuzzer {
    threads: Vec<Fuzzer>,
}

impl MultiFuzzer {
    fn new(num_threads: u32) -> Self {
        assert_ne!(num_threads, 0);
        let mut threads = Vec::<Fuzzer>::with_capacity(num_threads as usize);
        let part_size = 0xFFFF_FFFF / num_threads;
        let mut offset = 0u32;
        loop {
            let next_offset = match offset.checked_add(part_size) {
                None => break,
                Some(v) => v,
            };
            threads.push(Fuzzer::new(offset..next_offset));
            offset = next_offset;
        }
        threads.last_mut().unwrap().range.end = 0xFFFF_FFFF;
        Self { threads }
    }

    fn dispatch_progress_monitor(&self) {
        let this = self.clone();
        std::thread::spawn(move || {
            let start = Instant::now();
            let mut last = 0u32;
            loop {
                std::thread::sleep(Duration::from_secs(1));
                let elapsed = start.elapsed();
                let mut now = 0u32;
                for thread in &this.threads {
                    now += thread.counter.load(Ordering::Relaxed) - thread.range.start;
                }
                let per_second = now - last;
                last = now;
                let progress = 100f32 * ((now as f32) / (0x1_0000_0000u64 as f32));
                let avg = now as f32 / elapsed.as_secs_f32() / this.threads.len() as f32;
                println!("{per_second}/s\t{progress:05.2}%\tn=0x{now:08x} (avg {avg}/s)");
            }
        });
    }

    fn run(&self) -> f32 {
        self.dispatch_progress_monitor();
        let start = Instant::now();
        let handles: Vec<_> = self.threads.iter().map(|t| t.dispatch()).collect();
        for handle in handles {
            // TODO This doesn't panic immediately, since we'll block on thread zero
            //      for most of the time.
            handle.join().expect("thread panicked");
        }
        let end = start.elapsed();
        u32::MAX as f32 / end.as_secs_f32() / self.threads.len() as f32
    }
}

#[derive(Clone)]
struct Fuzzer {
    range: Range<u32>,
    counter: Arc<AtomicU32>,
}

impl Fuzzer {
    fn new(range: Range<u32>) -> Self {
        Self { range, counter: Arc::new(AtomicU32::new(0)) }
    }

    fn dispatch(&self) -> std::thread::JoinHandle<()> {
        let mut devnull = DevNull;

        let counter = Arc::clone(&self.counter);
        let range = self.range.clone();
        std::thread::spawn(move || {
            let mut parsed = ppc750cl::ParsedIns::default();
            for x in range.clone() {
                ppc750cl::Ins::new(x).parse_simplified(&mut parsed);
                writeln!(&mut devnull, "{parsed}").unwrap();
                if x % (1 << 19) == 0 {
                    counter.store(x, Ordering::Relaxed);
                }
            }
            counter.store(range.end, Ordering::Relaxed);
        })
    }
}

struct DevNull;

impl Write for DevNull {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        Ok(buf.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
