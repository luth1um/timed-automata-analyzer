use criterion::{Criterion, criterion_group, criterion_main};
use std::time::Duration;
use timed_automata_analyzer::ta::TimedAutomaton;
use timed_automata_analyzer::ta::clock::Clock;
use timed_automata_analyzer::ta::clock_constraint::ClockConstraint;
use timed_automata_analyzer::ta::clock_constraint::clause::{Clause, ClockComparator};
use timed_automata_analyzer::ta::location::Location;
use timed_automata_analyzer::ta::switch::Switch;

// Benchmarks
fn bench_find_unreachable_locations(c: &mut Criterion) {
    c.bench_function("reachability 5k states", |b| {
        b.iter(|| {
            // setup
            let clock_x = Clock::new("x");
            let clock_y = Clock::new("y");

            let clause_x_leq10 = Clause::new(&clock_x, ClockComparator::LEQ, 1);
            let invariant_loop = ClockConstraint::new(Box::from(vec![clause_x_leq10.clone()]));

            let clause_x_geq10 = Clause::new(&clock_x, ClockComparator::GEQ, 1);
            let guard_ll = ClockConstraint::new(Box::from(vec![clause_x_leq10, clause_x_geq10]));

            let clause_x_g20 = Clause::new(&clock_x, ClockComparator::GREATER, 5_000);
            let guard_le = ClockConstraint::new(Box::from(vec![clause_x_g20]));

            let loc_loop = Location::new("loop", true, Some(invariant_loop));
            let loc_end = Location::new("end", false, None);

            let sw_ll = Switch::new(
                &loc_loop,
                Some(guard_ll),
                "ll",
                Box::from(vec![clock_x.clone()]),
                &loc_loop,
            );
            let sw_le = Switch::new(
                &loc_loop,
                Some(guard_le),
                "le",
                Box::from(vec![clock_x.clone(), clock_y.clone()]),
                &loc_end,
            );

            let ta = TimedAutomaton::new(
                Box::from(vec![loc_loop, loc_end.clone()]),
                Box::from(vec![clock_x, clock_y]),
                Box::from(vec![sw_ll, sw_le]),
            );

            // function to test
            timed_automata_analyzer::find_unreachable_locations(ta);
        })
    });
}

// Configure Criterion
fn configure_criterion() -> Criterion {
    Criterion::default()
        .warm_up_time(Duration::from_secs(5))
        .measurement_time(Duration::from_secs(15))
        .sample_size(200)
}

criterion_group!(
    name = benches;
    config = configure_criterion();
    targets = bench_find_unreachable_locations
);
criterion_main!(benches);
