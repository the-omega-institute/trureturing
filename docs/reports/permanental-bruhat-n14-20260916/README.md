# Permanental Bruhat check at n = 14

The fixed source map passed all northwest-rank comparisons for all 25,401,600 = 7!² inputs at n = 14. The run also passed 25 source controls and evaluated 4,978,713,600 nonempty northwest cells. This is a finite computational result. The all-size conjecture remains open; this report supplies no Lean theorem or open-problem KPI increment.

For a permutation w preserving {1,…,7} and {8,…,14}, the program constructs the specific f₁₄(w) of Pan–Skandera–Wang and checks

`#{i ≤ r : wᵢ ≤ c} ≥ #{i ≤ r : f₁₄(w)ᵢ ≤ c}`

for every 1 ≤ r,c ≤ 14. Empty northwest rows and columns have rank zero. The map is fixed by the published recursive construction; choosing another parity-preserving image would test a different claim.

## Files and sources

- `checker.c` is the exact executed C source, including its fixed-storage enumerator and resource supervisor.
- `source_tests.h` contains the literal source examples used by its 25 controls.
- `result.json` contains the completed counts, measurements, limits and producer hashes.
- `source_audit.json` maps the code to the public definitions, records source clarifications and pins the author implementation.
- `AUTHOR-MIT.txt` retains the author implementation's MIT notice. The C implementation is independent; no substantial MATLAB code was copied.

The target is Conjecture 7.8 of Pan, Skandera and Wang, *Permanental Inequalities and Unit Interval Orders*, EPTCS 445 (2026), 139–147, [DOI 10.4204/EPTCS.445.17](https://doi.org/10.4204/EPTCS.445.17), and Conjecture 7.25 of [Pan's thesis](https://preserve.lehigh.edu/_flysystem/fedora/2026-06/Pan_lehigh_0105A_13246.pdf), Chapter 7. The northwest criterion follows Drake–Gerrish–Skandera, [DOI 10.37236/1847](https://doi.org/10.37236/1847). These named sources report verification through n ≤ 13. This report does not claim worldwide novelty for the n = 14 computation.

The complementary block split uses the ceiling; maximum insertion includes the append slot. The thesis p.60 displayed obstruction has actual slots 6 and 5, despite the printed 5 and 4. Controls retain its displayed permutations and distinguish that arbitrary comparable pair from the recursive f₆ pair. The source map gives further locators.

## Build and use

This implementation supports macOS only: it requires C11, libproc, kqueue and lock-free 64-bit atomics. It was executed with Apple clang 21.0.0 on arm64 Darwin. Other platforms and compiler versions are unverified. Apple's Command Line Tools supply clang and the SDK; install them with `xcode-select --install` if absent. The preprocessor rejects non-Apple targets.

From this report directory, compile into a fresh temporary directory:

```sh
experiment_build="$(mktemp -d)"
clang -std=c11 -O3 -Wall -Wextra -Wpedantic -Werror \
  -fstack-usage -fno-omit-frame-pointer checker.c -lproc \
  -o "$experiment_build/checker"
```

Invocation is `checker RUNNER_DIRECTORY STOP_UTC`. Supply an existing fresh output directory and a future UTC timestamp in `YYYY-MM-DDTHH:MM:SSZ` form. For example, an intentional new reproduction can use:

```sh
experiment_run="$(mktemp -d)"
experiment_stop="$(date -u -v+25M '+%Y-%m-%dT%H:%M:%SZ')"
"$experiment_build/checker" "$experiment_run" "$experiment_stop"
```

Every successful invocation runs the controls and then the entire fixed n = 14 scan; there is no controls-only mode or size option. It refuses to overwrite `checker.stdout.log`, `scan.once` and `terminal.json`. Those runtime outputs belong in the chosen output directory. `terminal.json` provides the raw result fields; the committed `result.json` presents the retained completed measurement with its mathematical scope. A nonzero exit or incomplete input count must not be interpreted as all-pass.

The code's literal `BUILD Apple clang21` log label describes the original build and does not detect the compiler. Use the actual compiler's `--version` for any new build. The source hash is `66ad936d835fe17fcc616f9636b91c448931333d11cae774d2f0e27c8c58d405`; both code files' hashes are recorded in the JSON data.

## Measurement limits

The completed run took 2.972533 seconds wall time and 2.863153 seconds child CPU time, with 1,294,336 bytes peak child RSS. Its static workspace was 1,116 bytes plus a 4,096-byte shared mapping. The 131,072-byte application-storage bound excludes runtime and library storage and is not a process-memory measurement.

CPU soft and hard limits were 1,200 seconds. The effective wall limit was 996.530484 seconds, selected from the program's 1,500-second maximum and the supplied absolute deadline. Child RSS was sampled every 100 ms against a 1 GiB watchdog threshold; this is not a hard address-space cap and can miss transient peaks. Successful completion, counts and exit status are separate from those resource limits.

The source controls cover published map examples, insertion, reversal, rank direction and the displayed obstruction. The main enumeration uses the staged construction; the separate maximum-removal point evaluator is used for controls and candidate verification, not for every successful input. Neither implementation constitutes a kernel-certified proof.
