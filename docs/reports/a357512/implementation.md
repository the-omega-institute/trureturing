# A357512 implementation record

Source: user implementation brief; first-tier OEIS conjecture. Skill: `lean4`.
Producer: Codex implementation seat, single agent, no independent review claimed.
Base: `d6836dd2ae403f006f1f2d6ae5ddef3af56c5e46`; worktree branch: `lane/math/a357512`.

## Target and preregistration

Let `a(n) = sum(k=0..n, k^5 choose(n,k)^2 choose(n+k,k)^2)`.
A: every odd `n` with `3 ∤ n` satisfies `n^4 ∣ a(n-1)`.
B: every prime `p ≥ 5` satisfies `p^4 ∣ a(p-1)`.
A fixes the explicitly suggested `P(2)={3}`; it is stronger than the bare
existence of some finite exceptional prime set. This distinction is retained.
B is an authorized universal fallback, not a finite-instance delivery.

Proposed B escape witness, before numerical or Lean experiments: a binomial
product expansion modulo `p^4` reducing the weighted summand to a polynomial
term and a harmonic correction; cancellation of their complete sum.
For A the corresponding unit-denominator step must also handle indices
divisible by a prime factor of a composite `n`; no such extension is claimed.

Success requires a kernel proof of A or B, repository build and delivery gates,
and an opened PR. A counterexample requires a kernel witness. A blocked result
must identify actual Lean goals, not only unsuccessful library searches.
Numerical disagreements with the brief trigger its explicit stop condition.

## Repository search

`rg -n 'A357512|[Aa]p[eé]ry|Supercongruence|supercongruence' D5 --glob '*.lean'`
found `A375178Supercongruence.lean` and unrelated zeta-value prose.
The full A375178 module was read: 23 lines beginning `private ` (including
private definitions/abbreviations); the public surface is `a` and
`supercongruence`. Its sole public theorem concerns a different binomial cube
sum. Its private helper proofs inform technique but provide no public GID.
`D5/S3/ArithSums` contains 3 files at this base.

## Pending evidence and nonclaims

Mathlib and third-party searches, paper full texts, independent numeric rerun,
and Lean proof attempts are pending. No target is proved or refuted yet.
No novelty claim, search-complete claim, freeze, coverage, CI success, or
independent consensus is asserted. Unopened external sources remain
`ASSUMED-UNVERIFIED` until a receipt and reading account replace this status.

## Numerical probe

Independent Python `math.comb` / integer calculation reproduces all supplied
readings: in `3 ≤ n ≤ 139`, 46 odd nonmultiples of 3 pass modulo `n^4`;
all 23 odd multiples of 3 fail. All 28 primes in `5 ≤ p ≤ 113` pass modulo
`p^4`; 27 fail modulo `p^5` (the sole fifth-power pass is `p=7`). The six
specified composites all pass. The first 17 calculated terms start
`0,4,1188,126144,10040000,682492500`; fetched OEIS identity comparison is pending.
The exact probe output is `numeric-probe.json` in the runner attempt directory.
These finite checks are probes only, not mathematical progress on A or B.

Pinned Mathlib: `v4.33.0`, revision
`db584cd6d46c92f209a44c0f1c829460d327499d`.
Text searches for Apéry/supercongruence and choose/ModEq found Lucas congruences
modulo a prime, plus generic factorial/binomial identities; no A357512 target.
Public helper candidates include `Nat.add_one_mul_choose_eq`,
`Nat.descFactorial_eq_factorial_mul_choose`, and `Nat.choose_mul_succ_eq`.

## Fetched source receipts

| URL | HTTP | Bytes | SHA-256 |
| --- | --- | --- | --- |
| https://oeis.org/search?q=id:A357512&fmt=json | 200 | 2499 | `6a642473a60423ea755db62d0b7a702f3024bcedaaa5345e94de4ab04dbbcbba` |
| https://oeis.org/A357512/b357512.txt | 200 | 354 | `024cfc8bafbce0b750834b74b2a404a40730fdefb62d96d2f7e3bd78a6157adc` |
| https://arxiv.org/pdf/2403.19503 | 200 | 117335 | `2ce5211f7b973c8eaced9963bc08c472244d86a359f8fee83e7935309540b8b2` |
| https://arxiv.org/pdf/1803.07146 | 200 | 236001 | `04aead65568fdb56bfb3c5a31b4ddd768fa47508eef7eabd622d3457065fc4c2` |
| https://arxiv.org/pdf/1401.0854 | 200 | 291946 | `902b4799157c7f5cae8be1122f3be10937a7f6d3533322da4b633d35154551af` |

OEIS DATA: all 17 terms match exactly. The FORMULA field additionally states
the explicit A target (`n ≡ 1 or 5 mod 6`) as a conjecture, removing any
ambiguity about its attribution to the entry. The comment retains its
existential-prime-set wording.

GitHub authenticated REST code search `A357512 language:Lean`: HTTP 200,
`total_count=0`, `incomplete_results=false`. This is a bounded negative search,
not an assertion about every third-party formalization.

`make lean-cache-ensure`: EXIT=0; `status=seeded`, `method=clonefile`,
`clonefile_attempts=1`, project and mathlib both `warm`, no missing mathlib oleans.
Donor `/Users/chronoai/trureturing`.

## Calibrated arXiv searches

| Query / URL | HTTP | Total | Bytes | SHA-256 |
| --- | --- | --- | --- | --- |
| [all:A357512](https://export.arxiv.org/api/query?search_query=all%3AA357512&max_results=30) | 200 | 0 | 696 | `7284ae403c36cff008a440f12bfca8b994b36b2d7491a219151c66f9b3ec1ef2` |
| [abs:supercongruence](https://export.arxiv.org/api/query?search_query=abs%3Asupercongruence&max_results=30) | 200 | 183 | 39278 | `5d09a7553f292c36da096730843a0591244d6aad964af647baf63b94c7350c38` |
| [abs:Apery](https://export.arxiv.org/api/query?search_query=abs%3AApery&max_results=30) | 200 | 52 | 37986 | `e1b09b22b98c2685e2ac6558370e8687a7775de7b21d10de79f81861a353a8dd` |
| [abs:"Apéry"](https://export.arxiv.org/api/query?search_query=abs%3A%22Ap%C3%A9ry%22&max_results=30) | 200 | 201 | 42248 | `a54bbbccb78393901d19736e6aaf08a1bf277a0a5ab0381f6728974fb6ec40b3` |
| [abs:"Apéry" AND abs:supercongruence](https://export.arxiv.org/api/query?search_query=abs%3A%22Ap%C3%A9ry%22+AND+abs%3Asupercongruence&max_results=30) | 200 | 16 | 23998 | `174318d020d72c54b5d6233306a8cc1fad7db4fdd152968bdbb33541c57973da` |
| [abs:Apery AND abs:supercongruence](https://export.arxiv.org/api/query?search_query=abs%3AApery+AND+abs%3Asupercongruence&max_results=30) | 200 | 3 | 4617 | `614be35b0103d1ec9fe3ed05828579ab960b9912b19dfa4dac1325c4674374c5` |

GitHub code searches: `supercongruence language:Lean` returned 0;
`apery language:Lean` returned 3 (both `incomplete_results=false`).
The hits are two files in `project-numina/LeanTriathlon` and unrelated prose
in `deancureton/sphere-six-complex`; the relevant file is being opened.

## Full-text reading and scope verdict

The three PDFs were opened and their relevant sections read, beyond abstracts:
Liu 2403.19503, §§1–5 (Theorems 2.1–2.2, Lemmas 3.1–3.4 and proofs), plus
§6 conjectures; Straub 1803.07146, §1 and §4 (Theorem 4.1 and its proof,
equations 23–29); Straub 1401.0854, §1, §3 Theorem 3.2, §5 Lemmas 5.1–5.3
and the proof of Theorem 3.2. Liu treats generalized Domb and C-star numbers
at `np`, with Bernoulli corrections; the 2018 paper treats q-binomial sums
modulo cyclotomic cubes; the 2014 paper proves multivariate prime-power scaling
modulo `p^(2r)` / `p^(3r)`. None of these read statements is A or B, nor is
setting their parameters a direct proof of the fifth-weighted sum modulo `p^4`.
Verdict: no proof of the target found in this stated scope; this is not an
exhaustive-literature assertion. Sections not listed are `ASSUMED-UNVERIFIED`.
PDF extraction used pypdf with fonttools; the rotated-text warnings concern
unextracted rotated content, not a claim of complete PDF transcription.

The relevant third-party Lean hit was opened at commit
`2aede4209c203ae9901eff870744e4b77dc6173f`:
https://github.com/project-numina/LeanTriathlon/blob/2aede4209c203ae9901eff870744e4b77dc6173f/LiveLeanTriathlonSorry/Apery/All.lean
It states irrationality of zeta(3), with `sorry`; it provides no usable
supercongruence lemma. No third-party library is imported.

## Revised proof plan (before Lean attempts)

The proposed expansion witness is sharpened: writing
`b(p,k)=choose(p-1,k)*choose(p+k-1,k)`, prove in `ZMod(p^4)` that
`k^4*b(p,k)^2 = p^2*k^2 - 2*p^3*k` for `0<k<p`, by the binomial recurrence
and cancellation of units. Multiplying by `k` gives the weighted summand.
The complete sum then vanishes by the square/cube sum formulas and cancellation
of 12. Harmonic corrections are unnecessary at this precision because `b`
already has a factor `p`. This replaces the provisional harmonic-cancellation
part of the initial plan; the numerical and literature conclusions remain valid.

Additional prerequisite search found and fully read the public surface of
`DedekindReciprocityFiniteSums`: its `sum_Ico_cast_sq` applies to every natural
bound, and will be reused by casting its denominator-cleared rational identity
through the integers. Mathlib's `sum_range_pow` supplies the cube sum. The
private `six_mul_sum_sq` in A373561 is unavailable as a public dependency.
First Lean attempt exposed an unnecessary rewrite after `dsimp` had already
normalized `p+(k+1)-1` to `p+k`; removing that rewrite preserves the statement.

`b_step`, `transport`, `binomial_sq_scaled`, and `weighted_term` now elaborate
with EXIT=0 and no `sorry` or added axiom. The only diagnostic is a tactic-style
warning. The actual escape witness is `binomial_sq_scaled`, proved by induction
and unit cancellation, and consumed by `weighted_term`.

A broader repository search found a material literature lead in
`Library/Words/oeis2026triage0910.md`: its A357512 assessment records Kutal's
`TheSil/A357513_conjecture/proof.tex` as proving the prime subcase with `m=-3`.
This source was absent from the brief's three-paper scope. Verification of the
actual source is pending; no B-level novelty claim will be made. The user's
explicit instruction permits local Lean proof after no usable library hit,
even for published mathematical results, and authorizes B as a delivery target.

## Exact upstream Lean hit: B scope correction

The complete README and mathematical proof were read at immutable revision
`59c677df3563c4c506dfafcdf45237475140bb86`. The source public definitions
`generalizedSum`, `u`, `exceptionalPrimes` and the principal theorem bodies
were inspected. `OddExponentCongruence.u_prime_sub_one_dvd_of_good` permits
`m : ℤ`; setting `m=-3` gives weight `k^5`, with good-prime condition
`¬(p-1 : ℤ) ∣ -2 ∨ (p : ℤ) ∣ 1`. Every prime `p≥5` satisfies the first
disjunct. The integer sum has denominator one, so its reduced numerator
is precisely A357512. B therefore has an exact third-party Lean hit.

This supersedes only the earlier no-hit assessment: GitHub code search did
not index this matching source under the searched words. Its absence from those
results cannot justify local reproof after this discovery. The brief permits
local proof for published results when no usable Lean hit exists; it also
explicitly requires direct reuse for exact Lean hits. Spec A17.2 requires
dependency or transplant, forbids reproof, and requires preservation of license
terms for transplant. Upstream Lean/mathlib is v4.29.0; this tree is v4.33.0.
The GitHub repository API reports `license: null`; the exact root tree has
no LICENSE/NOTICE file, and Proof.lean contains no license header. Compatibility
compilation is being tested locally without copying upstream code into Git.

| URL | HTTP | Bytes | SHA-256 |
| --- | --- | --- | --- |
| https://raw.githubusercontent.com/TheSil/A357513_conjecture/59c677df3563c4c506dfafcdf45237475140bb86/README.md | 200 | 3098 | `3eb4c29dc591396a3046091521212f210d4897026c02d0db80b6e4a64b8b7d4e` |
| https://raw.githubusercontent.com/TheSil/A357513_conjecture/59c677df3563c4c506dfafcdf45237475140bb86/proof.tex | 200 | 6390 | `be0dc8655f45e4a7bb3d57e8c6d3cfb60c329cc8943c6518ae741fbf5abc3e18` |
| https://raw.githubusercontent.com/TheSil/A357513_conjecture/59c677df3563c4c506dfafcdf45237475140bb86/Proof.lean | 200 | 51901 | `c375d541a9b14a18d591a0516bc9fb32784985fb75146eef42985cf5e9d4b1d0` |
| https://raw.githubusercontent.com/TheSil/A357513_conjecture/59c677df3563c4c506dfafcdf45237475140bb86/lean-toolchain | 200 | 24 | `85b71aa934e019c03eac6ec5ed97526956b4dff51b54c5d558fca8a5b34703e6` |
| https://raw.githubusercontent.com/TheSil/A357513_conjecture/59c677df3563c4c506dfafcdf45237475140bb86/lakefile.lean | 200 | 267 | `f2d179098dcb525a3799fd65bebbfcac45204ed0445c51ab2fd7c1da79f3ce37` |
