# Original fixed5040 box: complete source and fixed certificate (S21/C46/C48)

The source now has complete canonical coverage for **all 21 numbered units** in
section 32. The caller repaired the five table spans and performed one additional
canonical ingestion. Every byte of the original mathematical text, the embedded
certificate, and all 65 first-run CAS/YAML pairs is preserved. Five new full-unit
pairs complete the bindings for 32.3, 32.7, 32.13, 32.14 and 32.15. The final layer
contains the source, this report and 70 CAS/YAML pairs: **142 changed files**.
Independent review and ordinary delivery gates remain outstanding; this is not a
merged-delivery claim.

The mathematical result concerns only the original fixed box
`5040 = 2^4 * 3^2 * 5 * 7`, at `T = 0`, with strict domain
`log(1058400) < M0 < M1` and at least two actual corner sums in the closed slab.
The paper reduces every such real slab to 16 retained nodes and proves
`G < -1/1250`; its unique maximum occurs at shifted endpoint products
`(22226400,31752000)` (legacy products `(105840,151200)`). Section 32.17 proves
uniqueness over the real domain using a strict decrease in the prime-2 distance;
finite-node uniqueness alone would not suffice. The adapted certificate's
277 assertions passed in I16's one recorded run. The caller's C48 repair executed
**no mathematical program**. This upper-bound comparison does not establish RH.

## Caller C48 repair and current identities

I16's first ingestion exited 0 but left 2,182 bytes outside the emitted spans in
five units. That failed first-run coverage result remains failed and is preserved
verbatim below. The one-run restriction was in the caller's I16 brief. The caller
subsequently authorized the necessary reversible repair under C48 and added
exactly five `~~~text` / `~~~` fence pairs: 60 bytes and 10 LF. Removing just these
five fence pairs recovers every byte of the original returned source. No CAS or
YAML file was hand-edited, deleted, normalized, or renamed.

The second invocation used the same canonical command on the changed source:

```sh
make ingest BASE=fe3f12abe8bc2e14628a93990fee2755c30da2bd SOURCE=arithmetic-boundary-quantization
```

The host-tracked process was session 15004 and ended with exit 0. Its terminal
output was:

```text
INGEST residual_open_added=5 skipped_existing=286 coarse_fallbacks=0 open_genres=0 cas_objects_written=5 ledger_changed=true
```

The preceding caller patch receipt is timestamped 2026-09-09T22:19:57.087416Z;
the terminal result was collected before the byte audit at
2026-09-09T22:29:18.763917Z. An exact second-process finish timestamp and separate
stdout/stderr stream identities were not captured, so none is inferred from the
first-run receipt. The second invocation and the original first invocation are
two distinct generation events, on different source bytes.

| Current source component | Bytes | LF | SHA256 |
| --- | --- | --- | --- |
| prefix | 316724 | 5974 | `9229e2affc81243efcdcbd228058d8ca19cea395630a94ae943afde374157dd2` |
| suffix | 26768 | 524 | `db7e20d6fdd6df178758ca59807428a6c48a7eba2540ca84ddc0c142efbe1b88` |
| whole | 343492 | 6498 | `65f8ebe49381039838524752d4e3c19e4db13bc7046d74030f1acc9bb0f8be20` |

The predecessor prefix remains exactly 316724 bytes. The current certificate
remains 10595 bytes / 205 LF, SHA256
`b8a5972435d74afd0c843057bd6471736db3b7303ddb45a51381bb95d70f0602`.
The historical report's marker-based extraction still selects those exact bytes;
its former absolute line numbers and source-span coordinates describe the
original snapshot only. The original full report is preserved as one contiguous
byte sequence below: 67976 bytes / 956 LF, SHA256
`290a0a99d77f1030d37c91e7be1f1341dd367c996b3b20e8cbbc2ae84004acb6`.

## Complete current numbered-unit bindings

Every row below was checked against the **entire current numbered unit**, from
its bold numbered lead through the byte before the next lead, or source EOF.
Each unit equals one complete CAS blob, not a concatenation with missing prose.
All 21 comparisons pass; uncovered numbered-unit bytes are zero. No automatic
child or parent chain was emitted. First-run table rows remain independent
historical row atoms; the five newly emitted objects are full units.

Each bare ID expands to the exact two paths
`Meta/Digestion/atoms/sha256/<ID>` and
`Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/<ID>.yaml`.
For each row, raw_sha256, normalized_sha256 and cas_ref are all `sha256:<ID>`;
the YAML's own hash is given separately. Each YAML is 328 bytes / 7 LF with empty
coverage_gids and unresolved_subitems. Offsets are zero-based half-open UTF-8
bytes; line numbers are one-based inclusive. The ordered atom list for each unit
is exactly its one displayed ID and ordered_children is empty.

| Unit | Producer run | Current byte span | Current lines | Bytes / LF / terminal LF | ID | YAML SHA256 |
| --- | --- | --- | --- | --- | --- | --- |
| 32.1 | 1 | [316793,317790) | 5978-5992 | 997 / 15 / 2 | `577e0ea00b7c003c4a85f9277519129736ba52988fb506df6640363bf72baee2` | `1b22ece9c1996012a6e6b2ab2b9fa8e7a00001e2fad8a869043a439548c91b2f` |
| 32.2 | 1 | [317790,318804) | 5993-6011 | 1014 / 19 / 2 | `bb70f0b6709196af0ae33eb4e256cf09bcae4df5491f77162a7ef3036639561d` | `b8db18431c3ad61b77b97447a58e7503a6ea32e19dd4522a57428433158348dd` |
| 32.3 | 2 | [318804,320513) | 6012-6059 | 1709 / 48 / 2 | `af2714fed461cdcaf2da2725959e5001e1614a17dc6d10b4ab33ae5729bc32e0` | `98912e918c41078924648406ccde0a5509ef4d95041660955e64288b2b555c74` |
| 32.4 | 1 | [320513,321612) | 6060-6087 | 1099 / 28 / 2 | `67a340ef888de9e231fd65ab279997a59d5215a482a77f2ca115aa6bab25eabe` | `2e707e920bff67f6ddcbe2552b2953ed5c9178780edee15657cb0aa0ce39549a` |
| 32.5 | 1 | [321612,322281) | 6088-6102 | 669 / 15 / 2 | `dc7e472bfd09c2e5ad8ca57c353fd501607d33b6160e91c1f84632b58c73852b` | `ab40e9224624b8584f1ec11a5f867fa971a3c29930ff1e0e8913c973d0973eec` |
| 32.6 | 1 | [322281,322875) | 6103-6115 | 594 / 13 / 2 | `b812d431e527f840da3c065dcc99703aacf85c8e84c50f0943bafa95f2ebedcd` | `4eb197ad66a0461427c4427bb8df7281904f12211d2e588376c615aa1e7ec0c8` |
| 32.7 | 2 | [322875,323567) | 6116-6135 | 692 / 20 / 2 | `6a26e45b7ee03e5f635a6f0a250c9da2d851b616db78b20cb6d22cda2fdde2df` | `a5bd1b8ab6e07199e8c57a862e5a295f515baecc2366427c7af7c3f3d52d1330` |
| 32.8 | 1 | [323567,325236) | 6136-6169 | 1669 / 34 / 2 | `bfabe3fcb9e5e69459e48e7d26c86be755f98cea19edff3688d6779771d575c1` | `4adeae44054f742adfb74578e5fe8732e33ec9c3152bfab0f940f214c20d756c` |
| 32.9 | 1 | [325236,325828) | 6170-6180 | 592 / 11 / 2 | `edc7df17929ebaa65f2378f7723066c9580cd6569bb6eb9a800408e47b96dd86` | `8e36318e4081f6ede26e79fdab25a0e742b21c53851653145a5a483e660b075c` |
| 32.10 | 1 | [325828,326573) | 6181-6197 | 745 / 17 / 2 | `e2dddcccb5498bba7dfcd8bf7e660b29f7280ac0c9d9a3815809032a12e48cbf` | `40aad0056772759ecc880c3cbf07c23be9f163e004135411d37b3b2d4c937ee0` |
| 32.11 | 1 | [326573,327785) | 6198-6225 | 1212 / 28 / 2 | `d5e64f4c4a5b37d1666829475dbd2c6b834970ec90fea63418575ab70d02af82` | `cb49bd094c7fb315082c2d21d6e24b3b77ddd9889eaaa707a12e2b03adce64b1` |
| 32.12 | 1 | [327785,328713) | 6226-6243 | 928 / 18 / 2 | `5145aee91880772394bb9153a65de8e534ccfcab3d4500ab62bf9aa74655aa82` | `8e7895fdfb0e8e57ceef9ab9bc2964203458abb98cb6ddb7f00c8ddc2e229bc2` |
| 32.13 | 2 | [328713,330244) | 6244-6285 | 1531 / 42 / 2 | `33a959a8ab03c5d5129b81d23df781014dc5b7ad4ca827a28a098b957d57dbb8` | `79aa1cd085d1f6c708c6edc27406fc9571ac7587da981c88dce77b5d4a6effd4` |
| 32.14 | 2 | [330244,331456) | 6286-6311 | 1212 / 26 / 2 | `5a6ef842e39b9ef4700a2f7503c6e0f5a3334b4dd0e935d89691d81a82a0bd58` | `20fe8e26740bc14ea244f3c62f74b3edb6ca879eda0e538370b6d8d68d4e77a6` |
| 32.15 | 2 | [331456,333742) | 6312-6342 | 2286 / 31 / 2 | `c75ebee1711448d758b7599f9e1e76d188879116fe05c22ee5070883da852ad2` | `5303a01c74a6ad78321bb00978fc6e1dacbbbbf5340d9d70cb8a00315873f5af` |
| 32.16 | 1 | [333742,335157) | 6343-6379 | 1415 / 37 / 2 | `6b9de42b2b39e8047434fd00688dde1c2ec1b686815d8390138e08ea9d2b4f1f` | `43f043a0cae41a31b73e10515db217a8c61dca0f14cd6b534dc28e8fe8a4b0f2` |
| 32.17 | 1 | [335157,336182) | 6380-6399 | 1025 / 20 / 2 | `b494ca333580108b2deb6550e7123a7e08226df26dde679a3aabf52ac6d48df4` | `c782d591c87cc9220c7beba2551f6e7f573f3500444ba9a8e86db8c81679897e` |
| 32.18 | 1 | [336182,337546) | 6400-6425 | 1364 / 26 / 2 | `6f781365c3476b18072106757c1a1a873972e8de0c5fed7b1aae92f150140ac1` | `3c436f9e88edccc7bb53aed4e16fc7073428f20e430cf1a3b4c60ac998686c93` |
| 32.19 | 1 | [337546,339201) | 6426-6446 | 1655 / 21 / 2 | `998b44b7a9dd7706d0d2b3b3d2c3cc3ad984ea49260563741f5082a5fcbb872f` | `d17f1439a835b73dc9675fd846acd02e735841dd6ff918f6d73f620a14f141b4` |
| 32.20 | 1 | [339201,341136) | 6447-6468 | 1935 / 22 / 2 | `3ac23b4b613f6b57cc186bea84165e3aaa9f1b80ccd97d61467732d3c48f92c5` | `8e2eefec935a47381d9edfb1ae1122bd2712edc1eb312040f639aed90069cbca` |
| 32.21 | 1 | [341136,343492) | 6469-6498 | 2356 / 30 / 1 | `9ee4f78f7fd25b90c4b6fbf4af060e9c82cbf7ba12d1184d6e14e01c3fff3e1c` | `5637a58624730d078318732b9adfc5e84cc91937609fcff29754e06d8058d806` |

All 130 first-run output files were compared byte-for-byte with I16's original
return and are unchanged, including the historical unit-31.22 terminal-LF
variant. The five complete replacements add ten files; they do not erase the
partial heads or table rows. Only the existing theory source is modified among
tracked files. The report is not selected as an additional theory source, so
this report update requires no further ingestion.

Section 32.21 and the following original report describe **I16's first-return
scope**. In particular, their statements that one ingestion ran, the patch is
unapplied, and completion requires a follow-up were true of that historical
return. They are not the current caller status: C48 applied the patch, completed
the second ingestion and closed the five coverage gaps. No historical failure,
first-run coordinate, original program, or original execution receipt is
relabelled as a success or as a current measurement. S21 delivery still depends
on S20 MERGED and independent review. The standing research goal remains active.

<details open>
<summary>Historical I16 first return, preserved verbatim</summary>

<!-- BEGIN HISTORICAL I16 REPORT -->
# Original fixed5040 box: source and fixed certificate (S21/C46)

The adapted mathematical certificate passed. The single permitted canonical ingestion
exited 0, but the full-span check failed for five units containing Markdown tables:
32.3, 32.7, 32.13, 32.14 and 32.15. Their emitted atoms omit 2,182 source bytes,
including substantive prose after the tables. The source bytes remain intact.
This layer is **not ready for sealing as a complete canonical source layer**.
The precise gap inventory and an unapplied source-formatting proposal appear below;
no second ingestion or manual canonical repair has been performed.

This is the source/report/canonical-ingestion layer implemented by isolated Codex CLI
worker I16, flight `qgh0910-i16-actual-5040-fixed`, attempt 1, under the caller-pinned
`consensus-rnd:sshx` 1.0.0-beta.42 and its `CODEX_WORKER_SPEC.md`. The applicable
repository contract is CLAUDE 5.11. I16 is repo-prior-exposed; no extra worker,
subagent, oracle, independent review vote, or model-diversity claim is part of this
implementation. Caller-supplied actual GPT PRO and completed caller audits are prior
mathematical inputs. I16 consumed the primary `conclusion` only; its `log_ref` stayed
opaque. No worker log, caller transcript, peer envelope, other worktree or live target
was read. This report makes no review or standing-goal completion claim.

The source is [ARITHMETIC_BOUNDARY_QUANTIZATION.md](../../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md),
section 32, in branch `lane/math/quantized-gh-actual-5040-fixed-0910` at immutable base
`fe3f12abe8bc2e14628a93990fee2755c30da2bd`. The task-specific worktree is
`/Users/auricstudio/trureturing-qgh-actual-5040-fixed`. All changes are returned unstaged.
Caller owns sealing, public byte verification, independent review and ordinary delivery
gates. Final S21 delivery requires S20 MERGED; that lifecycle condition was not queried
or claimed discharged by this worker.

## Mathematical statement and proof boundary

The ordinary unique-factorization exponents are `(4,2,1,1)` for
`5040 = 2^4 * 3^2 * 5 * 7`, in prime order `(2,3,5,7)`. Lower coordinate exponentials
are `(32,27,25,49)`, upper ones `(64,81,125,343)`. The inner product is explicitly
`<x,y> = sum_i x_i*y_i`; neither unique encoding nor an optional Zeckendorf
re-encoding supplies orthogonality. The usual Pythagorean decomposition in these
chosen coordinates does not constitute an arithmetic sign theorem.

Write `Q = log(210)`, `A = log(1058400) = Q + log(5040)`. All budgets are finite real
numbers. The original domain is `A < M0 < M1`, with at least two distinct actual
corner sums in the closed slab `[M0,M1]`. Legacy exponent budgets are named
`tau_j = M_j - Q`; their exponentials differ from shifted ones by the factor 210.
No endpoint uses a future common-height symbol. This source is the original fixed
T=0 instance only. It excludes the lowest adjacent slot 0, whose lower budget is A.

For `f(x)=log(1-exp(-x))`, `I=[M0/4,M1/4]`, and the two-point coordinate sets `C_i`,
put `delta_i=dist(I,C_i)`, `V0=sum_i delta_i^2`, `mu=M1/4`, `rho=sqrt(V0/12)`,
`L=mu-rho`, `H=mu+3rho`, and `Psi=f(H)+3f(L)`. The price infimum D equals the
fractional knapsack maximum by the matching primal/price proof. D is an upper
bound on the exact discrete optimum W; it need not equal W at a general budget.
The comparison is `G=D-Psi`, with the same common Euler logarithm canceled as in
the predecessor source.

The full paper proof is in numbered units 32.5–32.12 and 32.17. The finite theorem
in section 26 is used under its actual hypotheses: k=4, distinct primes, ordinary
nonnegative integer exponents, actual corners and the original strict cutoff.
An actual corner proves `H >= L >= log(25) > 0` everywhere in the domain. Raising
the lower budget to the second largest admitted corner weakly increases G, with
equality precisely when every row distance remains unchanged. Between active
downward distance switches, the radius is convex as the Euclidean norm of a
nonnegative convex distance vector. Joint strict concavity and radius monotonicity
of F give strict concavity of Psi, including zero-radius cases. D is affine between
actual corner budgets. Thus G is strictly convex on each remaining interval, and
its interior is dominated by endpoints. At an upper corner the lower endpoint can
be saturated again. Beyond the largest corner D is constant and Psi strictly
increases, so the saturated upper tail strictly decreases. These arguments cover
all real budgets and their equality cases; a finite arithmetic run alone cannot do so.

The complete raw set has 15 adjacent and 56 reflected slots. The exact guards retain
adjacent slots 1 through 14 and reflected slots 23 and 37, with 55 inactive slots.
Inactive means ineligible; those slots are not reported as 55 negative evaluations.
Both surviving reflected upper legacy exponentials are noninteger rationals:
`274877906944/10418625` and `762939453125/12446784`. Their lower legacy exponentials
are 15120 and 35280 respectively. Their complete guards and all first-failed-guard
classes appear in units 32.13–32.14 and in the executable below.

Slot 9 uniquely maximizes the retained set. Let
`alpha=log(22226400)`, `omega=log(31752000)` and

```
z0 = (alpha - 24*log(2))/4
z1 = (16*log(3) - omega)/4
z2 = (12*log(5) - omega)/4
z3 = (alpha - 8*log(7))/4
r_star = sqrt((z0*z0 + z1*z1 + z2*z2 + z3*z3)/12)
Gmax = log(496/525) - f(omega/4 + 3*r_star) - 3*f(omega/4 - r_star)
```

All four z are positive and are the exact distance branches. The integer branch
inequalities in unit 32.16 establish this; numerical interval overlap is only a
consistency observation. At this node the unique fractional optimizer is `(1,1,1,0)`
and `D=log((63/64)*(80/81)*(124/125)*(48/49))=log(496/525)`. This actual corner is in
the slab, so W=D at this particular node. The certified bound is
`Gmax in [-821037164,-821037163]/10^12`, hence `G < -1/1250` throughout the original
domain. The maximizing legacy exponentials `(105840,151200)` correspond to shifted
`(22226400,31752000)`.

Uniqueness over the continuous domain uses an additional argument: any maximizer
must saturate to slot 9. With upper budget omega and lower budget a<alpha, the
prime-2 distance is `max(a/4-log(64),0)`, strictly less than its positive value at
alpha because `22226400 > 64^4`. Other distances cannot increase when a is lowered.
Thus saturation is strictly improving at this candidate. Equality `G=Gmax` occurs
exactly at `(alpha,omega)`. Generic saturation equality still permits unchanged
row distances; it was not silently replaced by equality of lower budgets. Zero G,
positive G, and equality at `-1/1250` are all excluded in this domain.

## Original inputs and execution attribution

All six authorized input files under `/tmp/qgh-boundaries-0908` are unchanged.
Hashes below are SHA256 of the complete original bytes, with LF counting byte 0x0A.

| Input filename | Bytes | LF | SHA256 |
| --- | --- | --- | --- |
| pro-actual-5040-box-envelope-0910.json | 16652 | 223 | `5be21f9a99b47cac955d478c7082301b85ca74db2c8e055217f928817962dca8` |
| caller-actual-5040-node-audit-0910.json | 30087 | 1342 | `ea7e59b56e4c46619ef3682ee81cde1ce146f17771320261ec2bacb75cf87cd3` |
| caller-actual-5040-node-audit-0910.py | 3905 | 72 | `fc98ce7579440ec814b19999588f16e516f7421a8df14452017598d7e823e957` |
| caller-actual-5040-sign-audit-0910.json | 13525 | 373 | `ee427151020fd42c2fb10a7ae998f8204cbaa325da331dda881c4c006239b897` |
| caller-actual-5040-sign-audit-0910.py | 6256 | 127 | `b773855012d7316e015d73cf58795b0eecdccac3501eeb60ebc29dd60e15b61b` |
| actual-5040-fixed-box-source-preparation-0910.json | 6143 | 120 | `c916924237b8b287c08681222f91869247c7bec838014491309bc2e8a39ab8ce` |

The actual GPT PRO designation and task
`0838ec9d-f978-4cfc-8d59-965a3331f912` come from the caller's supplied GoalArtifact.
The primary conclusion names flight `qgh0910-pro-actual-5040-box`. It reports
`DisabledError` retrieving the supplied immutable GitHub source, no source-byte
read or independent verification of its supplied byte/hash identity, and a
rederivation from the given definitions. Invocation-specific model/service
metadata was not independently verified. No conversation identifier was supplied
in these allowed artifacts, and none was inferred or retrieved from logs.

The primary reports a temporary standard-library integer/Fraction verifier on a
2^-160 outward mesh: 16 fixed corner constants, 71 eligibility slots, four densities
and 16 retained node evaluations. Its whole executable was not supplied in the
allowed primary envelope; this implementation does not claim to reproduce that
historical execution, its interpreter, or its stderr. The primary's global support
range `[3571708000370,5592595433915]/10^12` remains its self-reported range. The
adapted run below checks the broader fixed support bounds `0<L,H<16` separately.

The original caller node audit was created at
`2026-09-09T17:33:36.504288+00:00` and records 71 eligibility slots, 14 adjacent plus
2 reflected survivors, and zero G evaluations. The original caller sign audit,
created at `2026-09-09T18:03:45.685472+00:00`, records python-flint 0.8.0 / Arb256,
four density enclosures and 48 D/Psi/G enclosures, all passed, with a separate
paper-domain audit. Its exact interpreter version, invocation bytes, process exit
and stderr are not fields of the supplied JSON; they are not reconstructed as
historical observations. Neither original program was executed by I16.

### Raw remainder erratum

The original primary token is preserved verbatim as historical text:
`9/(41293^129)`. Its mathematical correction is **`9/(4*129*3^129)`**, since

```
2*(1/3)^129 / (129*(1-1/9)) = 9/(4*129*3^129).
```

For z=(t-1)/(t+1) in [0,1/3], the positive tail after j=0,...,63 in
`2*sum z^(2*j+1)/(2*j+1)` is bounded by the left side. This is the primary series
argument, derived in source unit 32.18. The related primary exponential recipe
uses `S80(x/16) + 2/81!`, valid for 0<x<16; its first omitted term and geometric
tail justify that constant. The new certificate checks the displayed rational
erratum identity but uses Arb logarithms, square roots and exponentials for all
sign certification. It does not silently repair or execute the raw primary recipe.

## Focused literature and repository overlap receipts

| URL | UTC access | Actual outcome | Bytes / SHA256 |
| --- | --- | --- | --- |
| https://home.cse.ust.hk/~dekai/271/notes/L14/L14.pdf | 2026-09-09T21:39:55.089012+00:00 | HTTP 200 | 51456 / `02a501415b8472ca147d17d6e5369d7889f7b2aeba7b9ba37082e7dbebdefa7d` |
| https://web.stanford.edu/class/ee364a/lectures/functions.pdf | 2026-09-09T21:39:55.089435+00:00 | HTTP 200 | 405347 / `c172569e16a24039ac7dd0ae9d1ee743e31eb6a9369eac38206b758cbe76903b` |
| https://python-flint.readthedocs.io/en/latest/arb.html | 2026-09-09T21:39:55.089578+00:00 | HTTP 200 | 310381 / `623fa9dd987b3b466e219a34d1151738387d0b32f8f3f9c2d4ff8b1784eab340` |
| https://dlmf.nist.gov/4.6 | 2026-09-09T21:39:55.089690+00:00 | HTTP 200 | 61279 / `3b97f47f148d890a7f0929b54bc97bb807798b03cff6588756876f8e5a73c5ce` |
| https://python-flint.readthedocs.io/en/0.8.0/arb.html | 2026-09-09T21:41:09.657195+00:00 | HTTPError: HTTP Error 403: Forbidden | No successful document read |

The successful downloads were read at the following precise scope. HKUST PDF
pages 4–7 contain the density sort, the last partial item and the exchange argument.
`pdftotext` was absent (command lookup exit 1); installed pypdf 6.17.0 extracted
these pages. Some HKUST formula glyphs extract as control characters. The readable
algorithm prose supports the stated overlap; the exact matching-price and boundary
proofs are supplied in the source rather than attributed to garbled formulas.
The Stanford PDF pages 6,16,26,27 (slides 3.4,3.14,3.24,3.25) explicitly give convexity
of norms, Jensen and scalar/vector composition with monotonicity conditions.
Endpoint maximization here follows directly from Jensen. The specialized strictness,
nonnegative-orthant composition, positive interpolated domain and zero-radius
handling are verified in the paper argument, not claimed as a literature sign result.

DLMF 4.6.4 supplies the classical logarithm expansion in `(t-1)/(t+1)`; its
specific 64-term tail estimate is the displayed derivation. The retrieved latest
python-flint arb page identifies itself as 0.9.0 and describes `[mid-rad,mid+rad]`
balls and `ctx.prec`. The 0.8.0 URL returned HTTP 403. This is a retained failed
retrieval, not evidence that version 0.8.0 lacks Arb. Runtime version assertions
below establish the actual pinned environment. Reading latest docs supplies
descriptive overlap only and is not a claim to have audited the 0.8.0 implementation.
No external source is claimed to prove this fixed G comparison. These are focused
checks of the tools actually used, not an exhaustive novelty or priority survey.

Local sealed-source overlap was read in this worktree: section 26.2–26.19 supplies
the general-k critical set, guards, saturation and maximum/equality classification;
26.28 records earlier classical attribution and its own historical access limits.
`ZECKENDORF_EULER_5040.md`, theorem 12.3 (lines 2304 onward), gives the existing exact
KL continuous–integer gap, a different quantity from G. Its chapter 11 already
contains a 5040 Robin certificate, not rerun here. `QUANTUM-RH.md`, “5040 还给出一个直接的维数障碍”
(lines 55820 onward), already states the ordinary exponent tuple and reversible
encoding interpretation. The fixed-box specialization, bounds and continuous-domain
proof are classified repo-derived paper arguments, with the classical ingredients
attributed above. No new definition of GH, RH equivalence/progress, Robin certificate,
Lean freezing or priority is claimed.

## Standalone certificate

This certificate has no caller-file inputs. Its only file read is its own program
bytes for the identity receipt. The four density intervals and all 48 node intervals
are literal rational endpoint data in `DENSITY_BINS` and `NODE_BINS`, exactly as in
source 32.7 and 32.15. The guards instantiate one preregistered integer box, not a
prime/exponent, height, moment or slab sweep. Each strict Arb comparison encloses
the exact result inside the displayed closed bin; decimals are not used for decisions.
`min`/`max` on Arb intervals cover nearest-endpoint ties without guessed branches.
Primal/dual and branch overlap checks do not prove algebraic equality; the source
provides that proof. Only this extracted adapted certificate was executed, once.

Program identity: 10595 bytes, 205 LF, SHA256 `b8a5972435d74afd0c843057bd6471736db3b7303ddb45a51381bb95d70f0602`.

Extract the exact bytes between the following Python fence and its closing fence;
the final program LF is included. From the repository root, the actual extraction
and execution paths used for this run were:

```sh
python3 - <<'PY'
from pathlib import Path
import hashlib
report = Path('docs/reports/actual-5040-fixed-box-0910.md').read_bytes()
start = report.index(b'<!-- BEGIN FIXED5040 CERTIFICATE -->\n```python\n')
start += len(b'<!-- BEGIN FIXED5040 CERTIFICATE -->\n```python\n')
end = report.index(b'```\n<!-- END FIXED5040 CERTIFICATE -->', start)
program = report[start:end]
assert hashlib.sha256(program).hexdigest() == 'b8a5972435d74afd0c843057bd6471736db3b7303ddb45a51381bb95d70f0602'
Path('/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qgh0910-i16-actual-5040-fixed/attempt-1/extracted-certificate.py').write_bytes(program)
PY
uv run --no-project --with python-flint==0.8.0 python /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qgh0910-i16-actual-5040-fixed/attempt-1/extracted-certificate.py
```

For another machine, choose any local extraction filename and substitute it in both
commands; the program has no dependency on this attempt path. The script writes one
JSON result to stdout and no output files. A process failure is not a passed certificate.

<!-- BEGIN FIXED5040 CERTIFICATE -->
```python
"""Fixed S21 proof inputs, one box and 71 theorem slots; no candidate search."""
import hashlib
import importlib.metadata
import json
import platform
import sys
from collections import Counter
from fractions import Fraction
from math import prod
from pathlib import Path

import flint
from flint import arb, ctx, fmpq

ctx.prec = 256
checks = Counter()


def require(category, condition):
    if not condition:
        raise AssertionError(category)
    checks[category] += 1


def q(value):
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))


def f(value):
    return (1 - (-value).exp()).log()


def enclosed(category, value, lower, upper):
    require(category, q(Fraction(lower, SCALE)) < value < q(Fraction(upper, SCALE)))


PRIMES = (2, 3, 5, 7)
EXPONENTS = (4, 2, 1, 1)
LOWER = (32, 27, 25, 49)
UPPER = (64, 81, 125, 343)
A_PRODUCT = 1058400
SCALE = 10**12
CORNERS = ((1, 0), (2, 1), (3, 2), (5, 4), (6, 3), (7, 8),
           (10, 5), (14, 9), (15, 6), (21, 10), (30, 7), (35, 12),
           (42, 11), (70, 13), (105, 14), (210, 15))
CAPACITIES = (1, 2, 6, 30, 210)
DENSITY_BINS = ((23083613113, 23083613114), (23045261959, 23045261960),
                (20373462417, 20373462418), (9095783332, 9095783333))
# slot, D lower/upper, Psi lower/upper, G lower/upper, all divided by SCALE.
NODE_BINS = (
    (1, -105585917043, -105585917042, -99815050712, -99815050711, -5770866331, -5770866330),
    (2, -93813806727, -93813806726, -89539949332, -89539949331, -4273857395, -4273857394),
    (3, -89612158690, -89612158689, -86872489407, -86872489406, -2739669284, -2739669283),
    (4, -86471575608, -86471575607, -83626367313, -83626367312, -2845208295, -2845208294),
    (5, -79204872042, -79204872041, -76118124932, -76118124931, -3086747110, -3086747109),
    (6, -72349767575, -72349767574, -69265007491, -69265007490, -3084760085, -3084760084),
    (7, -70944143900, -70944143899, -68063358972, -68063358971, -2880784928, -2880784927),
    (8, -64089039433, -64089039432, -61684687124, -61684687123, -2404352309, -2404352308),
    (9, -56822335867, -56822335866, -56001298703, -56001298702, -821037164, -821037163),
    (10, -55420214683, -55420214682, -54127825653, -54127825652, -1292389030, -1292389029),
    (11, -53761857306, -53761857305, -51730182731, -51730182730, -2031674576, -2031674575),
    (12, -49115498111, -49115498110, -45360861267, -45360861266, -3754636845, -3754636844),
    (13, -45427475339, -45427475338, -41767225027, -41767225026, -3660250313, -3660250312),
    (14, -39122758768, -39122758767, -35851557046, -35851557045, -3271201722, -3271201721),
    (23, -92756306669, -92756306668, -88503048096, -88503048095, -4253258574, -4253258573),
    (37, -75217271566, -75217271565, -72158981090, -72158981089, -3058290477, -3058290476),
)
FIRST_FAILED = {
    1: (15, 16, 17, 18),
    2: (22, 26, 30),
    3: (27, 28, 31, 32, 35, 36, 39, 40, 41, 43, 44, 45, 47, 48, 49,
        51, 52, 53, 55, 56, 57, 59, 60, 61, 63, 64, 65, 67, 68, 69),
    4: (),
    5: (19, 20, 21, 24, 25, 29, 33, 34, 38, 42, 46, 50, 54, 58, 62, 66, 70),
}
require('runtime_pin', importlib.metadata.version('python-flint') == '0.8.0')
require('runtime_pin', ctx.prec == 256)
require('fixed_box_identity', prod(p**b for p, b in zip(PRIMES, EXPONENTS)) == 5040)
require('fixed_box_identity', prod(PRIMES) == 210)
require('fixed_box_identity', tuple(p**(b+1) for p, b in zip(PRIMES, EXPONENTS)) == LOWER)
require('fixed_box_identity', tuple(p**(b+2) for p, b in zip(PRIMES, EXPONENTS)) == UPPER)
require('fixed_box_identity', prod(LOWER) == A_PRODUCT == 5040 * 210)
require('fixed_box_identity', CAPACITIES == tuple(prod(PRIMES[:i]) for i in range(5)))
for multiplier, mask in CORNERS:
    require('corner_identity', multiplier == prod(PRIMES[i] for i in range(4) if mask >> i & 1))
require('corner_order', len({m for _, m in CORNERS}) == 16)
require('corner_order', all(CORNERS[i][0] < CORNERS[i+1][0] for i in range(15)))

integers = [5040 * multiplier for multiplier, _ in CORNERS]
nodes = {}
raw = []
for slot in range(15):
    active = integers[slot] > 5040
    require('adjacent_eligibility', active == (slot > 0))
    raw.append((slot, [active]))
    if active:
        nodes[slot] = (Fraction(210 * integers[slot]), Fraction(210 * integers[slot+1]))
failed = {slot: guard for guard, slots in FIRST_FAILED.items() for slot in slots}
require('reflection_partition', len(failed) == sum(map(len, FIRST_FAILED.values())) == 54)
for j in range(1, 15):
    a, middle, upper = integers[j-1:j+2]
    X = 210 * a
    for i, (p, b) in enumerate(zip(PRIMES, EXPONENTS)):
        slot = 15 + 4 * (j-1) + i
        E = p**(4 * (2*b+3))
        guards = (a > 5040, p**(4*(b+1)) < X, X*X < E,
                  210**2 * a * middle < E, E < 210**2 * a * upper)
        first = next((g for g, ok in enumerate(guards, 1) if not ok), 0)
        require('reflected_eligibility', first == failed.get(slot, 0))
        raw.append((slot, guards))
        if all(guards):
            nodes[slot] = (Fraction(X), Fraction(E, X))
require('complete_raw_partition', [s for s, _ in raw] == list(range(71)))
require('complete_raw_partition', list(nodes) == list(range(1, 15)) + [23, 37])
require('reflected_endpoint_link', nodes[23] == (3175200, Fraction(17592186044416, 3175200)))
require('reflected_endpoint_link', nodes[37] == (7408800, Fraction(95367431640625, 7408800)))
require('reflected_endpoint_link', nodes[23][1]/210 == Fraction(274877906944, 10418625))
require('reflected_endpoint_link', nodes[37][1]/210 == Fraction(762939453125, 12446784))

h = [arb(p).log() for p in PRIMES]
c = [(b+1)*hi for b, hi in zip(EXPONENTS, h)]
d = [(b+2)*hi for b, hi in zip(EXPONENTS, h)]
fc = [q(Fraction(n-1, n)).log() for n in LOWER]
fd = [q(Fraction(n-1, n)).log() for n in UPPER]
gain = [upper-lower for lower, upper in zip(fc, fd)]
density = [v/hi for v, hi in zip(gain, h)]
for value, (lower, upper) in zip(density, DENSITY_BINS):
    enclosed('density_enclosure', value, lower, upper)
require('density_order', density[0] > density[1] > density[2] > density[3] > 0)
expected = {row[0]: row[1:] for row in NODE_BINS}
require('node_table_identity', set(expected) == set(nodes) and len(NODE_BINS) == 16)
values = {}
rows = []
for slot, (lower_product, upper_product) in nodes.items():
    lo, hi = q(lower_product).log(), q(upper_product).log()
    mu = hi/4
    distances = [(ci-mu).max(lo/4-ci).max(0).min((di-mu).max(lo/4-di).max(0))
                 for ci, di in zip(c, d)]
    radius = (sum(delta*delta for delta in distances)/12).sqrt()
    L, H = mu-radius, mu+3*radius
    require('fixed_support_range', 0 < L < 16)
    require('fixed_support_range', 0 < H < 16)
    psi = f(H) + 3*f(L)
    t = upper_product/A_PRODUCT
    if t == 210:
        D, price, y = sum(fd), arb(0), [arb(1)]*4
    else:
        index = next(i for i in range(4) if CAPACITIES[i] <= t < CAPACITIES[i+1])
        y = [arb(1) if i < index else q(t/CAPACITIES[index]).log()/h[index]
             if i == index else arb(0) for i in range(4)]
        D = sum(fc) + sum(v*yi for v, yi in zip(gain, y))
        price = density[index]
    dual = sum(fc) + price*q(t).log() + sum((v-price*hi_).max(0) for v, hi_ in zip(gain, h))
    require('primal_dual_overlap', (D-dual).contains(0))
    require('capacity_identity_overlap', (sum(hi_*yi for hi_, yi in zip(h, y))-q(t).log()).contains(0))
    G = D-psi
    for value, lower, upper in zip((D, psi, G), expected[slot][::2], expected[slot][1::2]):
        enclosed('node_enclosure', value, lower, upper)
    require('fixed_node_margin', G < -q(Fraction(1, 1250)))
    values[slot] = (D, psi, G, distances)
    rows.append({'slot': slot, 'shifted_endpoint_products': [str(lower_product), str(upper_product)],
                 'closed_mesh_enclosures': expected[slot]})

for slot in nodes:
    if slot != 9:
        require('unique_retained_maximizer', values[9][2] > values[slot][2])
X, Y = 22226400, 31752000
require('maximizer_branch_integer_link', X > 64**4)
for i in (1, 2, 3):
    require('maximizer_branch_integer_link', LOWER[i]**4 < X)
    require('maximizer_branch_integer_link', Y < UPPER[i]**4)
    switch_product = (LOWER[i]*UPPER[i])**4
    require('maximizer_branch_integer_link', X*Y > switch_product if i in (1, 2) else X*Y < switch_product)
alpha, omega = arb(X).log(), arb(Y).log()
branches = [(alpha-24*h[0])/4, (16*h[1]-omega)/4,
            (12*h[2]-omega)/4, (alpha-8*h[3])/4]
for a, b in zip(branches, values[9][3]):
    require('maximizer_branch_positive', a > 0)
    require('maximizer_branch_overlap', (a-b).contains(0))
require('exact_greedy_value', prod(Fraction(n-1, n) for n in (64, 81, 125, 49)) == Fraction(496, 525))
require('exact_greedy_value_overlap', (values[9][0]-q(Fraction(496, 525)).log()).contains(0))
require('legacy_budget_shift', Fraction(X, 210) == 105840)
require('legacy_budget_shift', Fraction(Y, 210) == 151200)
require('rational_margin', Fraction(-821037163, SCALE) < Fraction(-1, 1250))
require('erratum_rational_identity', Fraction(2, 129*3**129)/Fraction(8, 9) == Fraction(9, 4*129*3**129))
program = Path(__file__).read_bytes()
print(json.dumps({
    'status': 'passed', 'python_version': platform.python_version(), 'sys_version': sys.version,
    'python_implementation': platform.python_implementation(), 'python_executable': sys.executable,
    'python_flint_version': importlib.metadata.version('python-flint'),
    'flint_module_version': flint.__version__,
    'flint_library_version': getattr(flint, '__FLINT_VERSION__', getattr(flint, '__flint_version__', None)),
    'precision_bits': ctx.prec,
    'program_sha256': hashlib.sha256(program).hexdigest(), 'program_bytes': len(program),
    'program_lf': program.count(b'\n'), 'checks_by_category': dict(checks),
    'checks_total': sum(checks.values()), 'fixed_boxes': 1, 'raw_slots': 71,
    'active_adjacent_slots': list(range(1, 15)), 'active_reflected_slots': [23, 37],
    'inactive_slots': 55, 'inactive_reflected_by_first_failed_guard': FIRST_FAILED,
    'density_interval_numerators': DENSITY_BINS, 'density_intervals_verified': 4,
    'node_intervals_verified': 48, 'interval_denominator': SCALE, 'rows': rows,
    'unique_retained_maximizer': 9, 'maximum_interval_numerators': [-821037164, -821037163],
    'candidate_boxes_generated': 0, 'GPU_dispatches': 0, 'original_program_executions': 0,
    'proof_boundary': 'Fixed input and rounding certificate only. Continuous-domain coverage, exact primal/price equality and all-real uniqueness require the paper proof; interval overlap alone proves no identity.'
}, sort_keys=True, indent=2))
```
<!-- END FIXED5040 CERTIFICATE -->

## Adapted execution receipt

The adapted artifact ran exactly once, from `/Users/auricstudio/trureturing-qgh-actual-5040-fixed`, starting at `2026-09-09T21:55:01.905026+00:00` and ending at `2026-09-09T21:55:02.679099+00:00`. The process exit was **0**, result status **passed**. Runtime: CPython 3.13.12; full `sys.version`: `3.13.12 (main, Mar 10 2026, 18:26:32) [Clang 21.1.4 ]`; python-flint/module 0.8.0; FLINT 3.3.1; Arb precision 256 bits. Observed interpreter path: `/Users/auricstudio/.cache/uv/builds-v0/.tmpOWCXDz/bin/python`.

Program: 10595 bytes / 205 LF, SHA256 `b8a5972435d74afd0c843057bd6471736db3b7303ddb45a51381bb95d70f0602`. Stdout is the structured certificate result: 7674 bytes, SHA256 `5e3bddc6303b640a53a7926b554e11443d0e3fb95256ab93fe1450877f18ec9e`. **Stderr is empty**, 0 bytes, SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. The invocation is exactly the `uv run` command printed above; no original program was invoked.

The run passed 277 assertions. Exactly **4 density enclosures and 48 node enclosures** reproduce the original caller bins. The remaining 225 assertions are separate fixed input/identity/consistency links, including 2 runtime pins. Counts are assertion calls, not independent theorems or samples.

| Check category | Passed assertions |
| --- | --- |
| `adjacent_eligibility` | 15 |
| `capacity_identity_overlap` | 16 |
| `complete_raw_partition` | 2 |
| `corner_identity` | 16 |
| `corner_order` | 2 |
| `density_enclosure` | 4 |
| `density_order` | 1 |
| `erratum_rational_identity` | 1 |
| `exact_greedy_value` | 1 |
| `exact_greedy_value_overlap` | 1 |
| `fixed_box_identity` | 6 |
| `fixed_node_margin` | 16 |
| `fixed_support_range` | 32 |
| `legacy_budget_shift` | 2 |
| `maximizer_branch_integer_link` | 10 |
| `maximizer_branch_overlap` | 4 |
| `maximizer_branch_positive` | 4 |
| `node_enclosure` | 48 |
| `node_table_identity` | 1 |
| `primal_dual_overlap` | 16 |
| `rational_margin` | 1 |
| `reflected_eligibility` | 56 |
| `reflected_endpoint_link` | 4 |
| `reflection_partition` | 1 |
| `runtime_pin` | 2 |
| `unique_retained_maximizer` | 15 |

Result: one fixed box, 71 raw slots, 14 adjacent plus 2 reflected retained nodes, 55 inactive slots, unique retained maximizer 9 and `Gmax in [-821037164,-821037163]/10^12`. Fixed-node G comparisons are strictly below `-1/1250`. The continuous-domain conclusion and equality classification require the preceding paper proof. No new search scope is claimed.

The original caller's four plus 48 enclosures, the adapted run's four plus 48
enclosures, and all extra fixed proof-input links are distinct provenance records.
The extra checks validate identities, exact eligibility, support inputs, optimizer
consistency, strict finite maximum comparisons, the maximizing distance branches,
budget shifts and the corrected rational remainder constant. They do not add a
continuous quantifier. The original programs were not executed and no searched
range was replayed. Candidate generation, GPU dispatch, extra workers and daemon
counts are zero. No broad build/preflight was run; canonical ingestion's own normal
tool invocation is the sole repository generation command.

## Source identity and canonical boundary

| Source component | Bytes | LF | SHA256 |
| --- | --- | --- | --- |
| prefix | 316724 | 5974 | `9229e2affc81243efcdcbd228058d8ca19cea395630a94ae943afde374157dd2` |
| suffix | 26708 | 514 | `3bf3f9e9adb856305df2bbbfcafc08067f59264a6e44070c4973b7987914b678` |
| whole | 343432 | 6488 | `3d301e8454746ca7af80b6df01ee90b2b2f6993e1cfd7e908aa3fb348426f9f5` |

The entire predecessor prefix is retained, with all historical CAS, YAML and report
bytes. The section heading is structural; all numbered content units require full
span coverage. Canonical fingerprints and cas_ref values use `sha256:`; child atom
IDs remain bare. All automatic children and historical terminal-LF variants are
kept as actually emitted. No producer repair or manual EOF normalization is allowed.
The exact source/report content and executable were prepared before the single
canonical command:

```sh
make ingest BASE=fe3f12abe8bc2e14628a93990fee2755c30da2bd SOURCE=arithmetic-boundary-quantization
```

Its observed output inventory and source-span/ordered-chain checks are recorded
below after generation. The report itself is not selected as a second theory source.
Source, fixed certificate and their canonical bindings form one inseparable content
layer; file count does not justify detaching generated addresses from their source.
All actual generated bytes are preserved and returned unstaged. Caller retains the
later review, sealing, public verification and delivery obligations. Positive-height
17-node guards, all-height density, unreturned C45 mass/tail conclusions, other boxes,
arbitrary shapes/primes, GPU/program/search and Lean/frozen work are outside this layer.

<!-- BEGIN ACTUAL CANONICAL INVENTORY -->

## Actual canonical receipt and coverage limitation

The command above ran once, from `/Users/auricstudio/trureturing-qgh-actual-5040-fixed`, at `2026-09-09T21:59:08.208434+00:00` through `2026-09-09T21:59:27.297311+00:00`. Exit: **0**. Its observed counters were 65 residual-open entries added, 269 existing entries skipped, zero coarse fallbacks, zero open genres, 65 CAS objects written and ledger_changed=true. Stdout: 127 bytes, SHA256 `d4dbde47bf3b10f9142cd614f78000035e64bba3db77c33bf57e1e26be7d8330`. Stderr: empty, 0 bytes, SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. No additional repository generation command was run.

The complete output is 65 CAS files and 65 YAML entries: 64 new-section atoms (21 numbered-unit heads or whole units plus 43 independent table rows), and one historical terminal-LF variant. No chain and no automatic child was emitted. Every address and YAML binding matches its actual CAS bytes. These address checks passed; **entire numbered-unit coverage failed**. Sixteen units match a single complete atom. The five table-containing units do not match the ordered concatenation of their emitted atoms, leaving 2,182 bytes uncovered. The missing data include the original strict-domain definition, density-order conclusion, surviving-slot conclusion, reflected rational endpoints and the finite maximum comparison after their tables. They remain fully present in the source. This is a canonical traceability defect, not a numerical-certificate failure.

Read-only inspection of `GenericAtomizer.cs`, `MarkdownAstAtomizer.cs` and the Markdig table-span adapter explains the observed boundary: each nonheader table row is a separate nonextending claim; it truncates the extending numbered paragraph, and following unnumbered prose is not another claim. The row spans also omit their final pipe and LF. No producer file was changed or separate producer run performed. Independent rows are not relabelled as ordered children. The command's exit 0 is not treated as proof of full-unit coverage.

The task explicitly requires one ingestion and prohibits manual canonical repair. All 130 actual output files are retained, including the partial heads, row atoms and terminal-LF variant. A concrete **unapplied** patch adds `~~~text` / `~~~` around the five existing tables, preserving every table/prose byte and the entire predecessor prefix. Its path is `/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qgh0910-i16-actual-5040-fixed/attempt-1/proposed-source-table-fences.patch`; it has 3417 bytes / 78 LF, SHA256 `8a642a866aea0895f99fa517e283c17b0a07c05ab459dea9ccf7e55f150591ef`. The patch adds 60 bytes and 10 LF; it has not changed the returned source. Applying it and generating its new bindings would require explicit authorization for a second canonical ingestion, preserving all first-run outputs. No such authorization has been assumed. The full canonical completion obligation therefore remains open.

## Complete emitted CAS/YAML bindings

Offsets are zero-based half-open UTF-8 byte spans `[start,end)` in the complete source; lines are one-based inclusive and LF means byte 0x0A. Each row below identifies exactly two output files: `Meta/Digestion/atoms/sha256/<ID>` and `Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/<ID>.yaml`, where ID is the bare hexadecimal suffix of the displayed `sha256:` value. That displayed value is, in every row, **raw_sha256, normalized_sha256 and cas_ref**, with the prefix preserved. Each YAML file is exactly 328 bytes / 7 LF; its own SHA256 is listed separately. Each CAS byte count is `end-start`. All YAML coverage_gids and unresolved_subitems arrays are empty; **ordered_children=[] for every emitted binding**. The row order is source order. These definitions give the full two-path manifest without abbreviating any ID.

| # | Unit / emitted kind | Byte span | Lines | CAS LF / terminal LF | Fingerprints and cas_ref | YAML SHA256 |
| --- | --- | --- | --- | --- | --- | --- |

| 1 | 31.22 / historical EOF variant | [314718,316725) | 5950–5975 | 26 / 2 | `sha256:b66d29c438734b309c1416fbdc0c350fcd50c315b67d697c9d9dc3fbf2f5019e` | `43d7292a002ab4bc57efd716e5d053ee495eccce92ee0731ea6db511a3ba977e` |

| 2 | 32.1 / unit/head | [316793,317790) | 5978–5992 | 15 / 2 | `sha256:577e0ea00b7c003c4a85f9277519129736ba52988fb506df6640363bf72baee2` | `1b22ece9c1996012a6e6b2ab2b9fa8e7a00001e2fad8a869043a439548c91b2f` |

| 3 | 32.2 / unit/head | [317790,318804) | 5993–6011 | 19 / 2 | `sha256:bb70f0b6709196af0ae33eb4e256cf09bcae4df5491f77162a7ef3036639561d` | `b8db18431c3ad61b77b97447a58e7503a6ea32e19dd4522a57428433158348dd` |

| 4 | 32.3 / unit/head | [318804,319380) | 6012–6028 | 17 / 1 | `sha256:a9b72f60803002eff46174c36fb81e6940d2328859ae63ecf5d78d32a1e0bdfa` | `ddef0fa7827909fbb134585666ac88b8447ad0c07076a6f4be791836e11787db` |

| 5 | 32.3 / table row | [319380,319399) | 6029–6029 | 0 / 0 | `sha256:7e55ae8cc41b40b93b9131f14a3742485b253adaf1293b105564be53323e52bb` | `60dce026553bc079d053560ca0df99064d2f7cf79f5d4ac9f717f9389dae10eb` |

| 6 | 32.3 / table row | [319401,319421) | 6030–6030 | 0 / 0 | `sha256:a2b2849f37cf52da104f5b58fe3236e4fb8d88f93c3a05d76ccb8aca0cdf5390` | `0d0875578b91a8d694d01a9af4d1d3e4c348c5ead464e0f0a239d339494cfb0f` |

| 7 | 32.3 / table row | [319423,319443) | 6031–6031 | 0 / 0 | `sha256:760235d950de6dd8c39c6dd25d0912fb4afb0d2f75244a8734d9935e644babf4` | `3c3cf917d34527085d0478e3ef7af2d8f84eb2713db0ef83c5ea6c12a3d42292` |

| 8 | 32.3 / table row | [319445,319465) | 6032–6032 | 0 / 0 | `sha256:ba45b796d57e465a3a1da2d8f2fce55bd4907a1641e40a30e71744b2c1b39078` | `dc018d75638b6044547919d3591aa8ba9efe3fe3a8b6a30179e3ee61496955a5` |

| 9 | 32.3 / table row | [319467,319487) | 6033–6033 | 0 / 0 | `sha256:740e47a7104d88dd907af0fcd6ec4ad204111113492ebdde8b49189cef9ba8f9` | `f8aebe3ca0e8432e957db92853bc4e9b425638cee2e7c332477d1979024f9154` |

| 10 | 32.3 / table row | [319489,319509) | 6034–6034 | 0 / 0 | `sha256:d24087583467f7500ed53fe28cfe2f4e4aae98a687683b8fbabfa099a74950e6` | `1ecb0ba6681399f02621365b87e6bcb13276d2e518fb1530e09a95ea52e3dc63` |

| 11 | 32.3 / table row | [319511,319532) | 6035–6035 | 0 / 0 | `sha256:6b1c61d35af4bdcc2732a53a0aaa1965e59f6844d042e6198674ee0892bc268a` | `8275a8e4bea376ceaa76be5ad841af2c2c33dd433059b02fcf3d8392cacc7a36` |

| 12 | 32.3 / table row | [319534,319555) | 6036–6036 | 0 / 0 | `sha256:e4953539a0d59ac7bae8a3227240b9b4dd2fdd30576be9cba516a58645d56401` | `16e0b420798ad4d3a2517ddc8e4a468829dda136b1fbba454d954ab2edcfc5f3` |

| 13 | 32.3 / table row | [319557,319578) | 6037–6037 | 0 / 0 | `sha256:53b3b4f40651218ae280a983a76fab06c35912c7e6a85f1bc323ad8931cf86f8` | `a6d6a4a4c8208ecc7f241c058ab76958c6f94e034fe16d390161a6c66a1bf1f1` |

| 14 | 32.3 / table row | [319580,319603) | 6038–6038 | 0 / 0 | `sha256:62fe2f2deaeb7b78d6d306710ed8830d9b313a27aad55a963f9504a9ee463b96` | `8ad910dbe6d73304b5e5c3bcf2bb4f8892daf72f46511f89efdbe8e4e24b27d2` |

| 15 | 32.3 / table row | [319605,319628) | 6039–6039 | 0 / 0 | `sha256:5deaed73fb39f91993b52d47b33fb3ad114a53a6f165e140378ad610f3a939c9` | `e1344e710d58b51e80a928fa150f64422984a4ec9b09098d0c7cc499a6096954` |

| 16 | 32.3 / table row | [319630,319654) | 6040–6040 | 0 / 0 | `sha256:706b18955e70dd2b28628a67e9609f5166150d3ed3e3f0c84ce3fef12fa5bb73` | `b5948daa07b8b6f4219793a6a97b6a8829864794b333f47e1b30e9f21756505f` |

| 17 | 32.3 / table row | [319656,319680) | 6041–6041 | 0 / 0 | `sha256:72b7243b07434ab6f5c790b9fc53c0ba474649957b54b77abe3c31c1e6857840` | `7efb2e8b3c090c30174d8f85d55dad7d9f344e4af0747c580066a7351a9e3b64` |

| 18 | 32.3 / table row | [319682,319706) | 6042–6042 | 0 / 0 | `sha256:dd131b4e1db3a0022c8f4b52f2b620dd2043592bd2cc00c6648db2d12dfda095` | `2bd438f160c4ad504a1ad018637458ccbd657e8dcecd33b82403f044421c4511` |

| 19 | 32.3 / table row | [319708,319733) | 6043–6043 | 0 / 0 | `sha256:9fe7ba3b8c5dd596cd5b661040a32626aa1763136f377d15518df8c1b2d8f351` | `ee5688e77f8920810354e4b0debb609a979cddb6eb434202c25a893d06802a82` |

| 20 | 32.3 / table row | [319735,319761) | 6044–6044 | 0 / 0 | `sha256:6e0da5c1242f0ce1d310500323a2243b1e39d1258ed9a4da2b4c3a2953f5bf75` | `056ffb5e919aee88d6e6097faf47371f45cb2ca096e88eca14b89d81fb8705ba` |

| 21 | 32.4 / unit/head | [320501,321600) | 6058–6085 | 28 / 2 | `sha256:67a340ef888de9e231fd65ab279997a59d5215a482a77f2ca115aa6bab25eabe` | `2e707e920bff67f6ddcbe2552b2953ed5c9178780edee15657cb0aa0ce39549a` |

| 22 | 32.5 / unit/head | [321600,322269) | 6086–6100 | 15 / 2 | `sha256:dc7e472bfd09c2e5ad8ca57c353fd501607d33b6160e91c1f84632b58c73852b` | `ab40e9224624b8584f1ec11a5f867fa971a3c29930ff1e0e8913c973d0973eec` |

| 23 | 32.6 / unit/head | [322269,322863) | 6101–6113 | 13 / 2 | `sha256:b812d431e527f840da3c065dcc99703aacf85c8e84c50f0943bafa95f2ebedcd` | `4eb197ad66a0461427c4427bb8df7281904f12211d2e588376c615aa1e7ec0c8` |

| 24 | 32.7 / unit/head | [322863,323235) | 6114–6123 | 10 / 1 | `sha256:9041c9e77ca1aca2c455d95519fa5a381f2622af593ebdff2270cc6a6783c98b` | `5fd3cc7e0c0c8cb2ec1d493e6b5250d4eb1ebfe3dd2d8419e234176e4ff36d2c` |

| 25 | 32.7 / table row | [323235,323267) | 6124–6124 | 0 / 0 | `sha256:ef2ae0bce82fc2c30470ba93ed1cb2fe90a531ebd79d6456a091b0379269c0ba` | `ab4ebc940dd480c24e210774c985a9da20eb9ae5848d7b6fc53ea28310a33eae` |

| 26 | 32.7 / table row | [323269,323301) | 6125–6125 | 0 / 0 | `sha256:15e66db0a5fbc6c50026db8014f5e12800b249961a1284bfb17438e2bfc7aafd` | `18f992dcbb9769aef522e79dc0d3f3e0eebeaf4dd2660f7cbbae152b4e624270` |

| 27 | 32.7 / table row | [323303,323335) | 6126–6126 | 0 / 0 | `sha256:53ff4a3e9f1d7f4e673e0119e934961ae9a086e8f5db97aae2ce2c9586fdc01b` | `95371bf3c0b3dcc9522b827a93f1c109690a2c97f100e28058bd2afece0e4f54` |

| 28 | 32.7 / table row | [323337,323367) | 6127–6127 | 0 / 0 | `sha256:33b69d53ba97adbc5a181d8008c626d6a39a9368dd800fd95e001f7901f3b0b4` | `c5c103d5151d459f135eaf8a14c9a408a4ceac0d23ae130a04974dc1eacafcf7` |

| 29 | 32.8 / unit/head | [323543,325212) | 6132–6165 | 34 / 2 | `sha256:bfabe3fcb9e5e69459e48e7d26c86be755f98cea19edff3688d6779771d575c1` | `4adeae44054f742adfb74578e5fe8732e33ec9c3152bfab0f940f214c20d756c` |

| 30 | 32.9 / unit/head | [325212,325804) | 6166–6176 | 11 / 2 | `sha256:edc7df17929ebaa65f2378f7723066c9580cd6569bb6eb9a800408e47b96dd86` | `8e36318e4081f6ede26e79fdab25a0e742b21c53851653145a5a483e660b075c` |

| 31 | 32.10 / unit/head | [325804,326549) | 6177–6193 | 17 / 2 | `sha256:e2dddcccb5498bba7dfcd8bf7e660b29f7280ac0c9d9a3815809032a12e48cbf` | `40aad0056772759ecc880c3cbf07c23be9f163e004135411d37b3b2d4c937ee0` |

| 32 | 32.11 / unit/head | [326549,327761) | 6194–6221 | 28 / 2 | `sha256:d5e64f4c4a5b37d1666829475dbd2c6b834970ec90fea63418575ab70d02af82` | `cb49bd094c7fb315082c2d21d6e24b3b77ddd9889eaaa707a12e2b03adce64b1` |

| 33 | 32.12 / unit/head | [327761,328689) | 6222–6239 | 18 / 2 | `sha256:5145aee91880772394bb9153a65de8e534ccfcab3d4500ab62bf9aa74655aa82` | `8e7895fdfb0e8e57ceef9ab9bc2964203458abb98cb6ddb7f00c8ddc2e229bc2` |

| 34 | 32.13 / unit/head | [328689,329811) | 6240–6269 | 30 / 1 | `sha256:d9febb64631bf43aadc83ab5bdfe774d0eb4559a8aeb4ba458ac72689f039519` | `e4283afac140294f468688d675c4168db2795760cbec36fd8ecdff224ef6af07` |

| 35 | 32.13 / table row | [329811,329829) | 6270–6270 | 0 / 0 | `sha256:8632ed68e0330e692df73bb26f3683422284b2f14e674b7fd826d4be917809d7` | `a3f8009fe290c8dd6d2d0463e211a668153aa7925311be7ef829325ab7cebce7` |

| 36 | 32.13 / table row | [329831,329846) | 6271–6271 | 0 / 0 | `sha256:d8d63c24d67c3b97446285ecb92f0060cd168204cbd3643a213943ad7adff0e0` | `7952ba8a9cad4b769df110fc40ecc705d15ca7d7c17c76587891bfdd06a28680` |

| 37 | 32.13 / table row | [329848,329944) | 6272–6272 | 0 / 0 | `sha256:d45b588fa94c70d6a039f4eb89f14df5775ae1738934c86b33b93e2940464eed` | `2c2720b6c46b1860ea7916ee590379acd4f02c5c542230f8b91ed2e86330b637` |

| 38 | 32.13 / table row | [329946,329959) | 6273–6273 | 0 / 0 | `sha256:a50c00cf3946f0523f5d8b916406b25fe0cd4a1cb6a495ab842cfb08e0576faf` | `113258b39839011fc6c3551bbdb9d5fadda68d6a7b963a679edac38d4e26ab6b` |

| 39 | 32.13 / table row | [329961,330018) | 6274–6274 | 0 / 0 | `sha256:df6550cf9f2398b1173c45ce1d2b03407561491f8fab4296fa8b6cd9d9f5c0ef` | `0f257f9280a547b7802a91f9a72d07a59665ecebbcef27bfe77a7079ce01b8fb` |

| 40 | 32.14 / unit/head | [330208,330476) | 6280–6283 | 4 / 1 | `sha256:01e61aee85549b1df36e0119c10e1f6305b9fdb0e5e50be62859dd7e18c7ce4d` | `29e055c625e88509b80116892aaa93d1a388bb459991b61301842da67fe4cd9c` |

| 41 | 32.14 / table row | [330476,330583) | 6284–6284 | 0 / 0 | `sha256:eb8e8ff664256ff0cc6dcd3671557cea4ba762b32fd46a498cb33eb6d63149f7` | `3e197de98b8c441a0ac1e1430dc92efebcb8f74eb2ce046e508a398fab595929` |

| 42 | 32.14 / table row | [330585,330692) | 6285–6285 | 0 / 0 | `sha256:47015a272b045eb0281e555492115edd4c1bf5e32c14dde277e624c820c2abce` | `331ce8523123c06de0fc331771a4e235255c1dfdde8240347bff4cbff3c48d26` |

| 43 | 32.15 / unit/head | [331408,331889) | 6304–6310 | 7 / 1 | `sha256:2b4c02c06144ba1acf56a23936ca14876b9530ea69d43db3ccc99bb8953df956` | `3bded5dba7509647de550e40f7fd9d486238a0856add0205c7b3d305f235eef7` |

| 44 | 32.15 / table row | [331889,331983) | 6311–6311 | 0 / 0 | `sha256:8c0f1c1360e746bb191856570ea96923ac97bc1564ac555d9066c64e72319c82` | `f53eb9eb862aae936a8ca4bd8bf964aeb5d894a9ec2e365403e931f7bd04cf22` |

| 45 | 32.15 / table row | [331985,332077) | 6312–6312 | 0 / 0 | `sha256:42f5d91960995b17a9049a75fc5b07cb5e3903a8d3414309ab9d7f1d9bce9a85` | `369bec994f6ae8f68aa8a4c5d79a82df5ed3129950f2c3594ad97280378fdda3` |

| 46 | 32.15 / table row | [332079,332171) | 6313–6313 | 0 / 0 | `sha256:4bd965f152318e673854917aa9a53312cb026ff441b827ca313ab386330b08b5` | `99315e6f9574bd2b5e4e7c2fd9bb210211cb023168036c6a7cf06221e2f079e9` |

| 47 | 32.15 / table row | [332173,332265) | 6314–6314 | 0 / 0 | `sha256:f9ca15f38e1c863bd691fee53774eb8fb4da56eb5350d4b2a45237367141fa5a` | `31d73d1b56a2728f1f94871ec3320c34f88d3b669f23a59b6252c1ecb73c6b00` |

| 48 | 32.15 / table row | [332267,332359) | 6315–6315 | 0 / 0 | `sha256:3215d2768beb6710fca5b221285a27e140fc364dc26053cde12bf0c914358255` | `59e2afecea983a47cecfa869e0ed84c9d214fba63dab992a83a56d17eced16c6` |

| 49 | 32.15 / table row | [332361,332453) | 6316–6316 | 0 / 0 | `sha256:0edeb29acbbeee54c4ba248b302c800b91abbfb635eed06bf9a9ff3b77d860a2` | `602628284ae6cc38bc18b6f87c409c14e53c1229a55a64ae26ac170949289080` |

| 50 | 32.15 / table row | [332455,332547) | 6317–6317 | 0 / 0 | `sha256:7e8ea34e0dbf94e984f65610fdd650b309f1a8b4a32971dd17cc09b7fd4ffd46` | `5ee52777d044f2ef10ea329ec1668e41c4dd4d47604ff424feec0efe3b538703` |

| 51 | 32.15 / table row | [332549,332641) | 6318–6318 | 0 / 0 | `sha256:815250d050a520815c406b9eb6faddc38b4962e21179452f94efe5da74517f1c` | `9d492685f4ae40ce956fccaeb5cd95a24e0d4910cd3aa6fb5e85481ef3330732` |

| 52 | 32.15 / table row | [332643,332733) | 6319–6319 | 0 / 0 | `sha256:b2a648b5ecead5f43a565d2650ae04de4c64c3afc5396eb613f9e28048abd22c` | `bd430597c22514e2c923e34fee7b37f4708b028cd46981d8bb0be0e6cfd86a3e` |

| 53 | 32.15 / table row | [332735,332828) | 6320–6320 | 0 / 0 | `sha256:fe68b15039cc9901262b44c5a22b6bec3647c27671607568df8a1840392bf682` | `453f00c78e93e4706369b68a0db9d107dc3cfb21a452ae022c5a7efd911ddd49` |

| 54 | 32.15 / table row | [332830,332923) | 6321–6321 | 0 / 0 | `sha256:9b4bc9f73af1c3322539aa967689ee148c4c435bb1a489f837dca7b82843e129` | `778dcc4a991d0af89cba3e3a9408dc07c3261c5963724958b67d6ac8a3b0a5dc` |

| 55 | 32.15 / table row | [332925,333018) | 6322–6322 | 0 / 0 | `sha256:9fc0199306f46b9f17984da4b460bb43a6e0d23de53be0f20332e9df078b47eb` | `fcccfdffba584aa5b4ebcb74f17c692ddc9c2748713cbc2060c8cd8975b624b5` |

| 56 | 32.15 / table row | [333020,333113) | 6323–6323 | 0 / 0 | `sha256:deb8fcda5f9e82e26d4378937adef029805d5dfbf655fe28cba8f6f1bc5f03f3` | `5f8afcb4411d7e352ee0b4b31163f49ed5e47d1d46353cac7fa6d80904d79e46` |

| 57 | 32.15 / table row | [333115,333208) | 6324–6324 | 0 / 0 | `sha256:ab781bf5011ef1b8c309b7cd2039008b8c2be705763a8588682380b4621912c9` | `1334996fba2b831e05ea0c98c8e00823cb89a64d3443b8315ffc08f65f0b203d` |

| 58 | 32.15 / table row | [333210,333303) | 6325–6325 | 0 / 0 | `sha256:1f5a16b5d2184f367c6746951e4ed434693d8b70a59c22012c29b8dd757c9405` | `659ad1c371fc7318d3b06caff0eb00a4144534c66eb677794f253260f8af0fe2` |

| 59 | 32.15 / table row | [333305,333398) | 6326–6326 | 0 / 0 | `sha256:7c8f235bb7de9a50d60d9ae3a90d499dc6dfc42830508d37c5c3e82afaa20c4f` | `6638b0071168d5905f00d97c4c87bd63875b881e0578fee06076cb4325768b2c` |

| 60 | 32.16 / unit/head | [333682,335097) | 6333–6369 | 37 / 2 | `sha256:6b9de42b2b39e8047434fd00688dde1c2ec1b686815d8390138e08ea9d2b4f1f` | `43f043a0cae41a31b73e10515db217a8c61dca0f14cd6b534dc28e8fe8a4b0f2` |

| 61 | 32.17 / unit/head | [335097,336122) | 6370–6389 | 20 / 2 | `sha256:b494ca333580108b2deb6550e7123a7e08226df26dde679a3aabf52ac6d48df4` | `c782d591c87cc9220c7beba2551f6e7f573f3500444ba9a8e86db8c81679897e` |

| 62 | 32.18 / unit/head | [336122,337486) | 6390–6415 | 26 / 2 | `sha256:6f781365c3476b18072106757c1a1a873972e8de0c5fed7b1aae92f150140ac1` | `3c436f9e88edccc7bb53aed4e16fc7073428f20e430cf1a3b4c60ac998686c93` |

| 63 | 32.19 / unit/head | [337486,339141) | 6416–6436 | 21 / 2 | `sha256:998b44b7a9dd7706d0d2b3b3d2c3cc3ad984ea49260563741f5082a5fcbb872f` | `d17f1439a835b73dc9675fd846acd02e735841dd6ff918f6d73f620a14f141b4` |

| 64 | 32.20 / unit/head | [339141,341076) | 6437–6458 | 22 / 2 | `sha256:3ac23b4b613f6b57cc186bea84165e3aaa9f1b80ccd97d61467732d3c48f92c5` | `8e2eefec935a47381d9edfb1ae1122bd2712edc1eb312040f639aed90069cbca` |

| 65 | 32.21 / unit/head | [341076,343432) | 6459–6488 | 30 / 1 | `sha256:9ee4f78f7fd25b90c4b6fbf4af060e9c82cbf7ba12d1184d6e14e01c3fff3e1c` | `5637a58624730d078318732b9adfc5e84cc91937609fcff29754e06d8058d806` |


## Entire numbered-unit spans and ordered concatenations

The full-unit fingerprint below hashes every source byte from the bold numbered lead to the next numbered lead (or source EOF), including tables and following prose. For incomplete units it is an expected source fingerprint, **not an emitted cas_ref**. No parent chain is claimed. The later ordered lists contain bare emitted atom IDs, exactly in source order; comparing their raw-byte concatenation with each complete unit passes for 16 units and fails for the five indicated units.

| Unit | Entire byte span | Lines | Bytes / LF | Full-unit fingerprint | Concatenation | Missing bytes |
| --- | --- | --- | --- | --- | --- | --- |

| 32.1 | [316793,317790) | 5978–5992 | 997 / 15 | `sha256:577e0ea00b7c003c4a85f9277519129736ba52988fb506df6640363bf72baee2` | equal | 0 |

| 32.2 | [317790,318804) | 5993–6011 | 1014 / 19 | `sha256:bb70f0b6709196af0ae33eb4e256cf09bcae4df5491f77162a7ef3036639561d` | equal | 0 |

| 32.3 | [318804,320501) | 6012–6057 | 1697 / 46 | `sha256:87b286a5f6a8ed6bee5813aa739978e038ecc4562038a0e2f9f02cc4cb5442ab` | FAILED | 770 |

| 32.4 | [320501,321600) | 6058–6085 | 1099 / 28 | `sha256:67a340ef888de9e231fd65ab279997a59d5215a482a77f2ca115aa6bab25eabe` | equal | 0 |

| 32.5 | [321600,322269) | 6086–6100 | 669 / 15 | `sha256:dc7e472bfd09c2e5ad8ca57c353fd501607d33b6160e91c1f84632b58c73852b` | equal | 0 |

| 32.6 | [322269,322863) | 6101–6113 | 594 / 13 | `sha256:b812d431e527f840da3c065dcc99703aacf85c8e84c50f0943bafa95f2ebedcd` | equal | 0 |

| 32.7 | [322863,323543) | 6114–6131 | 680 / 18 | `sha256:f8d7841cfb8821ec298729281b73bbb21e7a8290667efa94a2da8acb8bb08dc1` | FAILED | 182 |

| 32.8 | [323543,325212) | 6132–6165 | 1669 / 34 | `sha256:bfabe3fcb9e5e69459e48e7d26c86be755f98cea19edff3688d6779771d575c1` | equal | 0 |

| 32.9 | [325212,325804) | 6166–6176 | 592 / 11 | `sha256:edc7df17929ebaa65f2378f7723066c9580cd6569bb6eb9a800408e47b96dd86` | equal | 0 |

| 32.10 | [325804,326549) | 6177–6193 | 745 / 17 | `sha256:e2dddcccb5498bba7dfcd8bf7e660b29f7280ac0c9d9a3815809032a12e48cbf` | equal | 0 |

| 32.11 | [326549,327761) | 6194–6221 | 1212 / 28 | `sha256:d5e64f4c4a5b37d1666829475dbd2c6b834970ec90fea63418575ab70d02af82` | equal | 0 |

| 32.12 | [327761,328689) | 6222–6239 | 928 / 18 | `sha256:5145aee91880772394bb9153a65de8e534ccfcab3d4500ab62bf9aa74655aa82` | equal | 0 |

| 32.13 | [328689,330208) | 6240–6279 | 1519 / 40 | `sha256:81c716399c07eb0195a5da9dbe49719c9471887fd034ec93abe64c1e58837814` | FAILED | 198 |

| 32.14 | [330208,331408) | 6280–6303 | 1200 / 24 | `sha256:c290e2cda39466a2ce59c49cea6bbcc9026de0fc06b233b1f8dfaa791cb0a97d` | FAILED | 718 |

| 32.15 | [331408,333682) | 6304–6332 | 2274 / 29 | `sha256:2cb44c2ecdb788d954e0696ca7e8073c53e491d9102bbbda3ef0b81220f6d0fc` | FAILED | 314 |

| 32.16 | [333682,335097) | 6333–6369 | 1415 / 37 | `sha256:6b9de42b2b39e8047434fd00688dde1c2ec1b686815d8390138e08ea9d2b4f1f` | equal | 0 |

| 32.17 | [335097,336122) | 6370–6389 | 1025 / 20 | `sha256:b494ca333580108b2deb6550e7123a7e08226df26dde679a3aabf52ac6d48df4` | equal | 0 |

| 32.18 | [336122,337486) | 6390–6415 | 1364 / 26 | `sha256:6f781365c3476b18072106757c1a1a873972e8de0c5fed7b1aae92f150140ac1` | equal | 0 |

| 32.19 | [337486,339141) | 6416–6436 | 1655 / 21 | `sha256:998b44b7a9dd7706d0d2b3b3d2c3cc3ad984ea49260563741f5082a5fcbb872f` | equal | 0 |

| 32.20 | [339141,341076) | 6437–6458 | 1935 / 22 | `sha256:3ac23b4b613f6b57cc186bea84165e3aaa9f1b80ccd97d61467732d3c48f92c5` | equal | 0 |

| 32.21 | [341076,343432) | 6459–6488 | 2356 / 30 | `sha256:9ee4f78f7fd25b90c4b6fbf4af060e9c82cbf7ba12d1184d6e14e01c3fff3e1c` | equal | 0 |


Ordered emitted atom IDs per numbered unit (these are not fabricated chain children):

```json
{
  "32.1": [
    "577e0ea00b7c003c4a85f9277519129736ba52988fb506df6640363bf72baee2"
  ],
  "32.2": [
    "bb70f0b6709196af0ae33eb4e256cf09bcae4df5491f77162a7ef3036639561d"
  ],
  "32.3": [
    "a9b72f60803002eff46174c36fb81e6940d2328859ae63ecf5d78d32a1e0bdfa",
    "7e55ae8cc41b40b93b9131f14a3742485b253adaf1293b105564be53323e52bb",
    "a2b2849f37cf52da104f5b58fe3236e4fb8d88f93c3a05d76ccb8aca0cdf5390",
    "760235d950de6dd8c39c6dd25d0912fb4afb0d2f75244a8734d9935e644babf4",
    "ba45b796d57e465a3a1da2d8f2fce55bd4907a1641e40a30e71744b2c1b39078",
    "740e47a7104d88dd907af0fcd6ec4ad204111113492ebdde8b49189cef9ba8f9",
    "d24087583467f7500ed53fe28cfe2f4e4aae98a687683b8fbabfa099a74950e6",
    "6b1c61d35af4bdcc2732a53a0aaa1965e59f6844d042e6198674ee0892bc268a",
    "e4953539a0d59ac7bae8a3227240b9b4dd2fdd30576be9cba516a58645d56401",
    "53b3b4f40651218ae280a983a76fab06c35912c7e6a85f1bc323ad8931cf86f8",
    "62fe2f2deaeb7b78d6d306710ed8830d9b313a27aad55a963f9504a9ee463b96",
    "5deaed73fb39f91993b52d47b33fb3ad114a53a6f165e140378ad610f3a939c9",
    "706b18955e70dd2b28628a67e9609f5166150d3ed3e3f0c84ce3fef12fa5bb73",
    "72b7243b07434ab6f5c790b9fc53c0ba474649957b54b77abe3c31c1e6857840",
    "dd131b4e1db3a0022c8f4b52f2b620dd2043592bd2cc00c6648db2d12dfda095",
    "9fe7ba3b8c5dd596cd5b661040a32626aa1763136f377d15518df8c1b2d8f351",
    "6e0da5c1242f0ce1d310500323a2243b1e39d1258ed9a4da2b4c3a2953f5bf75"
  ],
  "32.4": [
    "67a340ef888de9e231fd65ab279997a59d5215a482a77f2ca115aa6bab25eabe"
  ],
  "32.5": [
    "dc7e472bfd09c2e5ad8ca57c353fd501607d33b6160e91c1f84632b58c73852b"
  ],
  "32.6": [
    "b812d431e527f840da3c065dcc99703aacf85c8e84c50f0943bafa95f2ebedcd"
  ],
  "32.7": [
    "9041c9e77ca1aca2c455d95519fa5a381f2622af593ebdff2270cc6a6783c98b",
    "ef2ae0bce82fc2c30470ba93ed1cb2fe90a531ebd79d6456a091b0379269c0ba",
    "15e66db0a5fbc6c50026db8014f5e12800b249961a1284bfb17438e2bfc7aafd",
    "53ff4a3e9f1d7f4e673e0119e934961ae9a086e8f5db97aae2ce2c9586fdc01b",
    "33b69d53ba97adbc5a181d8008c626d6a39a9368dd800fd95e001f7901f3b0b4"
  ],
  "32.8": [
    "bfabe3fcb9e5e69459e48e7d26c86be755f98cea19edff3688d6779771d575c1"
  ],
  "32.9": [
    "edc7df17929ebaa65f2378f7723066c9580cd6569bb6eb9a800408e47b96dd86"
  ],
  "32.10": [
    "e2dddcccb5498bba7dfcd8bf7e660b29f7280ac0c9d9a3815809032a12e48cbf"
  ],
  "32.11": [
    "d5e64f4c4a5b37d1666829475dbd2c6b834970ec90fea63418575ab70d02af82"
  ],
  "32.12": [
    "5145aee91880772394bb9153a65de8e534ccfcab3d4500ab62bf9aa74655aa82"
  ],
  "32.13": [
    "d9febb64631bf43aadc83ab5bdfe774d0eb4559a8aeb4ba458ac72689f039519",
    "8632ed68e0330e692df73bb26f3683422284b2f14e674b7fd826d4be917809d7",
    "d8d63c24d67c3b97446285ecb92f0060cd168204cbd3643a213943ad7adff0e0",
    "d45b588fa94c70d6a039f4eb89f14df5775ae1738934c86b33b93e2940464eed",
    "a50c00cf3946f0523f5d8b916406b25fe0cd4a1cb6a495ab842cfb08e0576faf",
    "df6550cf9f2398b1173c45ce1d2b03407561491f8fab4296fa8b6cd9d9f5c0ef"
  ],
  "32.14": [
    "01e61aee85549b1df36e0119c10e1f6305b9fdb0e5e50be62859dd7e18c7ce4d",
    "eb8e8ff664256ff0cc6dcd3671557cea4ba762b32fd46a498cb33eb6d63149f7",
    "47015a272b045eb0281e555492115edd4c1bf5e32c14dde277e624c820c2abce"
  ],
  "32.15": [
    "2b4c02c06144ba1acf56a23936ca14876b9530ea69d43db3ccc99bb8953df956",
    "8c0f1c1360e746bb191856570ea96923ac97bc1564ac555d9066c64e72319c82",
    "42f5d91960995b17a9049a75fc5b07cb5e3903a8d3414309ab9d7f1d9bce9a85",
    "4bd965f152318e673854917aa9a53312cb026ff441b827ca313ab386330b08b5",
    "f9ca15f38e1c863bd691fee53774eb8fb4da56eb5350d4b2a45237367141fa5a",
    "3215d2768beb6710fca5b221285a27e140fc364dc26053cde12bf0c914358255",
    "0edeb29acbbeee54c4ba248b302c800b91abbfb635eed06bf9a9ff3b77d860a2",
    "7e8ea34e0dbf94e984f65610fdd650b309f1a8b4a32971dd17cc09b7fd4ffd46",
    "815250d050a520815c406b9eb6faddc38b4962e21179452f94efe5da74517f1c",
    "b2a648b5ecead5f43a565d2650ae04de4c64c3afc5396eb613f9e28048abd22c",
    "fe68b15039cc9901262b44c5a22b6bec3647c27671607568df8a1840392bf682",
    "9b4bc9f73af1c3322539aa967689ee148c4c435bb1a489f837dca7b82843e129",
    "9fc0199306f46b9f17984da4b460bb43a6e0d23de53be0f20332e9df078b47eb",
    "deb8fcda5f9e82e26d4378937adef029805d5dfbf655fe28cba8f6f1bc5f03f3",
    "ab781bf5011ef1b8c309b7cd2039008b8c2be705763a8588682380b4621912c9",
    "1f5a16b5d2184f367c6746951e4ed434693d8b70a59c22012c29b8dd757c9405",
    "7c8f235bb7de9a50d60d9ae3a90d499dc6dfc42830508d37c5c3e82afaa20c4f"
  ],
  "32.16": [
    "6b9de42b2b39e8047434fd00688dde1c2ec1b686815d8390138e08ea9d2b4f1f"
  ],
  "32.17": [
    "b494ca333580108b2deb6550e7123a7e08226df26dde679a3aabf52ac6d48df4"
  ],
  "32.18": [
    "6f781365c3476b18072106757c1a1a873972e8de0c5fed7b1aae92f150140ac1"
  ],
  "32.19": [
    "998b44b7a9dd7706d0d2b3b3d2c3cc3ad984ea49260563741f5082a5fcbb872f"
  ],
  "32.20": [
    "3ac23b4b613f6b57cc186bea84165e3aaa9f1b80ccd97d61467732d3c48f92c5"
  ],
  "32.21": [
    "9ee4f78f7fd25b90c4b6fbf4af060e9c82cbf7ba12d1184d6e14e01c3fff3e1c"
  ]
}
```

Every uncovered span is listed below. The small 2-byte gaps are the literal final pipe and LF of independent table rows. The longer terminal gaps contain the final row separator and the full following prose. None is discarded as a merely structural heading.

| Unit | Missing byte span | Lines | Bytes / LF | Missing-span SHA256 |
| --- | --- | --- | --- | --- |

| 32.3 | [319399,319401) | 6029–6029 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319421,319423) | 6030–6030 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319443,319445) | 6031–6031 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319465,319467) | 6032–6032 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319487,319489) | 6033–6033 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319509,319511) | 6034–6034 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319532,319534) | 6035–6035 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319555,319557) | 6036–6036 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319578,319580) | 6037–6037 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319603,319605) | 6038–6038 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319628,319630) | 6039–6039 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319654,319656) | 6040–6040 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319680,319682) | 6041–6041 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319706,319708) | 6042–6042 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319733,319735) | 6043–6043 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.3 | [319761,320501) | 6044–6057 | 740 / 14 | `1dcb88e62b591605d1d203b263a23c59fb3977c329a0131aa82b1f5ea524e3e8` |

| 32.7 | [323267,323269) | 6124–6124 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.7 | [323301,323303) | 6125–6125 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.7 | [323335,323337) | 6126–6126 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.7 | [323367,323543) | 6127–6131 | 176 / 5 | `57bcbf65a872d21dbb3ac50e41082f0811a3e7728ad10d317fe7ae8f9ac2e602` |

| 32.13 | [329829,329831) | 6270–6270 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.13 | [329846,329848) | 6271–6271 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.13 | [329944,329946) | 6272–6272 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.13 | [329959,329961) | 6273–6273 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.13 | [330018,330208) | 6274–6279 | 190 / 6 | `55762e36a7f4550076c8ef6cb794105f096f3bbce6a73ddbc8b3a80d8c110d2b` |

| 32.14 | [330583,330585) | 6284–6284 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.14 | [330692,331408) | 6285–6303 | 716 / 19 | `f5b77ac0debbecdbf3f8c5cb3b0b9d0151cd0f7dea9bba0607f75f8ea442d7ce` |

| 32.15 | [331983,331985) | 6311–6311 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [332077,332079) | 6312–6312 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [332171,332173) | 6313–6313 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [332265,332267) | 6314–6314 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [332359,332361) | 6315–6315 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [332453,332455) | 6316–6316 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [332547,332549) | 6317–6317 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [332641,332643) | 6318–6318 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [332733,332735) | 6319–6319 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [332828,332830) | 6320–6320 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [332923,332925) | 6321–6321 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [333018,333020) | 6322–6322 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [333113,333115) | 6323–6323 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [333208,333210) | 6324–6324 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [333303,333305) | 6325–6325 | 2 / 1 | `9d5244c50ced231a7bb23d76593f0bce8f8d3ff803dfe514176002739b6f75c1` |

| 32.15 | [333398,333682) | 6326–6332 | 284 / 7 | `f8e9f5c591b44f2309572582437e8222f7bbc282b78d5589e3836b47ddbd6619` |


The section-32 structural preamble occupies [316724,316793) (lines 5975–5977, 69 bytes / 3 LF, SHA256 `504c7cdafc0dff6a1c40cd394bf47b09f003cf66bba95443bfa30ba098ec48a6`). Its first LF is also the actual terminal byte of the historical variant; no source byte was removed or rewritten. Structural-heading atom coverage is not required.


## Historical terminal-LF variant and byte preservation

The producer emitted `sha256:b66d29c438734b309c1416fbdc0c350fcd50c315b67d697c9d9dc3fbf2f5019e` for unit 31.22, source bytes [314718,316725), lines 5950–5975: 2,007 bytes / 26 LF, ending in two LF bytes. It is exactly the preserved historical CAS `sha256:eae7985cf6b6ca0ed4b57eca118b4b48b116ff73442ea4cf699dec0cea6ff3c9` (2,006 bytes / 25 LF, ending in one LF) plus one LF introduced at the append boundary. The old CAS and YAML remain present and unchanged; old YAML SHA256 is `9d992fdcaed68fbacab613efa1445690d111c8181699df8cded036703a180da3`. This new variant is retained exactly, with no EOF normalization.

The complete predecessor source was compared directly with `BASE` and remains byte-identical. A separate complete-byte Git-blob comparison against the immutable BASE tree checked 64,190 historical files: 32,040 CAS files, 32,083 other Digestion files, and 67 reports. No historical path changed. Its path/byte/SHA256/Git-object inventory has 23812851 bytes and SHA256 `54e63139fb30fc90f6090d8073143039927d2085de33d9728cad196bce6fb269` and is returned as a worker artifact. This is preservation verification, not a historical mathematical calculation replay.

The complete changed-file set is the source path above, this report path, and exactly the 130 generated paths expanded from the binding table. No other tracked file changed; the index is empty of changes. The final worker envelope supplies the final source/report identities and every changed path with byte/LF/SHA256 fields, so the report does not attempt to embed its own complete-file hash.

## Execution limitations and remaining handoff

The original primary DisabledError, absent original executable/interpreter/stderr evidence, pinned-documentation HTTP 403, missing pdftotext and limited HKUST glyph extraction remain recorded above. During inventory inspection, a lowercase `metadata` directory lookup failed because the canonical directory is `Meta/Digestion`; inspection then used the actual emitted paths. An initial gap-preview display split a UTF-8 character and raised UnicodeDecodeError; decoding the complete byte slice before shortening the display resolved that read-only diagnostic. Neither attempt changed source, canonical data, input programs or mathematical results. Earlier overlong read output was retrieved in smaller targeted spans. The adapted certificate was executed exactly once, and the canonical command exactly once.

The tracked-source `git diff --check` exited 0 with empty stdout and stderr. A separate read-only `git diff --no-index --check` against `/dev/null` covered all 131 new paths, including the report: 72 returned the expected difference-only exit 1 with no whitespace findings; 59 generated CAS files returned exit 3 with diagnostics (43 row atoms have trailing whitespace and 16 other CAS objects have a new blank line at EOF). Source and report have no whitespace findings. These are actual producer bytes and were not normalized. The initial diagnostic classifier stopped on the first expected exit 1 with empty output; accepting that difference-only status resolved the checker, without rerunning ingestion or mathematical verification.

The source-formatting proposal is not applied. Resolving the five incomplete bindings needs an explicitly authorized follow-up; current coverage is not described as successful delivery. Caller still owns sealing, public byte verification, independent review, ordinary repository gates and final S21 delivery after S20 MERGED. No lifecycle condition was queried or marked complete. GH remains the literal user label; this fixed T=0 upper-bound comparison is not a translated-family theorem, Robin/RH result, novelty/priority claim or Lean freeze.

<!-- END ACTUAL CANONICAL INVENTORY -->
<!-- END HISTORICAL I16 REPORT -->

</details>

## C69 / I23 placement repair and current bindings (2026-09-10)

This note records the own S21 report relocation by the sole Codex CLI I23 worker,
flight `qgh0910-i23-s21-own-report-placement`, attempt 1 / retry budget 1,
under caller-pinned `consensus-rnd:sshx` 1.0.0-beta.42 and
`CODEX_WORKER_SPEC.md`; prior context is repo-prior-exposed. The exact clean
starting HEAD and ingestion BASE were
`18b4ca2e2f282187c7036b78da9455c2e940b43b`, on
`lane/math/quantized-gh-actual-5040-fixed-0910` in the worktree named above.
No additional worker, oracle, review or termination seat was launched.

The report now occupies
`docs/reports/quantized-gh/actual-5040-fixed-box-0910.md`.
Its sole live source destination is in **32.19**, original/current line 6440.
The sole active report backlink remains at original/current line 150, inside
the displayed historical I16 body. Both current relative Markdown links resolve.
Only `quantized-gh/` (13 bytes) was inserted in the source destination, and
only `../` (3 bytes) was inserted before the original report backlink.
Inherited S19/S20 report addresses and all their source bytes are unchanged.

The caller's allowed intake records 48 direct report blobs at measured dev
`45ca4ae3b012cb1f59ff74a84e845691a3f0c99c`, with this own report projecting a
49th against the recorded admission limit 48. That is previous-stage caller
evidence; I23 did not query current dev or run an integration/CI gate. In this
exact target, direct report files decreased from 36 to 35. This own report now
contributes zero direct files to the caller's eventual integrated candidate.

### Narrow navigation exception and exact historical recovery

C69 explicitly permits the three-byte backlink insertion within the historical
display. All earlier statements headed “current”, the old C48 binding table,
all source/report/prefix/hash claims, all provenance and verification statements,
the “preserved verbatim” summary, and the claim that the original I16 report is
one contiguous byte sequence retain their **historical snapshot meaning**.
The C48 statements describe the sealed C48 snapshot at the starting HEAD; the
I16 statements and source 32.21 describe the first I16 return. Their old paths,
commands, line/byte coordinates, ingest counts, failures and delivery status
are historical records, not assertions about this new placement. In particular,
the old C48 “current” 32.19 ID is historical after this address change. The
updated whole-unit table below gives the current binding. Earlier immutable
claims are not rewritten or silently made into claims of literal equality for
the current displayed body with its authorized navigation insertion.

The immutable originals remain available in the
[BASE source](https://github.com/the-omega-institute/trureturing/blob/18b4ca2e2f282187c7036b78da9455c2e940b43b/docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md)
and [BASE report](https://github.com/the-omega-institute/trureturing/blob/18b4ca2e2f282187c7036b78da9455c2e940b43b/docs/reports/actual-5040-fixed-box-0910.md),
and in the caller's allowed source/report snapshots. I23 compared the local Git
blob bytes and supplied snapshots directly; these URLs were not fetched anew.
Recovery uses zero-based half-open UTF-8 byte offsets, with no trimming:

- For the current source `s`, remove exactly `s[338672:338685]`, which equals
  `b'quantized-gh/'`: `s[:338672] + s[338685:]` recovers all 343492 original bytes,
  6498 LF, SHA256 `65f8ebe49381039838524752d4e3c19e4db13bc7046d74030f1acc9bb0f8be20`.
- For the moved report `r`, first take `h = r[:78315]` to exclude this appended
  note, then remove exactly `h[11717:11720]`, which equals `b'../'`:
  `h[:11717] + h[11720:]` recovers all 78312 original bytes, 1088 LF, SHA256
  `2a2c09a38094235089b50ef23a7411ac018c4e7e11ffed9c34d240d83b834592`.
  This prefix before recovery is 78315 bytes, SHA256
  `a24e1431750f1bd73d40195ed275f2d9eaea70fb30e4b8b1ac9b52f3cff93772`.
- The original I16 body occupied report bytes `[10289,78265)`. Its current
  display occupies `[10289,78268)`; remove only the same insertion at body
  offset 1428 to recover 67976 bytes / 956 LF, SHA256
  `290a0a99d77f1030d37c91e7be1f1341dd367c996b3b20e8cbbc2ae84004acb6`.

Every original byte outside these two named insertions is retained. In
particular, all eight historical fenced payloads compare exactly, including
the 10595-byte / 205-LF executable certificate with SHA256
`b8a5972435d74afd0c843057bd6471736db3b7303ddb45a51381bb95d70f0602`;
the existing JSON fence still parses. Raw-primary records, embedded result
bytes, stdout/stderr provenance, literal tables and their hashes are unchanged.
The 71 raw / 16 active / 55 inactive classification, 277 fixed assertions,
2182-byte first-run coverage failure and C48 five-pair repair retain exactly
their recorded mathematical and execution scope. No historical result, raw
envelope or inert log pointer was opened as a separate input or replayed.
For current certificate extraction, use the new report path above in the
unchanged marker-based recipe under “Standalone certificate”; the printed old
path and `uv run` command remain I16's execution receipt. I23 compared the
selected bytes in memory and did not execute or write out the certificate.

### Single current ingestion and complete span accounting

The finished source is 343505 bytes / 6498 LF, SHA256
`6b7b3212af93662b5bba9d9e312e72d05a9cee516a78152d42ab65256b54ed42`.
Its entire 316724-byte predecessor prefix remains exact, SHA256
`9229e2affc81243efcdcbd228058d8ca19cea395630a94ae943afde374157dd2`.
The current suffix is 26781 bytes / 524 LF, SHA256
`49f6721c360950dcc8f6a9059432ceb16aaea46e529a0c91e6b267424cca0bf8`.
Exactly one C69 invocation ran after the source insertion:

```sh
make ingest BASE=18b4ca2e2f282187c7036b78da9455c2e940b43b SOURCE=arithmetic-boundary-quantization
```

It exited 0, started at `2026-09-10T05:04:27.765733+00:00` and ended at
`2026-09-10T05:04:42.141403+00:00`. Its measured counters are
`residual_open_added=1`, `skipped_existing=290`, `coarse_fallbacks=0`,
`open_genres=0`, `cas_objects_written=1`, `ledger_changed=true`.
Stdout was 125 bytes, SHA256
`9efd2027d47989f51871f754507d408657bd741b53d3c6ce9eea5f15c9725b74`;
stderr was empty. This invocation is separate from the two recorded historical
I16/C48 ingests. No second C69 ingest or manual canonical repair occurred.

All 70 original CAS/YAML pairs (65 first-run pairs plus five C48 repair pairs)
match both exact BASE Git blobs and the supplied manifest byte for byte. The
one emitted pair binds the entire new 32.19 span: 1668 bytes / 21 LF, with two
terminal LF bytes, ID
`4b4515e76802e91f956ec04e63de2785119548fe214b27da72bcc064c5cc476d`.
Its YAML is 328 bytes / 7 LF, SHA256
`72d4577487cd229123b3696ca014dc7cf1421828ba620f3d29effc1473854fd0`.
The old 32.19 ID `998b44b7a9dd7706d0d2b3b3d2c3cc3ad984ea49260563741f5082a5fcbb872f`
and its YAML remain unchanged historical evidence. This accounts for every
newly emitted pair; there are 71 cumulative S21 pairs. No new child, parent
chain or inherited terminal-LF variant was emitted. Both old 31.22 LF variants,
the first-run partial/table atoms, and all other historical canonical files
remain intact. No existing canonical or earlier-report path changed.

Every row below equals its complete CAS blob from the bold numbered lead to
the next lead, or EOF for 32.21, including all trailing whitespace. Bare ID
`X` expands to `Meta/Digestion/atoms/sha256/X` and
`Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/X.yaml`.
Each YAML has raw/normalized fingerprints and `cas_ref` equal to `sha256:X`,
empty `coverage_gids` and `receipts.unresolved_subitems`; its ordered atom list
is `[X]`, with no children. All 21 whole-unit comparisons passed: zero gaps,
zero uncovered bytes. Only 32.19 has a new ID; later offsets shift by 13 bytes.

| Unit | Current byte span | Lines | Bytes / LF / terminal LF | Whole-unit ID |
| --- | --- | --- | --- | --- |
| 32.1 | [316793,317790) | 5978-5992 | 997 / 15 / 2 | `577e0ea00b7c003c4a85f9277519129736ba52988fb506df6640363bf72baee2` |
| 32.2 | [317790,318804) | 5993-6011 | 1014 / 19 / 2 | `bb70f0b6709196af0ae33eb4e256cf09bcae4df5491f77162a7ef3036639561d` |
| 32.3 | [318804,320513) | 6012-6059 | 1709 / 48 / 2 | `af2714fed461cdcaf2da2725959e5001e1614a17dc6d10b4ab33ae5729bc32e0` |
| 32.4 | [320513,321612) | 6060-6087 | 1099 / 28 / 2 | `67a340ef888de9e231fd65ab279997a59d5215a482a77f2ca115aa6bab25eabe` |
| 32.5 | [321612,322281) | 6088-6102 | 669 / 15 / 2 | `dc7e472bfd09c2e5ad8ca57c353fd501607d33b6160e91c1f84632b58c73852b` |
| 32.6 | [322281,322875) | 6103-6115 | 594 / 13 / 2 | `b812d431e527f840da3c065dcc99703aacf85c8e84c50f0943bafa95f2ebedcd` |
| 32.7 | [322875,323567) | 6116-6135 | 692 / 20 / 2 | `6a26e45b7ee03e5f635a6f0a250c9da2d851b616db78b20cb6d22cda2fdde2df` |
| 32.8 | [323567,325236) | 6136-6169 | 1669 / 34 / 2 | `bfabe3fcb9e5e69459e48e7d26c86be755f98cea19edff3688d6779771d575c1` |
| 32.9 | [325236,325828) | 6170-6180 | 592 / 11 / 2 | `edc7df17929ebaa65f2378f7723066c9580cd6569bb6eb9a800408e47b96dd86` |
| 32.10 | [325828,326573) | 6181-6197 | 745 / 17 / 2 | `e2dddcccb5498bba7dfcd8bf7e660b29f7280ac0c9d9a3815809032a12e48cbf` |
| 32.11 | [326573,327785) | 6198-6225 | 1212 / 28 / 2 | `d5e64f4c4a5b37d1666829475dbd2c6b834970ec90fea63418575ab70d02af82` |
| 32.12 | [327785,328713) | 6226-6243 | 928 / 18 / 2 | `5145aee91880772394bb9153a65de8e534ccfcab3d4500ab62bf9aa74655aa82` |
| 32.13 | [328713,330244) | 6244-6285 | 1531 / 42 / 2 | `33a959a8ab03c5d5129b81d23df781014dc5b7ad4ca827a28a098b957d57dbb8` |
| 32.14 | [330244,331456) | 6286-6311 | 1212 / 26 / 2 | `5a6ef842e39b9ef4700a2f7503c6e0f5a3334b4dd0e935d89691d81a82a0bd58` |
| 32.15 | [331456,333742) | 6312-6342 | 2286 / 31 / 2 | `c75ebee1711448d758b7599f9e1e76d188879116fe05c22ee5070883da852ad2` |
| 32.16 | [333742,335157) | 6343-6379 | 1415 / 37 / 2 | `6b9de42b2b39e8047434fd00688dde1c2ec1b686815d8390138e08ea9d2b4f1f` |
| 32.17 | [335157,336182) | 6380-6399 | 1025 / 20 / 2 | `b494ca333580108b2deb6550e7123a7e08226df26dde679a3aabf52ac6d48df4` |
| 32.18 | [336182,337546) | 6400-6425 | 1364 / 26 / 2 | `6f781365c3476b18072106757c1a1a873972e8de0c5fed7b1aae92f150140ac1` |
| 32.19 | [337546,339214) | 6426-6446 | 1668 / 21 / 2 | `4b4515e76802e91f956ec04e63de2785119548fe214b27da72bcc064c5cc476d` |
| 32.20 | [339214,341149) | 6447-6468 | 1935 / 22 / 2 | `3ac23b4b613f6b57cc186bea84165e3aaa9f1b80ccd97d61467732d3c48f92c5` |
| 32.21 | [341149,343505) | 6469-6498 | 2356 / 30 / 1 | `9ee4f78f7fd25b90c4b6fbf4af060e9c82cbf7ba12d1184d6e14e01c3fff3e1c` |

### Structural diagnostics and remaining ownership

The tracked delta check `git diff --check 18b4ca2e2f282187c7036b78da9455c2e940b43b --`
exited 0 with empty stdout/stderr. Each of the three untracked additions was
also checked with `git diff --no-index --check -- /dev/null <path>`.
The YAML and moved report each returned exit 1 with empty stdout/stderr:
these are addition-only difference exits, not whitespace findings. The new CAS
returned exit 3 and exactly this diagnostic, with empty stderr:

```text
Meta/Digestion/atoms/sha256/4b4515e76802e91f956ec04e63de2785119548fe214b27da72bcc064c5cc476d:21: new blank line at EOF.
```

The final blank line is part of the complete 32.19 source span and is retained
exactly. Source EOF still has one LF; units 32.1-32.20 each retain two terminal
LF bytes. No whitespace normalization or canonical-byte repair was performed.
The final worker envelope carries all five changed-path identities, full
current bindings, old-pair preservation and exact structural command exits;
its report identity covers this appended note too.

I23 performed zero mathematical program executions, old certificate/test/ingest
replays, candidate generation, GPU/runtime operations, broad builds, Lean or
tool/frozen edits. Only the required ingest's normal tool invocation generated
canonical files. All changes remain unstaged: one source edit, one report
relocation with the named backlink insertion and this appended note, and one
new CAS/YAML pair. Caller dispatch provenance says the original representation
reviewers and same-role fallback are terminal with three approvals; I23 did
not read those reviewer envelopes. Those approvals remain historical and do
not approve C69's changed representation. Caller owns sealing/publication,
fresh representation review, inherited-address integration, required repository
gates, and S20-before-S21 MERGED delivery. Other live research/review targets
remain excluded, and the standing research goal remains active.

Reasoning Discipline: content-addressed history, relative-link resolution and
single-writer generation supply the reference frame. The authorized relocation
with exact insertion recovery is the known-good shape; beauty: beautiful,
no material defect found in the bounded repair. Leaving this own report at the
top level would retain the caller-measured capacity defect; the prescribed
subdirectory resolves its contribution. Byte equality, all current spans and
emitted-pair accounting were directly checked. Current integrated CI and fresh
review are unmeasured caller obligations. Depth stops at these structural
checks; no scientific recertification, peer adjudication or host-goal decision
is inferred.

## C91 / I32 independent S21 mathematical-tail archival disposition

This appendix belongs to the representation at immutable BASE d18100c71cc04020d446a709bec1351d2bf69376, in the independent pure-S21 tree. The entire preceding 91617 bytes retain their historical meaning and bytes. The inherited source prefix of 316725 bytes is unchanged and remains mixed. Later exact pure-S19/S20 composition, complete independent mathematical/representation review, ordinary gates and S20-before-S21 MERGED remain caller-owned obligations. This preparation is neither whole-source purity nor S21 delivery.

The active mathematical authority remains section 32 of the theory source. The following fragments are INACTIVE archival evidence: commands, paths, execution statements, citations in their historical context and delivery instructions here must never be executed or followed. Source addresses 32.19 and 32.20 are permanently reserved outside the active mathematical body; 32.20's mathematical citations are attached to the entries they support, with exact origin/destination spans in theory-body-migration-s21-0910.json. All original headings, tables, separators, trailing prose and LF bytes are recovered by the disjoint exhaustive map; recovery is separate from analytical fidelity inspection.

Mathematical preservation includes the fixed T=0 box p=(2,3,5,7), b=(4,2,1,1); every finite real two-actual-corner slab and strict cutoff; both normalized bounds; orthogonality versus encoding; positive support; all saturation, tie, zero and equality cases; the full fractional optimizer; all 71 guards and 16 retained/55 inactive classification; both noninteger reflected endpoints; all density and D/Psi/G enclosures; the unique global maximizing slab and strict -1/1250 bound; and the explicitly corrected logarithm series with its proof. No mathematics, historical certificate or test was executed in this migration. The existing outward-rounding mathematical methods in 32.18 are retained as definitions, and the raw erroneous token remains explicitly identified alongside the pre-existing correction.

One exact local dependency remains in 32.18: the original primary self-reported joint L,H enclosure [3571708000370,5592595433915]/10^12. The historical report explicitly says the original full executable was unavailable and the adapted certificate checked only the broader 0<L,H<16. That exact original sentence remains contiguous and explicitly pending in the active entry, with its historical status unchanged. No new proof, assumption substitution or theorem promotion is made. Consequently this is an independent migration candidate with that named local dependency, not a claim of a completely pure S21 tail. The existing density and D/Psi/G enclosures have their separate original Arb evidence and remain theorem content with attached evidence citations. The pending tight support enclosure is not used as a new premise of the all-real-slab sign proof.

Only necessary mathematical type/proof/citation grammar is added. Original PAPER_ARGUMENT/repo-derived status, novelty limits, retrieval failures, missing model/conversation evidence, original computations, initial coverage failure, repairs, ingestion and delivery statuses remain archival facts. The original report's own earlier C48/C69 records and historical variants are not relabelled as current executions. Current ingestion and canonical bindings are recorded in the paired migration JSON and worker result after the sole authorized producer run.

### Inactive original source fragments

Original 32.1, source bytes [316815,316824), SHA256 3c54ab02e005fe059dbe1b09e7abe39f370b784a3ef3f58d68307c9a4eb62c9f; operational heading qualifier.

~~~~text
与状态
~~~~

Original 32.1, source bytes [316830,316895), SHA256 215bf7a53e7e452d282c3249d14a99f5e75f932a64bf0eacfb0864b6414c1ffc; stage and evidentiary classification retained in archive.

~~~~text
本节为 S21/C46 的 PAPER_ARGUMENT / repo-derived
参考输入:
~~~~

Original 32.5, source bytes [322224,322276), SHA256 29c6ea789d4dea75064c21678e2ce73ec9d4adb499a81ab4a1e56542239d65d5; execution-only clause after support proof.

~~~~text
;有限程序的支撑检查只是固定输入链接
~~~~

Original 32.7, source bytes [323022,323079), SHA256 56be466069541617d747bb7102731ce4c954d76bb98bba6fdaa1c4613f645601; historical attribution of four density enclosures.

~~~~text
原 primary 给出、原 caller Arb 审计独立确认的
~~~~

Original 32.8, source bytes [325165,325167), SHA256 beadba836315747fc95ae304452514b72fe122a6e345974638d70c4e8ebace6a; comma/LF replaced by sentence-ending grammar after archiving execution clause.

~~~~text
,
~~~~

Original 32.8, source bytes [325167,325235), SHA256 f50a595c8af6aeb12468f02c9f1ff06404d37c1b87c0e5b1d2e1a4d052f656c0; execution interpretation.

~~~~text
数值程序中的 primal/dual 区间交叠仅作一致性检查。
~~~~

Original 32.13, source bytes [329076,329103), SHA256 f25b70bed73dd9c4e11b4891c180d3543225b2fa73ed20985c102213742690e9; operational ID namespace comparison.

~~~~text
,不是三素数 GPU 行号
~~~~

Original 32.13, source bytes [330161,330242), SHA256 1c508697b4aa8a091d6dc788c31041d95e87c3b3caf69023858168f0d7e6b8e7; execution-count interpretation; inactive class and all guards retained.

~~~~text
不活跃槽只作资格核验,
没有被记作 55 个已计算负值的薄层。
~~~~

Original 32.15, source bytes [331569,331719), SHA256 2ba5d6712045778caa8ce949c511399e0afec57570082e1ce96b225e2f9e9a2e; historical numerical provenance and execution.

~~~~text
它是原 primary 表及原 caller Arb 审计的共同精确端点数据;
本轮报告的自足改编证书对自己的静态副本另执行一次。
~~~~

Original 32.16, source bytes [334464,334528), SHA256 9cabcc5ebf26d336982d08a6954297a317de9ff5f7fb4371d81b4ff69fb4bea8; historical verification of retained integer inequalities.

~~~~text
这些是报告改编证书额外核验的固定整数链接。
~~~~

Original 32.18, source bytes [336190,336202), SHA256 85f56448487a6ee4cb23e08550be74223321ada16e0b8c556a7cbb3fad32ad1b; primary attribution in the 32.18 heading.

~~~~text
原 primary 
~~~~

Original 32.18, source bytes [336223,336242), SHA256 536f2d4c8b05a69f8ac095c6198cf9a6c1887a4f9e08f0045d9381dc0b5e5fb9; historical-preservation heading qualifier.

~~~~text
,不改历史原文
~~~~

Original 32.18, source bytes [336248,336267), SHA256 c73b440d21805f57aadb2f9e3dc7266263d00f22e548deeb0eccdefe3d64d038; source provenance preceding raw erroneous notation.

~~~~text
原 conclusion 的
~~~~

Original 32.18, source bytes [336659,336687), SHA256 3e0f39a31297cc376cbfb63b599ab56566f7791223d5aa005d69241a88cfe938; historical attribution of enclosure method.

~~~~text
原 primary 自报的方法
~~~~

Original 32.18, source bytes [337231,337545), SHA256 b21eae71b328c1ea92a3e32f15d792a28dddd29158a1893973e9e8087ba71a94; historical execution and immutable-artifact provenance.

~~~~text
本实施不重跑或补造那份临时级数程序,也不把该自报执行当作本轮亲跑。
原 envelope/程序/审计全部保持字节不变;纠正只在新增文字中明示。
原 caller 与本轮改编使用的是独立的 outward Arb 运算,
不使用这个 raw 余项表达式来证明数值符号。
~~~~

Original 32.19, source bytes [337546,339214), SHA256 4b4515e76802e91f956ec04e63de2785119548fe214b27da72bcc064c5cc476d; wholly operational entry; permanent reservation.

~~~~text
**32.19 证据分工、复现与历史限制。** caller 指定的实际 GPT PRO fixed-box primary
task 为 0838ec9d-f978-4cfc-8d59-965a3331f912,flight
qgh0910-pro-actual-5040-box。仅消费其已完成 conclusion;
primary 明报获取所供 immutable GitHub URL 失败为 DisabledError,
没有读取该源字节或独立核验 caller 给出的源 hash/字节数。
它从所给定义自行重导有限归约,临时整数/Fraction 级数程序的执行是其自报。
模型/service 元数据并未由 primary 或本实施独立鉴定,不补造 conversation 身份。
I16 则在本树实际阅读第 26 节,核对其 \(k\ge2\)、互异素数、\(b_i\in\mathbb Z_{\ge0}\)
及原始严格 cutoff 等全部适用条件;没有读取 S20 的其它物理工作树。

原 caller node audit 只核验这个箱体的 71 槽资格,没有 \(G\) 值计算。
原 caller sign audit 记录 python-flint 0.8.0 / Arb256 对四个密度区间和
48 个 \(D,\Psi,G\) 区间的独立确认,并另述纸面连续域核对;
这些是原先完成的证据,原程序未在本轮执行。
单一报告 [actual-5040-fixed-box-0910.md](../../reports/quantized-gh/actual-5040-fixed-box-0910.md)
嵌入一份无 caller 绝对路径依赖的完整可执行证书,静态带入角点、整数 guards、
四个密度区间和 48 个节点区间。只抽取并执行该改编一次,
精确程序字节/hash、实际解释器/库版本、命令、结果和 stderr 见报告。
新增固定分支整数链接与原 52 个包络检查分列;它们不是候选生成或连续域的计算穷举。
Arb 的有理输入和区间比较承担向外认证,打印小数与区间交叠不承担等式证明。

~~~~

Original 32.20, source bytes [339214,339397), SHA256 2ef3a45588358c685e1401e3ccd40408511ab7df5b75bae11e337b40f619375b; citation access/provenance or reserved heading.

~~~~text
**32.20 文献重叠与仓内归属。** 本层专门化的证明组合标为 repo-derived,
不声称经典工具或这个 fixed-box 陈述具有新颖性或优先权。
现场读取 
~~~~

Original 32.20, source bytes [339575,339637), SHA256 8d0a5aac33f0a5c79822b0a0f12e5f28dfe1cfa792256399245e19f695164586; citation access/provenance or reserved heading.

~~~~text

文本提取的一些数学字体乱码保留为访问限制,
~~~~

Original 32.20, source bytes [339676,339684), SHA256 ae4892ce1e5e339972064cfcfe666fb38e9b67987ec09d84535d11351a50c4c4; citation access/provenance or reserved heading.

~~~~text

读取 
~~~~

Original 32.20, source bytes [340016,340017), SHA256 01ba4719c80b6fe911b091a7c05124b64eeece964e09c058ef8f9805daca546b; citation access/provenance or reserved heading.

~~~~text

~~~~

Original 32.20, source bytes [340146,340634), SHA256 d123b00702c018b5a9a82dcdbfee3b329073960ea662406e53f52cfb132f687e; citation access/provenance or reserved heading.

~~~~text

python-flint [arb 文档](https://python-flint.readthedocs.io/en/latest/arb.html)
成功读取的是显示为 0.9.0 的 latest 页面,介绍球区间及 \(\mathrm{ctx.prec}\);
指定 0.8.0 文档 URL 的实际请求返回 HTTP 403,不宣称读取了它。
实际证书库钉版与版本来自程序自己的运行记录,不由 latest 文档替代。
所有 URL 的访问时刻、字节/hash 和支持范围在报告列明,不把有限检索称为穷尽调查。

仓内直接复用的是
~~~~

Original 32.20, source bytes [340718,340719), SHA256 01ba4719c80b6fe911b091a7c05124b64eeece964e09c058ef8f9805daca546b; citation access/provenance or reserved heading.

~~~~text

~~~~

Original 32.20, source bytes [340861,340894), SHA256 e07b2d65b3ea7ce9556d3090e020a6ea6cb4910e7aba3ad579243d882f0491f6; citation access/provenance or reserved heading.

~~~~text
本层没有重做这些计算或
~~~~

Original 32.20, source bytes [340926,340927), SHA256 01ba4719c80b6fe911b091a7c05124b64eeece964e09c058ef8f9805daca546b; citation access/provenance or reserved heading.

~~~~text

~~~~

Original 32.20, source bytes [341042,341149), SHA256 b8ff86a938f8e0173aa7444a7cfd14ec162a09ba31255c55df8c787a1ac1218f; citation access/provenance or reserved heading.

~~~~text

这些重叠是既有参考输入的归属,不是本节的新发现,也不是 Lean 冻结状态声明。

~~~~

Original 32.21, source bytes [341149,342864), SHA256 79319e9af85f610fa2be4d0f66cfca8f2f3588d433a049e5a5413c9def811874; implementation/ingestion/delivery entry prefix.

~~~~text
**32.21 单层摄入与交付边界。** 本层由 caller 指定的隔离 Codex CLI I16
在 consensus-rnd:sshx 1.0.0-beta.42 及其 CODEX_WORKER_SPEC.md 下实施,
flight qgh0910-i16-actual-5040-fixed,attempt 1;repo-prior-exposed。
遵守 CLAUDE 5.11 与本次 brief,无委派、native subagent、额外 worker/oracle 或本轮 review 票;
不声称 sterile priors 或模型族多样性。工作树为
/Users/auricstudio/trureturing-qgh-actual-5040-fixed,
分支 lane/math/quantized-gh-actual-5040-fixed-0910,
immutable BASE 为 fe3f12abe8bc2e14628a93990fee2755c30da2bd。
完整前缀保留 316724 字节、5974 个 LF,SHA256
9229e2affc81243efcdcbd228058d8ca19cea395630a94ae943afde374157dd2。
唯一源改动为追加本节,另加一个报告,canonical 输出仅来自一次
~~~sh
make ingest BASE=fe3f12abe8bc2e14628a93990fee2755c30da2bd SOURCE=arithmetic-boundary-quantization
~~~
全部历史 CAS、entry、报告和输入保留,自动 children、历史 terminal-LF 变体
及每个 producer EOF 字节均原样保留。编号内容单元作完整跨度和有序 chain 拼接核对,
结构标题不要求成为 atom;fingerprint/cas_ref 带 sha256: 前缀,child atom_id 为裸 hash。
源/报告/前后缀身份、完整改动清单与实际 canonical 绑定见实施结论及报告。
该源、证书及其摄入绑定是同一个内容层,不拆出脱离源语义的地址产物。

CPU 只作固定数学核验及必要编排;没有指数/高度/薄层 sweep、候选生成、旧搜索重放、
GPU、daemon、广泛 build/preflight、工具/metadata/Lean/frozen 修复或手工 canonical 规范化。
没有读取 worker 日志、log_ref 内容、caller 转录、同轮 peer 信封或其它 live target。
~~~~

Original 32.21, source bytes [342957,342972), SHA256 9d7a0003380d894849e407fbad57180613c49af715c950b6c0d86071f5bca958; formal-status qualifier.

~~~~text
或 Lean freeze
~~~~

Original 32.21, source bytes [343059,343071), SHA256 77c62ff815f53e335caf29f1cbac5079f8091563654c0b0d6c570fc6c71c50bf; research-flight status qualifier.

~~~~text
未返回的
~~~~

Original 32.21, source bytes [343185,343505), SHA256 54b004a17081e67877ca9f2947b93100123e0ac0221de29023eec6d49751a3c2; delivery and goal-status suffix.

~~~~text
全部改动返回 unstaged;不作 stage/commit/push/PR/merge 或生命周期动作。
caller 负责后续封存、公共字节核对、独立评审、普通仓库门与交付;
最终 S21 交付必须等待 S20 MERGED。本次实施不作 termination 判词,
不把有限层的实现或摄入标成持续目标完成。
~~~~

## C99 / I35 support-proof adoption

This appendix records a new, scoped implementation at BASE 2dcd259aa895ad0030875378e2748da57ee563f8. The entire preceding report remains historical evidence. The mathematical authority is [source 32.22–32.24](../../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md); the sole authoritative recovery and current canonical binding map is [support-proof-adoption-s21-0910.json](support-proof-adoption-s21-0910.json). The old I32 map is immutable and describes its own earlier representation.

The original tight support interval is CERTIFIED for all sixteen prescribed nodes, with no refuted or inconclusive comparison. The paper bound 0 < L <= H < 14 < 16 is proved independently of this numerical evidence. The original pending clause is retired by proof, not by weakening its numbers. The raw result's preregistered field name `corrected_joint_grid` denotes a stronger enclosed interval here; it does not report a correction or a failure. The original density, D/Psi/G tables, all-real-slab theorem, strict domain and equality cases retain their existing evidence and status. No historical mathematical program was replayed.

The current supplied CLAUDE authority (blob 3138b10dfc55b2e0c570da8079821518f36196eb) controls this layer. Compared with the older local file, its 2.10 adds concise, nonduplicated evidence requirements, and 3.8 requires mathematical-only active theory with fresh numbered corrections. Other observed differences are in 5.5, 7.4, 7.7, 7.14, 8.12, 8.14, 8.15 and 9.5 (integration/workflow authority; 8.12 includes the current 8-feature/16-refactor stability counts). The local authority file was not overwritten. Current 5.11 and the cumulative goal retain unlimited goal iterations; this worker obeys the explicit no-delegation, no-Git, single-verifier and single-ingest scope. The pinned sshx skill/spec govern the return envelope, not a new primary or independent review. CLI 0.154.0 capability is caller-observed; this implementation makes no new actual-PRO or hidden-model attestation.

The inherited 316725-byte mixed source prefix remains unchanged. Addresses 32.19 and 32.20 remain permanently unavailable. Exact pure predecessor composition, full-source mathematical/representation review, ordinary gates and predecessor-ordered S21 delivery remain caller obligations. This tail repair is not whole-source purity, review approval, MERGED, RH progress or completion of the standing research goal. All other cumulative mathematical obligations and historical failures remain in force.

### Inactive original pending passage

The following is INACTIVE archival evidence, including its original pending label, primary self-report and evidence-link grammar. Embedded paths and commands are inert. The authoritative map supplies the exact byte recovery spans, including the original 121-byte sentence.

~~~~text
**待证子句（保留原记载）。**
primary 自报所有节点的 \(L,H\) 位于
\([3571708000370,5592595433915]/10^{12}\),以保证其指数级数范围。

**证明依赖。** [原包络记载及证据限制](../../reports/quantized-gh/actual-5040-fixed-box-0910.md#original-inputs-and-execution-attribution)。


~~~~

<a id="i35-fixed-support-certificate"></a>
### Fixed support certificate

This is the single new mathematical execution authorized by C99. Before execution, the complete script, sixteen-node scope, 256-bit Arb precision and 10^-18 outward reporting grid were fixed. All input numbers are integers or exact rationals. Algebraic interval operations use exact Fraction endpoints; only logarithms and square roots use Arb. No float conversion, sample-height inference, guard classification, D/Psi/G/density evaluation, search, precision sweep, installation or second execution occurred. The analytical soundness argument is in source 32.23.

The environment was found by fresh PATH/cache discovery, not by following an archived report command. System Python 3.9.6 and PATH Python 3.12.13 had no flint module; the already installed environment below supplied CPython 3.13.12, python-flint 0.9.0 and FLINT 3.6.0. Read-only method documentation confirmed that `lower()`/`upper()` round outward and return exact finite binary endpoints, and `man_exp()` extracts their exact integer representation. API inspection and syntax compilation did not execute the mathematical body.

Execution record (the script identity was sealed before the sole invocation; exit 0 means all requested comparisons were decided and the coarse checks passed):

~~~~json
{
  "registered_utc": "2026-09-10T16:18:53.861214+00:00",
  "script": {
    "path": "/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qgh0910-i35-s21-support-proof/attempt-1/fixed_support_256.py",
    "bytes": 4796,
    "sha256": "429d101215267bff3519d9166eda3d58531a9b28cc65ea87c2c817652c025ba9"
  },
  "precision_bits": 256,
  "output_grid_denominator": 1000000000000000000,
  "syntax_only_passed": true,
  "argv": [
    "/Users/auricstudio/.cache/uv/archive-v0/LrAPww9gQrptI5dhPuGZq/bin/python",
    "/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qgh0910-i35-s21-support-proof/attempt-1/fixed_support_256.py"
  ],
  "execution_count": 1,
  "started_utc": "2026-09-10T16:19:13.781035+00:00",
  "ended_utc": "2026-09-10T16:19:14.144746+00:00",
  "exit": 0,
  "stdout_bytes": 17518,
  "stdout_sha256": "b975c26c9b4cf498554432ddcc2de5be91390d5afe088365dcb909a20872dbd2",
  "stderr": ""
}
~~~~

Exact standalone script (UTF-8; final LF included):

~~~~python
"""I35: one fixed 16-node support verification; no search or sign evaluation.

Arb transcendental precision is 256 bits throughout. Interval endpoints and
all algebraic interval operations use exact Fraction arithmetic. The reporting
grid is fixed at 10^-18 before execution and is never used as an input.
"""
import json
import sys
from fractions import Fraction as Q
import flint
from flint import arb, fmpq, ctx

PRECISION = 256
GRID = 10**18
Q_LIST = (1, 2, 3, 5, 6, 7, 10, 14, 15, 21, 30, 35, 42, 70, 105, 210)
NODES = tuple((r, Q(1058400 * Q_LIST[r]), Q(1058400 * Q_LIST[r+1]))
              for r in range(1, 15)) + (
    (23, Q(3175200), Q(17592186044416, 3175200)),
    (37, Q(7408800), Q(95367431640625, 7408800)),
)
TIGHT = (Q(3571708000370, 10**12), Q(5592595433915, 10**12))


def dyadic(x):
    m, e = x.man_exp()
    m, e = int(m), int(e)
    return Q(m * 2**e) if e >= 0 else Q(m, 2**(-e))


def endpoints(x):
    if not x.is_finite():
        raise ArithmeticError("nonfinite Arb enclosure")
    return dyadic(x.lower()), dyadic(x.upper())


def ball(q):
    return arb(fmpq(q.numerator, q.denominator))


def log_interval(q):
    assert q > 0
    return endpoints(ball(q).log())


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def scale(a, q):
    assert q >= 0
    return a[0] * q, a[1] * q


def maximum(*args):
    return max(a[0] for a in args), max(a[1] for a in args)


def minimum(*args):
    return min(a[0] for a in args), min(a[1] for a in args)


def square_nonnegative(a):
    assert 0 <= a[0] <= a[1]
    return a[0]**2, a[1]**2


def sqrt_nonnegative(a):
    assert 0 <= a[0] <= a[1]
    lo = endpoints(ball(a[0]).sqrt())[0]
    hi = endpoints(ball(a[1]).sqrt())[1]
    return max(Q(0), lo), hi


def grid(a):
    lo, hi = (x * GRID for x in a)
    return [lo.numerator // lo.denominator,
            -((-hi.numerator) // hi.denominator)]


def ge(a, q):
    return "proved" if a[0] >= q else "refuted" if a[1] < q else "inconclusive"


def le(a, q):
    return "proved" if a[1] <= q else "refuted" if a[0] > q else "inconclusive"


def main():
    ctx.prec = PRECISION
    c = [log_interval(Q(n)) for n in (32, 27, 25, 49)]
    d = [log_interval(Q(n)) for n in (64, 81, 125, 343)]
    rows = []
    zero = (Q(0), Q(0))
    for slot, e0, e1 in NODES:
        v, w = scale(log_interval(e0), Q(1, 4)), scale(log_interval(e1), Q(1, 4))
        delta = [minimum(maximum(sub(ci, w), sub(v, ci), zero),
                         maximum(sub(di, w), sub(v, di), zero))
                 for ci, di in zip(c, d)]
        V0 = zero
        for a in delta:
            V0 = add(V0, square_nonnegative(a))
        rho = sqrt_nonnegative(scale(V0, Q(1, 12)))
        L, H = sub(w, rho), add(w, scale(rho, Q(3)))
        comparisons = {"L_ge_tight_lower": ge(L, TIGHT[0]),
                       "L_le_tight_upper": le(L, TIGHT[1]),
                       "H_ge_tight_lower": ge(H, TIGHT[0]),
                       "H_le_tight_upper": le(H, TIGHT[1])}
        rows.append({"slot": slot, "exp_M0": [e0.numerator, e0.denominator],
                     "exp_M1": [e1.numerator, e1.denominator],
                     "delta_grid": [grid(a) for a in delta], "V0_grid": grid(V0),
                     "rho_grid": grid(rho), "L_grid": grid(L), "H_grid": grid(H),
                     "tight_comparisons": comparisons,
                     "coarse_0_lt_L_le_H_lt_14_lt_16":
                         L[0] > 0 and rho[0] >= 0 and H[1] < 14 < 16})
    verdicts = [v for row in rows for v in row["tight_comparisons"].values()]
    status = "contradicted" if "refuted" in verdicts else (
        "inconclusive" if "inconclusive" in verdicts else "certified")
    result = {"schema": "fixed5040-support-256-v1", "precision_bits": ctx.prec,
              "interpreter": sys.executable, "python_version": sys.version,
              "python_flint_version": flint.__version__,
              "flint_version": flint.__FLINT_VERSION__,
              "grid_denominator": GRID, "node_count": len(rows),
              "original_tight_numerators": [3571708000370, 5592595433915],
              "original_tight_denominator": 10**12,
              "original_tight_status": status,
              "inconclusive_comparisons": verdicts.count("inconclusive"),
              "corrected_joint_grid": [min(row["L_grid"][0] for row in rows),
                                       max(row["H_grid"][1] for row in rows)],
              "coarse_all_certified": all(row["coarse_0_lt_L_le_H_lt_14_lt_16"] for row in rows),
              "rows": rows}
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result["coarse_all_certified"] and not result["inconclusive_comparisons"] else 2


if __name__ == "__main__":
    sys.exit(main())
~~~~

Actual stdout, verbatim (the stderr was empty):

~~~~json
{
  "schema": "fixed5040-support-256-v1",
  "precision_bits": 256,
  "interpreter": "/Users/auricstudio/.cache/uv/archive-v0/LrAPww9gQrptI5dhPuGZq/bin/python",
  "python_version": "3.13.12 (main, Mar 10 2026, 18:26:32) [Clang 21.1.4 ]",
  "python_flint_version": "0.9.0",
  "flint_version": "3.6.0",
  "grid_denominator": 1000000000000000000,
  "node_count": 16,
  "original_tight_numerators": [
    3571708000370,
    5592595433915
  ],
  "original_tight_denominator": 1000000000000,
  "original_tight_status": "certified",
  "inconclusive_comparisons": 0,
  "corrected_joint_grid": [
    3571708000370205849,
    5592595433914645222
  ],
  "coarse_all_certified": true,
  "rows": [
    {
      "slot": 1,
      "exp_M0": [
        2116800,
        1
      ],
      "exp_M1": [
        3175200,
        1
      ],
      "delta_grid": [
        [
          175618115285980525,
          175618115285980526
        ],
        [
          345517152081377998,
          345517152081377999
        ],
        [
          422478193217506323,
          422478193217506324
        ],
        [
          149100002997878442,
          149100002997878443
        ]
      ],
      "V0_grid": [
        350942459437322005,
        350942459437322006
      ],
      "rho_grid": [
        171012294742542318,
        171012294742542319
      ],
      "L_grid": [
        3571708000370205849,
        3571708000370205850
      ],
      "H_grid": [
        4255757179340375123,
        4255757179340375124
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 2,
      "exp_M0": [
        3175200,
        1
      ],
      "exp_M1": [
        5292000,
        1
      ],
      "delta_grid": [
        [
          276984392313021620,
          276984392313021621
        ],
        [
          446883429108419093,
          446883429108419094
        ],
        [
          523844470244547418,
          523844470244547419
        ],
        [
          21393597056380771,
          21393597056380772
        ]
      ],
      "V0_grid": [
        551295867797514614,
        551295867797514615
      ],
      "rho_grid": [
        214339269188964883,
        214339269188964884
      ],
      "L_grid": [
        3656087431865280954,
        3656087431865280955
      ],
      "H_grid": [
        4513444508621140490,
        4513444508621140491
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 3,
      "exp_M0": [
        5292000,
        1
      ],
      "exp_M1": [
        6350400,
        1
      ],
      "delta_grid": [
        [
          242875993106937361,
          242875993106937362
        ],
        [
          478442064419704270,
          478442064419704271
        ],
        [
          651550876186045089,
          651550876186045090
        ],
        [
          0,
          0
        ]
      ],
      "V0_grid": [
        712414101292672593,
        712414101292672594
      ],
      "rho_grid": [
        243655169808459805,
        243655169808459806
      ],
      "L_grid": [
        3672351920444274689,
        3672351920444274690
      ],
      "H_grid": [
        4646972599678113912,
        4646972599678113913
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 4,
      "exp_M0": [
        6350400,
        1
      ],
      "exp_M1": [
        7408800,
        1
      ],
      "delta_grid": [
        [
          204338323150122785,
          204338323150122786
        ],
        [
          439904394462889694,
          439904394462889695
        ],
        [
          697131265384533746,
          697131265384533747
        ],
        [
          24186792142107885,
          24186792142107886
        ]
      ],
      "V0_grid": [
        721847028666332412,
        721847028666332413
      ],
      "rho_grid": [
        245262958996110338,
        245262958996110339
      ],
      "L_grid": [
        3709281801213438733,
        3709281801213438734
      ],
      "H_grid": [
        4690333637197880086,
        4690333637197880087
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 5,
      "exp_M0": [
        7408800,
        1
      ],
      "exp_M1": [
        10584000,
        1
      ],
      "delta_grid": [
        [
          115169587165439690,
          115169587165439691
        ],
        [
          350735658478206599,
          350735658478206600
        ],
        [
          735668935341348322,
          735668935341348323
        ],
        [
          62724462098922461,
          62724462098922462
        ]
      ],
      "V0_grid": [
        681422676507871086,
        681422676507871087
      ],
      "rho_grid": [
        238296502371148096,
        238296502371148097
      ],
      "L_grid": [
        3805416993823084069,
        3805416993823084070
      ],
      "H_grid": [
        4758603003307676456,
        4758603003307676457
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 6,
      "exp_M0": [
        10584000,
        1
      ],
      "exp_M1": [
        14817600,
        1
      ],
      "delta_grid": [
        [
          31051528010136457,
          31051528010136458
        ],
        [
          266617599322903366,
          266617599322903367
        ],
        [
          700482181952765725,
          700482181952765726
        ],
        [
          151893198083605555,
          151893198083605556
        ]
      ],
      "V0_grid": [
        585795972517845553,
        585795972517845554
      ],
      "rho_grid": [
        220944180831163317,
        220944180831163318
      ],
      "L_grid": [
        3906887374518372080,
        3906887374518372081
      ],
      "H_grid": [
        4790664097843025352,
        4790664097843025353
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 7,
      "exp_M0": [
        14817600,
        1
      ],
      "exp_M1": [
        15876000,
        1
      ],
      "delta_grid": [
        [
          13803310138398594,
          13803310138398595
        ],
        [
          249369381451165503,
          249369381451165504
        ],
        [
          683233964081027862,
          683233964081027863
        ],
        [
          236011257238908788,
          236011257238908789
        ]
      ],
      "V0_grid": [
        584885582993479350,
        584885582993479351
      ],
      "rho_grid": [
        220772428644195995,
        220772428644195996
      ],
      "L_grid": [
        3924307344577077266,
        3924307344577077267
      ],
      "H_grid": [
        4807397059153861248,
        4807397059153861249
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 8,
      "exp_M0": [
        15876000,
        1
      ],
      "exp_M1": [
        22226400,
        1
      ],
      "delta_grid": [
        [
          0,
          0
        ],
        [
          165251322295862271,
          165251322295862272
        ],
        [
          599115904925724629,
          599115904925724630
        ],
        [
          253259475110646651,
          253259475110646652
        ]
      ],
      "V0_grid": [
        450388228788821111,
        450388228788821112
      ],
      "rho_grid": [
        193732682836604588,
        193732682836604589
      ],
      "L_grid": [
        4035465149539971906,
        4035465149539971907
      ],
      "H_grid": [
        4810395880886390258,
        4810395880886390259
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 9,
      "exp_M0": [
        22226400,
        1
      ],
      "exp_M1": [
        31752000,
        1
      ],
      "delta_grid": [
        [
          70314749016904637,
          70314749016904638
        ],
        [
          76082586311179176,
          76082586311179177
        ],
        [
          509947168941041534,
          509947168941041535
        ],
        [
          337377534265949884,
          337377534265949885
        ]
      ],
      "V0_grid": [
        384602439607463665,
        384602439607463666
      ],
      "rho_grid": [
        179025705697874494,
        179025705697874495
      ],
      "L_grid": [
        4139340862663385094,
        4139340862663385095
      ],
      "H_grid": [
        4855443685454883071,
        4855443685454883072
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 10,
      "exp_M0": [
        31752000,
        1
      ],
      "exp_M1": [
        37044000,
        1
      ],
      "delta_grid": [
        [
          159483485001587732,
          159483485001587733
        ],
        [
          37544916354364600,
          37544916354364601
        ],
        [
          471409498984226958,
          471409498984226959
        ],
        [
          426546270250632978,
          426546270250632979
        ]
      ],
      "V0_grid": [
        431013239129593796,
        431013239129593797
      ],
      "rho_grid": [
        189519840458634171,
        189519840458634172
      ],
      "L_grid": [
        4167384397859439993,
        4167384397859439994
      ],
      "H_grid": [
        4925463759693976678,
        4925463759693976679
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 11,
      "exp_M0": [
        37044000,
        1
      ],
      "exp_M1": [
        44452800,
        1
      ],
      "delta_grid": [
        [
          198021154958402308,
          198021154958402309
        ],
        [
          0,
          0
        ],
        [
          425829109785738302,
          425829109785738303
        ],
        [
          465083940207447554,
          465083940207447555
        ]
      ],
      "V0_grid": [
        436845879990858595,
        436845879990858596
      ],
      "rho_grid": [
        190797859874191328,
        190797859874191329
      ],
      "L_grid": [
        4211686767642371492,
        4211686767642371493
      ],
      "H_grid": [
        4974878207139136808,
        4974878207139136809
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 12,
      "exp_M0": [
        44452800,
        1
      ],
      "exp_M1": [
        74088000,
        1
      ],
      "delta_grid": [
        [
          243601544156890965,
          243601544156890966
        ],
        [
          8035472844124056,
          8035472844124057
        ],
        [
          298122703844240631,
          298122703844240632
        ],
        [
          510664329405936211,
          510664329405936212
        ]
      ],
      "V0_grid": [
        409061485014465688,
        409061485014465689
      ],
      "rho_grid": [
        184630596284957080,
        184630596284957081
      ],
      "L_grid": [
        4345560437173103411,
        4345560437173103412
      ],
      "H_grid": [
        5084082822312931734,
        5084082822312931735
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 13,
      "exp_M0": [
        74088000,
        1
      ],
      "exp_M1": [
        111132000,
        1
      ],
      "delta_grid": [
        [
          371307950098388635,
          371307950098388636
        ],
        [
          135741878785621726,
          135741878785621727
        ],
        [
          196756426817199535,
          196756426817199536
        ],
        [
          638370735347433882,
          638370735347433883
        ]
      ],
      "V0_grid": [
        602525738704413354,
        602525738704413355
      ],
      "rho_grid": [
        224076947108281934,
        224076947108281935
      ],
      "L_grid": [
        4407480363376819653,
        4407480363376819654
      ],
      "H_grid": [
        5303788151809947391,
        5303788151809947392
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 14,
      "exp_M0": [
        111132000,
        1
      ],
      "exp_M1": [
        222264000,
        1
      ],
      "delta_grid": [
        [
          472674227125429731,
          472674227125429732
        ],
        [
          237108155812662822,
          237108155812662823
        ],
        [
          23469631677213208,
          23469631677213209
        ],
        [
          739737012374474977,
          739737012374474978
        ]
      ],
      "V0_grid": [
        827402873629282518,
        827402873629282519
      ],
      "rho_grid": [
        262583776096519101,
        262583776096519102
      ],
      "L_grid": [
        4542260329528568813,
        4542260329528568814
      ],
      "H_grid": [
        5592595433914645221,
        5592595433914645222
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 23,
      "exp_M0": [
        3175200,
        1
      ],
      "exp_M1": [
        549755813888,
        99225
      ],
      "delta_grid": [
        [
          276984392313021620,
          276984392313021621
        ],
        [
          446883429108419093,
          446883429108419094
        ],
        [
          523844470244547418,
          523844470244547419
        ],
        [
          9921607063976374,
          9921607063976375
        ]
      ],
      "V0_grid": [
        550936620089235776,
        550936620089235777
      ],
      "rho_grid": [
        214269421540816959,
        214269421540816960
      ],
      "L_grid": [
        3667629269505833276,
        3667629269505833277
      ],
      "H_grid": [
        4524706955669101113,
        4524706955669101114
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    },
    {
      "slot": 37,
      "exp_M0": [
        7408800,
        1
      ],
      "exp_M1": [
        3814697265625,
        296352
      ],
      "delta_grid": [
        [
          66238281398719054,
          66238281398719055
        ],
        [
          301804352711485964,
          301804352711485965
        ],
        [
          735668935341348322,
          735668935341348323
        ],
        [
          62724462098922461,
          62724462098922462
        ]
      ],
      "V0_grid": [
        640616517810127014,
        640616517810127015
      ],
      "rho_grid": [
        231051314251857447,
        231051314251857448
      ],
      "L_grid": [
        3861593487709095353,
        3861593487709095354
      ],
      "H_grid": [
        4785798744716525144,
        4785798744716525145
      ],
      "tight_comparisons": {
        "L_ge_tight_lower": "proved",
        "L_le_tight_upper": "proved",
        "H_ge_tight_lower": "proved",
        "H_le_tight_upper": "proved"
      },
      "coarse_0_lt_L_le_H_lt_14_lt_16": true
    }
  ]
}
~~~~

### Observed errors and limitations

Oversized intake displays were truncated (instruction/goal reads and later I32-map projections); the required text was recovered in bounded reads. The full structured I32 map was parsed, its semantic fields inspected, and every recovery/metadata/unit/CAS/YAML identity traversed against the assigned local files. Large historical inventories were not copied into this new appendix. A PATH discovery command, `command -v -a ...`, failed with exit 127 and `zsh:1: command not found: -v`; fresh `whence -a` discovery succeeded. A broad installed-package path display and runner search display were also truncated; the selected environment and completion predicate were then read directly. These were structural intake/discovery diagnostics, not mathematical executions. The single mathematical process exited 0 with empty stderr and no inconclusive comparisons. No blanket process-purity claim is made.

Historical I32 errors remain in its unchanged map/report, including the old discovery failure and verbatim archival whitespace diagnostics; they are not newly executed failures. Only bounded syntax/JSON/byte/canonical checks and the prescribed ingest are performed in this layer. There is no new test suite, broad build, GPU, candidate generation, historical certificate replay, Lean/frozen/tool/policy edit, independent review or Git lifecycle action.

### Sole ingest and complete-unit audit

The prescribed producer exited 0 and added 26 CAS/YAML pairs. A subsequent byte audit found a real representation defect: the unfenced table in 32.24 was split into one header atom and sixteen row atoms; each row omits its final pipe and LF. The proof after the table is outside those objects, and the full 32.24 parent is absent. The authoritative map records all 16 uncovered spans (1025 bytes) and all actual fragments. The other 21 complete units and their ordered chains are exact. This is an implementation/ingestion gap despite the successful producer exit, not a failed support proposition. The single-ingest and no-source-edit-after-ingest limits were retained; no source or producer byte was repaired afterward. A separately authorized representation repair and new layer are needed for complete-unit canonical coverage. Current tracked diff whitespace checking passes. Producer-only whitespace diagnostics are recorded verbatim in the map, including the preserved row-ending spaces and blank final lines; no normalization was applied.

Actual ingest receipt:

~~~~json
{
  "argv": [
    "make",
    "ingest",
    "BASE=2dcd259aa895ad0030875378e2748da57ee563f8",
    "SOURCE=arithmetic-boundary-quantization"
  ],
  "cwd": "/Users/auricstudio/trureturing-qgh-pure-s21",
  "invocation_count": 1,
  "new_layer": true,
  "source_sha256": "157686e0d16aeb73fe96616e28084c5c254d1c01dd8ebf136dba3dd00aecc986",
  "started_utc": "2026-09-10T16:24:17.094028+00:00",
  "ended_utc": "2026-09-10T16:24:46.194099+00:00",
  "exit": 0,
  "stdout": "INGEST residual_open_added=26 skipped_existing=292 coarse_fallbacks=0 open_genres=0 cas_objects_written=26 ledger_changed=true\n",
  "stderr": ""
}
~~~~
