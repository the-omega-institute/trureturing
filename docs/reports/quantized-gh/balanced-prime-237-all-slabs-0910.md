# Balanced (2,3,7): whole-box, all-real-slab fixed certificate (S20 / C43)

This report supports [section 31 of the source](../../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md#31-三素数-237-的九节点证书与整箱全薄层邻域), a repo-derived paper argument implemented by isolated CLI worker I15. For steps `(log 2, log 3, log 7)`, every finite `T >= log 2` and every closed real slab containing at least two distinct endpoint-corner budgets has `exp(T) G < -1/40` at equal shape. The closed neighborhood `min xi = 0`, `0 <= xi_i <= 1/320` has `exp(T) G < -1/80`. The comparison uses the standard Euclidean metric and `rho = sqrt(sum delta_i^2 / 6)`, with positive envelope arguments. This is a comparison of two upper bounds, not an RH criterion or a Lean/kernel-frozen theorem.

The corner multipliers are exactly `1, 2, 3, 6, 7, 14, 21, 42`. All eighteen integer reflected eligibility tests leave raw slots `10` and `24`; together with adjacent slots `0..6`, these give nine retained nodes. The change from `5 < 6` to `6 < 7` is proved in the integer table, not selected by floating diagnostics. Section 31 supplies the complete lower-budget saturation, convex-cell, endpoint/tie/zero-distance and upper-tail argument on the wider continuous domain. Its cumulative upper-mass/positive-part integral proof establishes every positive integer moment from the largest-two-mass and total-mass inequalities. Finite arithmetic certifies the nine inputs to that infinite argument; it does not itself verify an infinite quantifier.

The shape transfer compares the same feasible mixtures and uses projection plus distance Lipschitz bounds. Neither a stable nearest-endpoint branch nor a stable greedy permutation is assumed under perturbation. Homogeneous simultaneous approximation gives unbounded positive integers `q,m,n` with the spread of `(q log 2, m log 3, n log 7)` tending to zero. No exponent witness or sequence was computed. Original strict-domain slabs exist exactly when `A > log 2 + log 5040`; equality and smaller values give the empty domain. The actual product cannot equal `10080 = 2^5 * 3^2 * 5 * 7`, since a `(2,3,7)` product has no factor 5. This exclusion does not change the continuous-box threshold. The scaled bounds are strict at `T = log 2` and the closed shape boundary, while unscaled gaps approach zero along the stated continuous and actual families.

## Literal-domain and overlap audit

The locally read sealed source is the worktree's immutable predecessor, not the live S19 target. Section 30.2 fixes `(2,3,5)`, so its sections 30.3–30.7 and 30.9–30.19, including the finite reduction, transfer and actual lattice sequence, do not state the corresponding `(2,3,7)` theorem. Section 31 proves those arguments in the required new domain. Section 30.8 separately states the general mass-three measure lemma on `[0,1]`; its assumptions genuinely apply, and section 31.10 also writes the integral proof explicitly. Sections 26.2–26.16 carry actual-integer/strict-cutoff hypotheses, so their original-domain theorem is not silently applied to the wider continuous boxes. Section 27.3 explicitly extends the matched primal/price certificate to positive real grids. The positive-real-step mixture and series mechanisms in 29.2, 29.4–29.6 are reusable, but 29.3's cutoff-height domain and the `(2,3,5)` specializations in 29.13, 29.16 and 29.18 are not substituted for the new domain.

The reads covered section 30 in full and overlapping definitions/proofs in 26.2–26.16, 26.21, 26.23–26.24, 26.28, 27.2–27.3, 29.2–29.6, 29.13, 29.16–29.18 and the metric/KL distinctions of section 10. The source adds units 31.1–31.22. Later fixed-5040, translated-5040, density-order, C39 ray and search/program work are excluded. General primes and arbitrary shapes remain open; no priority, general inhomogeneous density, effective exponent cutoff, new orthogonality, RH progress or formalization claim is made.

## Self-contained adapted executable

The Python block below is the complete executable input. It reads no files, needs no caller-local paths or third-party package, and evaluates only prescribed constants/nodes using integers and `fractions.Fraction`. It makes no calls to floating `log`, `exp` or `sqrt`. The 80-term logarithm enclosures and positive degree-12 Taylor polynomials are fixed certificates, not height, exponent or moment searches.

The original caller audit and its program are unchanged and were not rerun. This adaptation preserves its 131 mathematical predicates and adds 21 fixed links: one verifies that the eight distinct binary corner vectors produce the strictly ordered products; two derive the reflected budgets from their raw slots; nine prove the exact greedy numerator lies between zero and its denominator; nine verify positive ordered Taylor inputs. In particular, an outward quotient interval may extend above 1 at an exact greedy endpoint. Its lower-bound arithmetic is still valid, but the old predicate `theta_lo <= 1` alone is not the needed exact-weight-domain proof. The added linear-log sign checks supply it.

<!-- fixed-certificate:begin -->
```python
"""Self-contained fixed certificate for section 31; no candidate generation.
Adapted from the unchanged caller 131-predicate audit. Only the prescribed
three log bounds, eighteen raw guards and nine theorem nodes are evaluated.
The all-height, all-moment and lattice quantifiers require the source proof.
"""
from fractions import Fraction as F
from math import factorial
import json
import re

certificate = {'log_enclosures': {'denominator': 1000000000000000,
                    'strict_bounds': [{'quantity': 'a=log2',
                                       'lower_numerator': 693147180559945,
                                       'upper_numerator': 693147180559946},
                                      {'quantity': 'b=log3',
                                       'lower_numerator': 1098612288668109,
                                       'upper_numerator': 1098612288668110},
                                      {'quantity': 'c=log7',
                                       'lower_numerator': 1945910149055313,
                                       'upper_numerator': 1945910149055314}]},
 'reflected_eligibility': {'rows': [[1, 1, 2, 3, 1, 2, 3, [7, 8, 9], [False, False, False]],
                                    [2, 2, 3, 6, 4, 6, 12, [10, 11, 12], [True, False, False]],
                                    [3, 3, 6, 7, 9, 18, 21, [13, 14, 15], [False, False, False]],
                                    [4, 6, 7, 14, 36, 42, 84, [16, 17, 18], [False, False, False]],
                                    [5,
                                     7,
                                     14,
                                     21,
                                     49,
                                     98,
                                     147,
                                     [19, 20, 21],
                                     [False, False, False]],
                                    [6,
                                     14,
                                     21,
                                     42,
                                     196,
                                     294,
                                     588,
                                     [22, 23, 24],
                                     [False, False, True]]]},
 'node_certificates': {'rows': [[0, '0', 'a', ['0', '0', '0'], 0, 0, 231, 231, 794, 794],
                                [1, 'a', 'b', ['a', 'a', 'a'], 4901, 4902, 202, 692, 818, 501],
                                [2,
                                 'b',
                                 'a+b',
                                 ['2a-b', 'b', 'b'],
                                 6450,
                                 6451,
                                 382,
                                 1027,
                                 683,
                                 359],
                                [3,
                                 'a+b',
                                 'c',
                                 ['3a-c', '3b-c', 'a+b'],
                                 9174,
                                 9175,
                                 342,
                                 1260,
                                 711,
                                 284],
                                [4,
                                 'c',
                                 'a+c',
                                 ['0', '3b-a-c', 'c'],
                                 8384,
                                 8385,
                                 600,
                                 1438,
                                 550,
                                 238],
                                [5,
                                 'a+c',
                                 'b+c',
                                 ['c-2a', '2b-c', 'a+c'],
                                 11061,
                                 11062,
                                 646,
                                 1752,
                                 526,
                                 174],
                                [6,
                                 'b+c',
                                 'a+b+c',
                                 ['b+c-3a', '0', '2c-a-b'],
                                 9435,
                                 9436,
                                 931,
                                 1874,
                                 395,
                                 154],
                                [10, 'a', '2a', ['a', 'a', 'a'], 4901, 4902, 298, 788, 743, 455],
                                [24,
                                 'a+c',
                                 '2c-a',
                                 ['c-2a', '3b-2c+a', 'a+c'],
                                 11020,
                                 11021,
                                 698,
                                 1800,
                                 498,
                                 166]]}}

checks = []


def check(name, predicate, extra=False):
    checks.append({'name': name, 'passed': bool(predicate),
                   'group': 'extra_fixed_link' if extra else 'inherited_predicate'})
    if not predicate:
        raise AssertionError(name)


log_bounds = []
denominator = certificate['log_enclosures']['denominator']
for p, row in zip((2,3,7), certificate['log_enclosures']['strict_bounds']):
    lo, hi = F(row['lower_numerator'],denominator), F(row['upper_numerator'],denominator)
    t = F(p-1,p+1)
    S = 2*sum((t**(2*j+1)/(2*j+1) for j in range(80)), F(0))
    U = S + 2*t**161/(161*(1-t*t))
    check(f'log {p}: exact 80-term strict enclosure', lo < S < U < hi)
    log_bounds.append((lo,hi))

zero, a, b, c = (0,0,0), (1,0,0), (0,1,0), (0,0,1)


def vector(expression):
    if expression == '0':
        return zero
    result = [0,0,0]
    tokens = list(re.finditer(r'([+-]?)([0-9]*)([abc])', expression))
    if ''.join(m.group(0) for m in tokens) != expression:
        raise ValueError(expression)
    for token in tokens:
        s, k, x = token.groups()
        result['abc'.index(x)] += (-1 if s == '-' else 1)*int(k or '1')
    return tuple(result)


def add(v,w): return tuple(x+y for x,y in zip(v,w))
def sub(v,w): return tuple(x-y for x,y in zip(v,w))
def mul(k,v): return tuple(k*x for x in v)


def interval(v):
    return (sum((x*(lo if x >= 0 else hi) for x,(lo,hi) in zip(v,log_bounds)), F(0)),
            sum((x*(hi if x >= 0 else lo) for x,(lo,hi) in zip(v,log_bounds)), F(0)))


def sign(v):
    if v == zero:
        return 0
    lo,hi = interval(v)
    if lo > 0: return 1
    if hi < 0: return -1
    raise AssertionError(('unresolved fixed linear-log branch',v,lo,hi))


corners = [zero,a,b,add(a,b),c,add(a,c),add(b,c),add(add(a,b),c)]
products = [1,2,3,6,7,14,21,42]
check('link: all eight corner coefficients, integer products and strict order',
      len(set(corners)) == 8 and
      all(all(k in (0,1) for k in v) for v in corners) and
      [2**v[0]*3**v[1]*7**v[2] for v in corners] == products and
      all(x < y for x,y in zip(products,products[1:])), extra=True)
retained = []
for row in certificate['reflected_eligibility']['rows']:
    j,P,Lp,Up,P2,LP,UP,slots,eligible = row
    check(f'reflected j={j}: exact tabulated products',
          [P,Lp,Up] == products[j-1:j+2] and [P2,LP,UP] == [P*P,Lp*P,Up*P])
    for i,p in enumerate((2,3,7)):
        found = P>1 and P*P<p**3 and Lp*P<p**3<Up*P
        slot = 7+3*(j-1)+i
        check(f'reflected slot {slot}: exact eligibility', slots[i]==slot and eligible[i]==found)
        if found: retained.append(slot)
check('complete reflected set is slots 10 and 24', retained == [10,24])

pairs = {i:pair for i,pair in enumerate(zip(corners,corners[1:]))}
pairs[10] = (a,mul(2,a))
pairs[24] = (add(a,c),sub(mul(2,c),a))
for slot in (10,24):
    j, i = (slot-7)//3+1, (slot-7)%3
    lower = corners[j-1]
    check(f'link: reflected slot {slot} equals its derived budget pair',
          pairs[slot] == (lower,sub(mul(3,(a,b,c)[i]),lower)), extra=True)
rows = certificate['node_certificates']['rows']
check('all nine prescribed nodes occur exactly once', [row[0] for row in rows] == [0,1,2,3,4,5,6,10,24])
margins = []
for row in rows:
    slot,u_text,v_text,q_text,Rlo,Rhi,alpha,beta,l,r = row
    u,v = vector(u_text),vector(v_text)
    q = tuple(vector(s) for s in q_text)
    check(f'node {slot}: exact budget pair and positive width', (u,v)==pairs[slot] and sign(sub(v,u))>0)
    derived_q = []
    for step in (a,b,c):
        endpoint = mul(3,step)
        if sign(sub(endpoint,u)) < 0:
            q_i = sub(u,endpoint)
        elif sign(sub(endpoint,v)) <= 0:
            q_i = zero
        else:
            other = sub(endpoint,v)
            q_i = u if sign(sub(u,other)) <= 0 else other
        derived_q.append(q_i)
    check(f'node {slot}: independent nearest-endpoint branches', tuple(derived_q)==q)
    q_intervals = [interval(q_i) for q_i in q]
    check(f'node {slot}: nonnegative distance coordinates', all(lo >= 0 for lo,hi in q_intervals))
    Rlo,Rhi = F(Rlo,10000),F(Rhi,10000)
    sq_lo = sum((lo*lo for lo,hi in q_intervals),F(0))/6
    sq_hi = sum((hi*hi for lo,hi in q_intervals),F(0))/6
    if slot==0:
        check('node 0: exact zero radius', Rlo==Rhi==sq_lo==sq_hi==0)
    else:
        check(f'node {slot}: outward squared radius enclosure', Rlo*Rlo < sq_lo <= sq_hi < Rhi*Rhi)
    alpha,beta,l,r = F(alpha,1000),F(beta,1000),F(l,1000),F(r,1000)
    check(f'link: node {slot} has positive ordered Taylor inputs',
          0 < alpha <= beta, extra=True)
    vlo,vhi = interval(v)
    check(f'node {slot}: strict lower offsets', (vlo-Rhi)/3 > alpha and (vlo+2*Rlo)/3 > beta)
    check(f'node {slot}: mass-three comparison atom domain', 0 < r <= l <= 1)
    for label,x,bound in [('lower',alpha,l),('upper',beta,r)]:
        polynomial = sum((x**k/factorial(k) for k in range(13)),F(0))
        check(f'node {slot}: {label} atom strict degree-12 certificate', bound*polynomial > 1)
    if sign(sub(v,add(a,b))) <= 0:
        numerator = interval(sub(v,a))
        theta_lo = numerator[0]/log_bounds[1][1]
        theta_hi = numerator[1]/log_bounds[1][0]
        Wlo = F(5,2)-F(2,3)*theta_hi
        Klo = 2-theta_hi/2
    else:
        numerator = interval(sub(v,add(a,b)))
        theta_lo = numerator[0]/log_bounds[2][1]
        theta_hi = numerator[1]/log_bounds[2][0]
        Wlo = F(11,6)-F(6,7)*theta_hi
        Klo = F(3,2)-F(2,3)*theta_hi
    n_vec,d_vec = ((sub(v,a),b) if sign(sub(v,add(a,b))) <= 0
                   else (sub(v,add(a,b)),c))
    check(f'link: node {slot} exact greedy fraction lies in the closed unit interval',
          sign(n_vec) >= 0 and sign(sub(d_vec,n_vec)) >= 0 and sign(d_vec) > 0,
          extra=True)
    # Preserve the original interval predicate; exact endpoint range is linked above.
    # theta_hi may exceed 1 by outward interval widening without harming a lower bound.
    check(f'node {slot}: greedy fractional range', theta_lo >= 0 and theta_lo <= 1 and theta_hi >= theta_lo)
    check(f'node {slot}: largest-two-mass strict dominance', Klo > 2*l)
    margin = Wlo-2*l-r
    check(f'node {slot}: uniform strict first-moment margin', margin > F(1,40))
    margins.append({'slot':slot,'rational_lower_bound':str(margin)})

check('nearby radius gives strict 1/80 scaled margin', -F(1,40)+4*F(1,320)==-F(1,80))
check('strict-cutoff integer threshold is 10080', 2*5040==10080)
check('actual 2,3,7 product cannot equal cutoff due to prime 5', 10080%5==0 and all(p%5!=0 for p in (2,3,7)))

result = {
    'certificate': 'balanced-prime-237-section31-v1',
    'adapted_fixed_checks': len(checks),
    'inherited_predicates': sum(row['group']=='inherited_predicate' for row in checks),
    'extra_fixed_links': sum(row['group']=='extra_fixed_link' for row in checks),
    'all_passed': all(row['passed'] for row in checks),
    'retained_adjacent_slots': list(range(7)),
    'retained_reflected_slots': retained,
    'first_moment_margin_lower_bounds': margins,
    'sampled_heights': 0,
    'moment_sweep': False,
    'CPU_candidate_search': False,
    'GPU_dispatches': 0,
    'independent_review': False,
}
print(json.dumps(result, sort_keys=True, separators=(',', ':')))
```
<!-- fixed-certificate:end -->

## Observed adapted execution

The embedded program was extracted byte-for-byte, including its final LF, and executed **once**. It is 12265 bytes / 271 LF, SHA256 `cd3f0d53cc0bbad4ceb0f1563d64021e059b0afe5c297fa69ed794d4efb24af0`. The actual program command was:

```sh
/Applications/Xcode.app/Contents/Developer/usr/bin/python3 /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qgh0910-i15-balanced-prime-237/attempt-1/balanced-prime-237-fixed-certificate.py
```

Working directory: `/Users/auricstudio/trureturing-qgh-balanced-prime-237`. Interpreter: Python 3.9.6, `3.9.6 (default, Jan 9 2026, 11:03:41) [Clang 17.0.0 (clang-1700.6.4.2)]`. Execution began `2026-09-09T20:56:59.977423+00:00` and finished `2026-09-09T20:57:00.007395+00:00`; exit code **0**, empty stderr. The emitted JSON result, reformatted without changing values, was:

```json
{
  "CPU_candidate_search": false,
  "GPU_dispatches": 0,
  "adapted_fixed_checks": 152,
  "all_passed": true,
  "certificate": "balanced-prime-237-section31-v1",
  "extra_fixed_links": 21,
  "first_moment_margin_lower_bounds": [
    {
      "rational_lower_bound": "59/500",
      "slot": 0
    },
    {
      "rational_lower_bound": "42828729571471189/366204096222703000",
      "slot": 1
    },
    {
      "rational_lower_bound": "14281959752685337/131833474640173080",
      "slot": 2
    },
    {
      "rational_lower_bound": "404775250280537827/6810685521693595500",
      "slot": 3
    },
    {
      "rational_lower_bound": "831665980583945971/6810685521693595500",
      "slot": 4
    },
    {
      "rational_lower_bound": "378067434689136667/6810685521693595500",
      "slot": 5
    },
    {
      "rational_lower_bound": "109619605063447799/3405342760846797750",
      "slot": 6
    },
    {
      "rational_lower_bound": "456078446976526793/3295836866004327000",
      "slot": 10
    },
    {
      "rational_lower_bound": "351499268595746779/6810685521693595500",
      "slot": 24
    }
  ],
  "independent_review": false,
  "inherited_predicates": 131,
  "moment_sweep": false,
  "retained_adjacent_slots": [
    0,
    1,
    2,
    3,
    4,
    5,
    6
  ],
  "retained_reflected_slots": [
    10,
    24
  ],
  "sampled_heights": 0
}
```

Every displayed rational lower bound exceeds `1/40`; these match the historical audit's recorded lower bounds. This comparison reads the existing audit result, not its program execution. The exact node inequalities are evidence for sections 31.7–31.12. All-height convergence, the all-positive-integer-moment implication, finite-node completeness, shape transfer and the infinite attainable sequence are supplied by the source proofs. The adapted run is fixed implementation verification, not independent review and not a fresh primary calculation or search.

For reproduction from a repository checkout, extract the same code bytes to any chosen external temporary directory, verify the identity, then run them. The following standalone extraction example needs only the checked-in report and Python's standard library; its temporary pathname is not a certificate input:

```sh
python3 - <<'PY_EXTRACT'
from pathlib import Path
import hashlib, tempfile
report = Path('docs/reports/balanced-prime-237-all-slabs-0910.md').read_bytes()
opening = b'<!-- fixed-certificate:' + b'begin -->\n```python\n'
closing = b'```\n<!-- fixed-certificate:' + b'end -->'
assert report.count(opening) == report.count(closing) == 1
code = report.split(opening, 1)[1].split(closing, 1)[0]
assert len(code) == 12265 and code.count(b'\n') == 271
assert hashlib.sha256(code).hexdigest() == 'cd3f0d53cc0bbad4ceb0f1563d64021e059b0afe5c297fa69ed794d4efb24af0'
target = Path(tempfile.mkdtemp(prefix='balanced-prime-237-')) / 'certificate.py'
target.write_bytes(code)
print(target)
PY_EXTRACT
# Run: python3 <the printed certificate.py path>
```

The extraction example is a reproduction recipe, not a second recorded execution. The original caller 131-check program was neither edited nor executed by I15, and the embedded program was not rerun after its success.

## Immutable prior evidence and limits

Caller-supplied completed actual-GPT-PRO task: `107ae020-e13b-4e13-a174-c5f1544a39d1`, flight `qgh0910-pro-balanced-prime-237`, attempt 1. Only its envelope `conclusion` was consumed; `log_ref` remained opaque. This worker did not independently identify the serving model, inspect any worker transcript, or infer model-family diversity. The primary self-reported nine fixed floating node evaluations as diagnostics and separately reported `Fraction` node verification plus eighteen integer guard evaluations. It supplied no aggregate count comparable to the caller's 131. Its diagnostics are not proof premises.

The earlier caller audit records 131 successful fixed predicates at `2026-09-09T17:44:33.073018+00:00`. That is historical caller evidence. The adapted 152-check execution above is new implementation evidence; its extra 21 links are separately identified. Neither is a Lean proof or a review vote. The preparation file described an earlier in-flight predecessor at its creation time; C43's sealed BASE below is the actual implementation base.

All four prior files were read without modification, with the primary payload limited to its conclusion. Exact identities are:

| Prior input basename (under `/tmp/qgh-boundaries-0908/`) | Bytes | LF | SHA256 |
|---|---:|---:|---|
| `pro-balanced-prime-237-envelope-0910.json` | 15248 | 159 | `7170e171ad3596e697ff4d515393606b935fb6d5237505d7191b464c46852439` |
| `caller-balanced-prime-237-audit-0910.json` | 13625 | 578 | `82b9062f4bc0bff3b6d35e889516bc78f3cb26cca84372d54d7557752ff5ec64` |
| `caller-balanced-prime-237-audit-0910.py` | 6879 | 156 | `2f972594f3d14641db91d2f70b29a60c96d13242dd7fc739b16f9ba0e29749dd` |
| `balanced-prime-237-source-preparation-0910.json` | 5386 | 80 | `0c0f03685baa69430fd278ab65a93378b80032fb4f89620d183ed67cc146afe4` |

The primary's two actual failed public retrievals remain failures; they were not silently recast as independent GitHub access:

| Immutable public URL attempted by the primary | Actual reported outcome |
|---|---|
| <https://github.com/the-omega-institute/trureturing/blob/feb497ec31f68e09ccc547a08810c398e66f3ee6/docs/develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md> | `DisabledError`; source contents not inspected |
| <https://github.com/the-omega-institute/trureturing/blob/391f7355698085c6500b46838a093dad05947ffb/docs/reports/prime-slab-finite-design-0909.md> | `DisabledError`; source contents not inspected |

I15's local source reads and the classical-source retrievals below have separate provenance and do not repair those historical accesses. No same-round peer implementation/review envelope, caller transcript, log content, live S19 worktree or other live target was opened.

## Focused classical-source receipts

Five focused read-only public requests returned HTTP 200 with no redirect (`final_url` equals the URL below). These receipts attest retrieved bytes and the specified overlap only; they do not claim exhaustive literature coverage or priority for the specialized theorem.

| URL / received file | Retrieval UTC | Bytes | SHA256 |
|---|---|---:|---|
| <https://home.cse.ust.hk/~dekai/271/notes/L14/L14.pdf> (`hkust-knapsack.pdf`) | `2026-09-09T20:40:46.868675+00:00` | 51456 | `02a501415b8472ca147d17d6e5369d7889f7b2aeba7b9ba37082e7dbebdefa7d` |
| <https://web.stanford.edu/class/ee364a/lectures/functions.pdf> (`boyd-functions.pdf`) | `2026-09-09T20:40:46.869137+00:00` | 405347 | `c172569e16a24039ac7dd0ae9d1ee743e31eb6a9369eac38206b758cbe76903b` |
| <https://arxiv.org/pdf/1801.00977> (`integrated-quantiles.pdf`) | `2026-09-09T20:40:46.869264+00:00` | 514768 | `f7378b6383d5b686146326a0ad6d7c29c76ad29816a5f47949ec67de61631c39` |
| <https://encyclopediaofmath.org/wiki/Dirichlet_theorem> (`dirichlet.html`) | `2026-09-09T20:40:46.869754+00:00` | 23171 | `8f363716f6de68ce4d46d669caba2ebab574eac52ae751d052943071a6eb30a5` |
| <https://dlmf.nist.gov/4.6.E1.tex> (`log-series.tex`) | `2026-09-09T20:40:46.869871+00:00` | 69 | `f5bdb547043c7dac361980c2de25ca3762b6fae40f38eba76d53dc600b7e531c` |

- **Fractional knapsack:** HKUST Lecture 14, PDF pp.4–7: decreasing value/weight, a fractional last item and the exchange argument. This supports the classical optimizer used in 31.4, whose exact matched price proof and endpoints are included in the source.
- **Convexity:** Boyd/Vandenberghe, *Convex functions*, PDF pp.6,16,26,27 (slides 3.4,3.14,3.24,3.25): norm convexity, Jensen and monotone composition. Section 31.6 explicitly checks nonnegative convex distances, the decreasing-radius envelope and positive support; no generic composition rule is invoked without its hypotheses.
- **Increasing convex order:** Alexander A. Gushchin and Dmitriy A. Borzykh, *Integrated quantile functions: properties and applications*, *Modern Stochastics: Theory and Applications* 4(4) (2017), 285–314, DOI `10.15559/17-VMSTA88`, arXiv `1801.00977` v1 (January 2018). PDF p.10 / journal p.294, Theorem 5(ii) and proof, gives the relevant increasing-convex/positive-part characterization. The source's mass-three convention normalizes to probability by dividing by 3. Its finite-atom cumulative argument is written out and does not require equal first moments.
- **Homogeneous approximation:** Encyclopedia of Mathematics, *Dirichlet theorem*, subsection “In Diophantine approximations”: simultaneous approximation of multiple real numbers and the box principle. Section 31.18 uses only the explicitly proved two-dimensional `Q=N^2` pigeonhole case, then a unique-factorization argument for unboundedness and positivity. No general inhomogeneous density claim is inferred.
- **Logarithmic series:** NIST DLMF equation 4.6.E1, the retrieved TeX for `ln(1+z) = z - z^2/2 + z^3/3 - ...`. Applying this to `t` and `-t` gives the atanh series used in the exact logarithm enclosure; its positive tail bound and the positive exponential Taylor-tail argument are stated in the source.

`pdftotext` was unavailable. Python `pypdf` supplied the needed page extraction, with missing-fontTools / CFF Type1 decoding warnings. Some HKUST formula glyphs were incomplete; the stated greedy prose was readable, as were the relevant Boyd slides and Gushchin–Borzykh theorem/proof. This is a disclosed extraction limitation, not a claim of complete flawless PDF decoding. No extra tooling was installed. The self-contained derivations and exact certificate carry the specialized formulas. The draft also had one missing LaTeX backslash in the actual-product line, corrected within the appended section before final identity recording and ingestion; no failed certificate run occurred.

## Source identity and canonical ingestion boundary

Worktree: `/Users/auricstudio/trureturing-qgh-balanced-prime-237`; branch: `lane/math/quantized-gh-balanced-prime-237-0910`; immutable BASE: `7b443a1764e5756c670b3912300a71f5b2e470f3`. The complete predecessor prefix remains **286326 bytes / 5391 LF**, SHA256 `4856aba958844029d1c7150f610104d3652dcfd25139bdfb53e4346cd905db0a`. Only section 31 was appended. All historical CAS/entry/report bytes are to remain unchanged, including the previous terminal-LF version of the final source unit.

The complete source prepared for ingestion is **316724 bytes / 5974 LF**, SHA256 `9229e2affc81243efcdcbd228058d8ca19cea395630a94ae943afde374157dd2`. The appended suffix is **30398 bytes / 583 LF**; source byte offsets in the implementation envelope use zero-based half-open spans and line numbers are one-based inclusive. The report hash is recorded externally in that envelope to avoid a circular self-identity.

The single authorized ingestion invocation, after source and report content are ready, is:

```sh
make ingest BASE=7b443a1764e5756c670b3912300a71f5b2e470f3 SOURCE=arithmetic-boundary-quantization
```

The implementation envelope records the actual command outcome, changed-file manifest, all canonical bindings, raw and normalized fingerprints, `cas_ref`, source offsets/lines and ordered children after execution. Every numbered unit's complete source span must be covered, not merely its start; structural headings need not be claim atoms. Fingerprints and `cas_ref` use `sha256:` prefixes, while child atom IDs are bare. All actual generated children and the historical terminal-LF variant are retained exactly as produced. No manual canonical-EOF, ledger, metadata or producer repair is authorized or used.

I15 is the assigned isolated CLI implementation worker under caller-pinned `consensus-rnd:sshx1.0.0-beta.42` and its `CODEX_WORKER_SPEC.md`, with CLAUDE 5.11 and the caller's explicit no-delegation boundary controlling composition and continuation. No native subagent, oracle, review, lifecycle action, daemon, candidate generation, GPU execution, old-search replay, broad build/preflight, tools/Lean/frozen edit or Git mutation is part of this layer. CPU work is fixed proof verification and necessary orchestration. The returned work is unstaged. Caller owns sealing, independent review, ordinary repository gates, push/PR/publication and final delivery after **S19 MERGED**; the predecessor's merge status was not independently asserted here. This implementation does not complete the standing research goal.

The reasoning frame is the existing positive-grid dual/Euclidean envelope, classical fractional knapsack, increasing convex order and homogeneous approximation. The coherent form is a complete wider-domain reduction, one fixed nine-node certificate, and a transfer argument that compares all mixtures without branch stability. The material domain risk was reuse of `(2,3,5)` statements outside their literal hypotheses; the new source proves the required extensions. The exact greedy-range link closes the difference between an outward rational quotient and a true endpoint weight. Finite verified inputs and analytic quantifiers remain separate. Within this bounded implementation no material mathematical defect remains identified; broader primes/shapes, priority, serving-model identity and delivery are not promoted to verified conclusions. The depth boundary is this prescribed theorem and source/report/ingestion layer, not a research-termination judgment.

## C72 current placement, provenance, and coverage note

This I25 placement record scopes the historical S20/I15 body above, as stored at `fe3f12abe8bc2e14628a93990fee2755c30da2bd`. Its 31,711 original bytes occupy 31,714 current bytes after the sole three-byte navigation insertion. All earlier “current”/“new” statements, paths, counts, hashes, classifications, source identities, retrievals, commands, execution results and ingestion statements retain their own documented historical times and scopes. The same applies to I15 provenance and execution/ingestion statements in source 31.21–31.22. In particular, source SHA256 `9229e2affc81243efcdcbd228058d8ca19cea395630a94ae943afde374157dd2`, report SHA256 `2b100f9d29e4d481fe7f76433ddbd3644eb925975f52bd7655584a839b49c0fa`, C43 BASE `7b443a1764e5756c670b3912300a71f5b2e470f3`, caller 131 checks and I15’s single adapted 152-check run remain historical snapshots. This note records no new mathematical result or execution.

The report now resides at `docs/reports/quantized-gh/balanced-prime-237-all-slabs-0910.md`. At zero-based source offset 314676 (line 5948, 31.21), I25 inserted exactly `quantized-gh/` (13 bytes); at original report offset 124 (line 3), exactly `../` (3 bytes). The current source destination `../../reports/quantized-gh/balanced-prime-237-all-slabs-0910.md` and report backlink `../../develop/theory/ARITHMETIC_BOUNDARY_QUANTIZATION.md#31-三素数-237-的九节点证书与整箱全薄层邻域` resolve to their files. The original anchor is verbatim; inherited S19 addresses are untouched. The historical extraction recipe retains its old path; reproducing it would require the current report path, but I25 did not extract-and-execute it.

The current source is 316,737 bytes / 5,974 LF, SHA256 `3f27fbd4bef498d995cd7e1bd566c960ad8a384c5f04f8b5b2a91cb1625dc351`. Deleting current source interval `[314676,314689)` recovers all 316,724 BASE bytes. Taking report `[0,31714)` and deleting `[124,127)` recovers all 31,711 BASE bytes; this note starts at 31714. Both recovered bodies equal the allowlisted caller snapshots. The embedded 12,265-byte / 271-LF executable, SHA256 `cd3f0d53cc0bbad4ceb0f1563d64021e059b0afe5c297fa69ed794d4efb24af0`, is unchanged inert text. The 152 and 131 checks, raw payloads, assertions, errors and evidence classifications retain their original provenance. Two primary `DisabledError` retrievals remain failures; I15’s five HTTP 200 requests remain focused historical retrievals, with unavailable `pdftotext`, pypdf/fontTools/CFF warnings and incomplete HKUST glyphs. I25 made no new literature retrieval.

The 22 current whole-unit bindings below cover `[286396,316737)` without gaps (30,341 bytes); the preceding 69-byte section heading is structural. For each ID, CAS is `Meta/Digestion/atoms/sha256/<id>` and YAML is `Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/<id>.yaml`. Every full span equals its CAS bytes. Each YAML has identical `raw_sha256`, `normalized_sha256` and `cas_ref` values `sha256:<id>`, empty `coverage_gids` and `receipts.unresolved_subitems`, and no ordered children or chain. Offsets are zero-based half-open; lines are one-based inclusive.

| unit | source byte span `[start,end)` | lines | atom_id / CAS and YAML basename |
|---|---:|---:|---|
| 31.1 | `286396,287868` | `5395–5413` | `a3d2dfbbd30f2b02f3cd0cb0de014f2d39a4dcda70da8dd821cf2efbadc9a393` |
| 31.2 | `287868,289745` | `5414–5453` | `0be59d21c69aa72d67f4ec597dacf58c88edf66db8232bc8dc1fc71efe04a21b` |
| 31.3 | `289745,290770` | `5454–5475` | `2a3f7444911832698e244eb782de1a8714ec6ecf0ffbc0b0bf7cf2226d940e3c` |
| 31.4 | `290770,291950` | `5476–5498` | `1a54a6183ad88b96e803453e73cfe6b74c491fafaf1ac0dd69c5c5c5a9c6162c` |
| 31.5 | `291950,293373` | `5499–5524` | `5a64fb3857c7fdf6efd603c05a197b4bb55098c9279416cc5b6d2ee5a7cf2245` |
| 31.6 | `293373,295092` | `5525–5556` | `32afc62c98de321b1a38b77a2063f24ea7f5005c75186f499353cab39e10ec22` |
| 31.7 | `295092,296401` | `5557–5582` | `53296486ed232186fcd6a5839bc00537a418662da699351e42f6c8ede80467c0` |
| 31.8 | `296401,297465` | `5583–5608` | `1b9fcc68044e7d95c433e3ab46e24840d411663c818add48a5d6bcaac7b760a3` |
| 31.9 | `297465,298829` | `5609–5635` | `45f91b8b5474b7afd95e7b0b00d16ceac3aefca1e0146f0c90574d1639c72868` |
| 31.10 | `298829,300258` | `5636–5667` | `aef948efeeebd9af5b667646d176b4ef4c92e1e74a9f3c6a716ae992c5f036d8` |
| 31.11 | `300258,302246` | `5668–5722` | `9df3ed2502f24227234912ddc76091d92dbcf57cc37041885f4891fa5dbdc57e` |
| 31.12 | `302246,303641` | `5723–5753` | `126bc3571bcbac93f7fdb5a0d533f90c804323969953128cc652b26a35a5ef45` |
| 31.13 | `303641,304248` | `5754–5770` | `ed4edb6d9cccc93dee709af5f20edf5ee3bab995acd19e9dfb90e0661d5ddfd8` |
| 31.14 | `304248,304866` | `5771–5781` | `213738e1deed74d55481b5af448c8953fe4e9853fe3ef6f01d1c05e1d67f9801` |
| 31.15 | `304866,305962` | `5782–5805` | `cba3c1a89589e252a81fc3b8abb0f2a4cd1baafa88b4794a24e992cba4168f5b` |
| 31.16 | `305962,307430` | `5806–5834` | `8c61b20e7390ed05bd75dadb4f509f09dbc5a25b02eb071773c741a59afb9837` |
| 31.17 | `307430,307975` | `5835–5849` | `8bae706cc82dbe8a812fa9b0974a27bb2139f9223426e195a4f223d8c9ce0095` |
| 31.18 | `307975,309521` | `5850–5875` | `edc19ada48d671aa3902f203f9f210c0fbd1f36c2dec82dcea7a067b41acd80b` |
| 31.19 | `309521,310682` | `5876–5898` | `393537011e7bd06dbb3b66e60b5ea0d74500ce0bfe3c290da266cea124868c02` |
| 31.20 | `310682,312043` | `5899–5916` | `023e3b1466025fc225d800c3dd465c445efb19b600cf5e8ca5f28e7a02fc4daf` |
| 31.21 | `312043,314731` | `5917–5949` | `f2fab9d4d570e602fa98a391dc85e63152f7caa22cbd49a7aa43d47ee3b38493` |
| 31.22 | `314731,316737` | `5950–5974` | `eae7985cf6b6ca0ed4b57eca118b4b48b116ff73442ea4cf699dec0cea6ff3c9` |


All 23 old S20 pairs remain exact BASE bytes: the 21 unchanged 31.x IDs above, old 31.21 `d080b2cc1aee415399495a49b7f5db89c10c5c7f9f5fac9cd6776cee2e1d5cae`, and 30.21 `2e4936cf8d14b00684fef92027ebcc5074feadefbce0305606d5851ad4c584ce`. Both old 30.21 LF variants, including `41d300e7a5f0f9881740937ed7ebe63480459a69e0e0ba4c118088e4975a6140`, remain unchanged with their YAML entries. The only fresh pair is current 31.21 `f2fab9d4d570e602fa98a391dc85e63152f7caa22cbd49a7aa43d47ee3b38493` (2,688-byte / 33-LF CAS and 328-byte / 7-LF YAML).

I25 ran exactly once: `make ingest BASE=fe3f12abe8bc2e14628a93990fee2755c30da2bd SOURCE=arithmetic-boundary-quantization`, exit 0; the writer reported `residual_open_added=1`, `skipped_existing=269`, `coarse_fallbacks=0`, `open_genres=0`, `cas_objects_written=1`, `ledger_changed=true`. No second ingest or manual canonical edit occurred. Tracked `git diff --check` exited 0 without diagnostics. Untracked `git diff --no-index --check /dev/null <path>` exited 1 without diagnostics for this report and the YAML (ordinary addition-only differences); the new CAS exited 3 with `:33: new blank line at EOF.` Its two terminal LF bytes are the exact source-span ending and remain unnormalized. The worker handoff supplies complete identities and command receipts.

The caller’s original terminal/three-approve settlement is dispatch provenance only; I25 did not open reviewer envelopes and it does not approve this placement. All changes remain unstaged. Caller retains sealing/push, public byte verification, fresh complete representation review, inherited-address integration, current capacity and ordinary CI/PR gates, and S19-before-S20 MERGED delivery. This repair makes no fresh independent-review, MERGED, model-diversity, RH, Lean, novelty or continuous-goal completion claim.

## C85 / S20 section 31 archival representation (I29, 2026-09-10)

This is historical report ownership, not a second active theory source. The complete preceding 39,335 bytes, including the original fixed executable certificate and the C72 placement note, remain verbatim. Records inside the archive below describe their original I15/I25 periods; none describes a certificate, literature retrieval, historical audit or old ingest executed by I29.

C85 explicitly supersedes active-source byte equality only for the mapped section 31 operational passages and necessary mathematical type/citation metadata. All mathematical wording, numbers, tables, proofs and actual scope limitations remain active; classical citations from 31.21 are attached to their corresponding proofs. The original 31.21 address now resolves through those attachments plus its historical remainder; 31.22 is wholly archived. Both numbers are permanently reserved and must never be reused. The JSON companion records every original source byte, every current addition and each old/new numbered identity. Intervals are zero-based UTF-8 byte offsets with exclusive ends; payload boundaries exclude the surrounding archive labels and fences. Reconstruct the original source by concatenating destination slices in original-byte order.

The preserved 286,327-byte prefix includes the separator LF and is the inherited S20 representation, SHA256 731be813ad24c47bec760cb7dff17ee02731cd8d2df4ba7556c7a2e403b0304f. It is still mixed mathematical/process prose. It is not assumed byte-identical to the original C78/S19 source. This downstream tail preparation neither repairs the complete inherited body nor settles the C82 proof obligation. Actual C82 PRO work, S19-first complete-body migration, reconciliation of mathematical/source mappings, complete pure-predecessor integration, fresh full-source review, ordinary delivery gates and S19-before-S20 MERGED remain pending with the caller. Earlier reviews remain historical; this implementation is not independent approval, new primary research, Lean admission, an RH/novelty claim or standing-goal completion.

Historical C72 recovery remains exact: after reconstructing the 316,737-byte source (SHA256 3f27fbd4bef498d995cd7e1bd566c960ad8a384c5f04f8b5b2a91cb1625dc351), remove [314676,314689), the 13 bytes `quantized-gh/`, to recover 316,724 bytes / SHA256 9229e2affc81243efcdcbd228058d8ca19cea395630a94ae943afde374157dd2. Take report [0,31714), remove [124,127), the three bytes `../`, to recover the 31,711-byte original / SHA256 2b100f9d29e4d481fe7f76433ddbd3644eb925975f52bd7655584a839b49c0fa. The preceding placement note [31714,39335) remains 7,621 bytes. This is a recovery recipe, not a replay or a relabeling of prior execution.

All original CAS/YAML, including both 30.21 terminal-LF variants and both historical 31.21 identities, remain immutable. The caller's original 131 predicates and I15's adapted 152 = 131 + 21 predicates remain distinct historical evidence. The primary's two DisabledError retrieval failures, I15's five limited HTTP 200 requests, unavailable pdftotext, pypdf/font/glyph warnings, and all I25/caller process and audit deviations disclosed in the preceding report/placement note remain in force. No fresh literature retrieval or arithmetic execution supports this migration.

### Verbatim relocated source payloads

#### Archive 004: 31.1, original bytes [286409,286418)

Operational status title fragment. Verbatim payload:

~~~~~text
、状态
~~~~~

#### Archive 006: 31.1, original bytes [286457,286653)

Model, task, implementation and prior execution provenance. Verbatim payload:

~~~~~text
本节为 C43 / S20 的
PAPER_ARGUMENT / repo-derived 参考输入,实施已完成的实际 GPT PRO primary
107ae020-e13b-4e13-a174-c5f1544a39d1 和既有 caller 固定核验所支持的数学。

~~~~~

#### Archive 008: 31.1, original bytes [287807,287831)

Priority and novelty nonclaims. Verbatim payload:

~~~~~text
优先权、新颖性、
~~~~~

#### Archive 010: 31.1, original bytes [287833,287856)

Formal admission status nonclaim. Verbatim payload:

~~~~~text
 或 Lean/kernel-frozen
~~~~~

#### Archive 026: 31.8, original bytes [297435,297460)

Execution nonclaim; all-positive-height optimality retained. Verbatim payload:

~~~~~text
;本表没有采样高度
~~~~~

#### Archive 034: 31.11, original bytes [300596,300621)

Arithmetic execution modality; exact rational proof retained. Verbatim payload:

~~~~~text
认证不用浮点对数:
~~~~~

#### Archive 036: 31.11, original bytes [302112,302244)

Report executable placement and execution-scope nonclaim; all series, constants, inequalities and proof steps retained. Verbatim payload:

~~~~~text
报告嵌入全部固定常数和可执行有理运算;
80 项对数证书和 12 次指数多项式均不是高度或矩阶扫描。
~~~~~

#### Archive 040: 31.12, original bytes [303397,303445)

Historical adapted-certificate provenance; full weight-domain obligation and sign linkage retained. Verbatim payload:

~~~~~text
报告的改编证书明确补上这一链接。
~~~~~

#### Archive 044: 31.13, original bytes [304186,304247)

Execution/diagnostic nonclaim; analytical infinite quantifier retained in 31.9–31.13. Verbatim payload:

~~~~~text
没有以有限若干矩或浮点诊断外推无穷量词。

~~~~~

#### Archive 056: 31.18, original bytes [309341,309399)

Execution nonclaim; non-effective scope and full existence proof retained. Verbatim payload:

~~~~~text
没有执行上述抽屉构造或产生任何指数见证,
~~~~~

#### Archive 062: 31.20, original bytes [311489,311496)

Ticket identifier; third-prime-ray exclusion retained. Verbatim payload:

~~~~~text
C39 的
~~~~~

#### Archive 064: 31.20, original bytes [311570,311592)

Search/program scope statement; mathematical exclusions retained. Verbatim payload:

~~~~~text
及搜索/程序工作
~~~~~

#### Archive 066: 31.20, original bytes [311998,312038)

Implementation/standing-goal status; mathematical OPEN scope retained. Verbatim payload:

~~~~~text
,本次实施不完成长期研究目标
~~~~~

#### Archive 068: 31.21, original bytes [312043,312250)

31.21 historical provenance/retrieval/execution remainder; number permanently reserved externally. Verbatim payload:

~~~~~text
**31.21 经典出处、历史访问失败和固定核验的产地。** 专门九节点、两项缩放裕量、
整箱传递和实际格点应用标为 repo-derived。经典工具当场作聚焦只读核对:

~~~~~

#### Archive 070: 31.21, original bytes [312401,312402)

31.21 historical provenance/retrieval/execution remainder; number permanently reserved externally. Verbatim payload:

~~~~~text


~~~~~

#### Archive 072: 31.21, original bytes [312560,312561)

31.21 historical provenance/retrieval/execution remainder; number permanently reserved externally. Verbatim payload:

~~~~~text


~~~~~

#### Archive 074: 31.21, original bytes [312953,312964)

31.21 historical provenance/retrieval/execution remainder; number permanently reserved externally. Verbatim payload:

~~~~~text

另核对 
~~~~~

#### Archive 076: 31.21, original bytes [313032,313041)

31.21 historical provenance/retrieval/execution remainder; number permanently reserved externally. Verbatim payload:

~~~~~text
,
以及 
~~~~~

#### Archive 078: 31.21, original bytes [313241,313242)

31.21 historical provenance/retrieval/execution remainder; number permanently reserved externally. Verbatim payload:

~~~~~text


~~~~~

#### Archive 080: 31.21, original bytes [313324,313460)

31.21 historical provenance/retrieval/execution remainder; number permanently reserved externally. Verbatim payload:

~~~~~text

PDF 文本提取有字体解码警告,HKUST 若干公式字形不全;实际可读的算法文字与
其它指定定理/公式已核对,
~~~~~

#### Archive 082: 31.21, original bytes [313529,314731)

31.21 historical provenance/retrieval/execution remainder; number permanently reserved externally. Verbatim payload:

~~~~~text

检索收据及其适用范围见报告,不作穷尽文献或优先权声明。

primary envelope 的 SHA256 为
7170e171ad3596e697ff4d515393606b935fb6d5237505d7191b464c46852439;
只消费其 conclusion,log_ref 不透明。它原报两次公开获取均失败于 DisabledError:
封存 feb497ec31f68e09ccc547a08810c398e66f3ee6 的本源文件 URL,
及封存 391f7355698085c6500b46838a093dad05947ffb 的
docs/reports/prime-slab-finite-design-0909.md URL。它没有读取这些源字节;
本实施对本树的读取不改变这一历史事实。primary 自报九个指定节点的浮点计算
仅作有界诊断,另有 Fraction 固定证书与十八项整数资格核对;不把诊断列为证明前提。
caller 原审计记录 131 项全通过,不是 primary 的执行计数,也不是本轮独立评审票。
原审计与程序保持原字节且未重跑。新报告把相同常数改编为无 caller-local 路径依赖的
自足可执行证书,另补固定输入到证明假设的链接,只执行改编证书一次。
精确命令、版本、字节/hash、实际结果及各类证据分工见
[balanced-prime-237-all-slabs-0910.md](../../reports/quantized-gh/balanced-prime-237-all-slabs-0910.md)。


~~~~~

#### Archive 083: 31.22, original bytes [314731,316737)

31.22 wholly operational historical entry; number permanently reserved externally. Verbatim payload:

~~~~~text
**31.22 单一内容层、保留边界及 caller 交付义务。** 本层由隔离 Codex CLI 实施席 I15
在 caller 固定的 consensus-rnd:sshx 1.0.0-beta.42 和 CODEX_WORKER_SPEC.md 下产生,
flight qgh0910-i15-balanced-prime-237,attempt 1。遵照 CLAUDE 5.11 和明确 brief,
无 native subagent、委派、额外 oracle 或本轮评审票;repo-prior-exposed,
不声称上下文无先验或模型族多样性。实际 GPT PRO 来源取自 caller 既有身份记录,
本实施未独立鉴定 serving model。准备输入中旧的 predecessor-in-flight 描述属于其准备时刻,
本层实际 immutable BASE 为 7b443a1764e5756c670b3912300a71f5b2e470f3,
工作树为 /Users/auricstudio/trureturing-qgh-balanced-prime-237,
分支 lane/math/quantized-gh-balanced-prime-237-0910。

第 1-30 节完整前缀保留 286326 字节、5391 个 LF,SHA256
4856aba958844029d1c7150f610104d3652dcfd25139bdfb53e4346cd905db0a;
全部历史 CAS、entry 和报告保留。只追加本节、单一报告和以下命令的实际 canonical 输出:
~~~sh
make ingest BASE=7b443a1764e5756c670b3912300a71f5b2e470f3 SOURCE=arithmetic-boundary-quantization
~~~
源语义、固定证书及其 CAS/YAML 绑定属于同一可审查内容层,不拆出脱离源的派生地址。
全部自动 children、历史末单元 terminal-LF 变体和 producer EOF 均保留原字节,
指纹与 cas_ref 带 sha256: 前缀,子 atom_id 为裸 hash;完整映射由实施结论提供。
摄入不等于 Lean 吸收或冻结。CPU 仅用于固定证明核验和必要编排,
无候选搜索、旧搜索重放、GPU、daemon、工具/Lean/frozen 编辑或广泛 build/preflight。
没有读取任何 worker 日志、log_ref 内容、caller 转录、同轮 peer 结果或其它 live target。
本层返回 unstaged;caller 负责其后封存、独立评审、普通仓库门、push/PR/发布,
最终 S20 交付等待 S19 MERGED。本实施不作 review 或 termination 判词,
不执行暂存、commit、push、PR、merge 或生命周期命令。

~~~~~

### I29 current migration and producer receipt

I29 used codex-cli 0.154.0 and the pinned consensus-rnd:sshx 1.0.0-beta.42 worker contract. Target CLAUDE.md, agents/CONTEXT.md and both pinned skill files were completely read before target actions; truncated prerequisite outputs were recovered in bounded chunks. The caller-supplied current 3.8/5.11 override (guidance blob 7fda0813773083e59b3783843c16b55f560f7805) governs this explicit disposition. Starting HEAD/repair BASE is db8037532d5dea5067e0edfb3fcaebc671eccbf2 on lane/math/quantized-gh-balanced-prime-237-0910; initial status was clean. The scientific BASE is historical only.

The only current ingest invocation was:

```sh
make ingest BASE=db8037532d5dea5067e0edfb3fcaebc671eccbf2 SOURCE=arithmetic-boundary-quantization
```

It exited 0 and printed `INGEST residual_open_added=20 skipped_existing=248 coarse_fallbacks=0 open_genres=0 cas_objects_written=20 ledger_changed=true`. The unchanged producer emitted exactly 20 CAS/YAML pairs; no predecessor-boundary pair, child, chain, coverage GID or unresolved subitem was added. All 166 current numbered spans match their full canonical bodies; every new YAML is the complete seven-line empty-receipts structure. Current source SHA256 is 28ee1eb94e166ef4f8b4f2b01408779b2fdfe0d05ee692a0158790841e2fe894 (312,957 bytes / 5,939 LF). No source edit followed ingest.

Both pre-ingest and post-ingest fixed recovery checks passed 314/314: exact full original reconstruction, original prefix/report/certificate preservation, C72 inverses, all 52 display-math blocks unchanged in order, all 292 inline-math literals preserved, every mapped current addition accounted for, and all 50 separately pinned historical canonical paths unchanged. The complete analytical review covers all 22 original units, including mathematical prose, examples, limits and dependencies; literal formulas alone are not its substitute. No new mathematical claim, easier assumption or new proof was introduced.

Current entire-unit bindings (one CAS and one matching YAML per SHA256) are below. CAS paths use `Meta/Digestion/atoms/sha256/<SHA256>`; YAML paths use `Meta/Digestion/backfill/arithmetic-boundary-quantization/residual-open/<SHA256>.yaml`. Exact old/new and archive addresses, all changed canonical paths, file identities, source byte partitions and citation/type additions are recorded in [theory-body-migration-s20-0910.json](theory-body-migration-s20-0910.json).

| Unit | Current source bytes [start,end) | Current source lines | CAS/YAML SHA256 identity |
|---|---|---|---|
| 31.1 | [286396,287716) | 5395–5412 | `e203a5fdc570e70bc107641b7c0aa5ab1e66d9f83b23c75a46db819d2c31c3a9` |
| 31.2 | [287716,289602) | 5413–5452 | `74b30d5f33553ada17490d2dbd669a36cc5d98342c1b6ca57b8af89b36382b80` |
| 31.3 | [289602,290636) | 5453–5474 | `28df2a866cf2599b3db54e34a9b48622ab51e31ddcc65c6494f6335459d7b223` |
| 31.4 | [290636,292012) | 5475–5501 | `4e93abc85901724bc34ef7bfbc4eeb7a80d59894310295600607edd58a88836f` |
| 31.5 | [292012,293444) | 5502–5527 | `faf2dd9aa53dcbbb7655830f4bead0ebe479e98441b83658cd6990d559ece2e9` |
| 31.6 | [293444,295366) | 5528–5563 | `ed92624998d14e9206a6f63096dd75eed9187f3bea27cf9f9bc6de0543b58e90` |
| 31.7 | [295366,296684) | 5564–5589 | `e4456d5e7c99e47cb1d52fa62650b401d8e52d1766b0090979ac037294fc89d3` |
| 31.8 | [296684,297732) | 5590–5615 | `ff96fb9f894a4be2a0e4e89e397130c9aa75859e43d7f28625bcb30ebc9a15db` |
| 31.9 | [297732,299114) | 5616–5642 | `020d834706e562c524e2c5a85dc7e1afbfdbfa88e2e692d1a8fd738003667dda` |
| 31.10 | [299114,301064) | 5643–5683 | `1354efff2359ce7e651c3da6604e346644b9b5e0eac9b790d3971d986efd6fc8` |
| 31.11 | [301064,303079) | 5684–5742 | `aaa5c1e2d362254798ef93f6912a968fe376a81085719573f07dd3f743e10082` |
| 31.12 | [303079,304435) | 5743–5773 | `7a568d646a3f73f21196340d3b310008e6078132fdb70a9cc83941956f59b82b` |
| 31.13 | [304435,304990) | 5774–5789 | `c4370324efffbd29226372285085a59f4b37121d47409e8f4952f4ed8895317f` |
| 31.14 | [304990,305617) | 5790–5800 | `9a7622e2188ec059d639e90b52d45c687a5a31789cc1f1a663104410da9507eb` |
| 31.15 | [305617,306722) | 5801–5824 | `51e024ecf2bac9615eb77aaf3436725490e37d13948b4c5cdcea7c4b981945f2` |
| 31.16 | [306722,308199) | 5825–5853 | `0b42e820527004ab3e7244c3c02f2f2892f612f21c45e84f6ca616831351a0ab` |
| 31.17 | [308199,308753) | 5854–5868 | `dfc9b7f0fe8d10470a9210f46cc79b8f82205f3a6bcdda79b13b12b62917e785` |
| 31.18 | [308753,310486) | 5869–5898 | `cdc610937f5756f7321801922d966f4d21d0b6acc2bf73ea23fa45daa7558ec5` |
| 31.19 | [310486,311656) | 5899–5921 | `bdc653a8245dd48a3f82bc00d5d05326f69e59583a891594c0da7b791360dbbd` |
| 31.20 | [311656,312957) | 5922–5939 | `b8003665e354e4b0cdba7d5bd42652ae1d60879902b6d997e7e33e99891dff46` |

The first wide canonical checker exited 1 (602/605) because it omitted a nested heading from inherited 24.2 and treated preserved whitespace diagnostics as defects. The second exited 1 (597/603) because its correction wrongly included peer-level headings after 24.5, 24.9 and 24.13. The unchanged producer's scoped-heading rule resolved these checker errors; the final checker exited 0 (606/606). No source/canonical repair or ingest replay followed these checks. These failed check receipts remain disclosed.

`git diff --check` exited 2: the active source line 5939 has a new blank line at EOF; report lines 658 and 667 have trailing spaces in the exact original payloads `另核对 ` and `以及 `. Each of the 20 new CAS `git diff --no-index --check /dev/null` calls exited 3 with only the producer-owned terminal blank-LF diagnostic; each of the 20 YAML calls exited 1 with no diagnostic. Those statuses are preserved, not reported as a clean whitespace pass. Nested instruction discovery returned rg exit 1 for no matches. The own-attempt assembly filename listing was initially overlong; narrowed exact-name discovery supplied the complete relevant result.

The canonical Make invocation used .NET SDK 10.0.400. Worker scratch, compiler outputs and SDK/NuGet locations were directed to the runner attempt directory, and shared compilation/node reuse were disabled; no separate build, test or cache/preflight command was run. Unexpectedly, the SDK first-use stderr reported `已安装 ASP.NET Core HTTPS 开发证书。` No trust command was run. The certificate store/location and actual host-side effects were not independently inspected; no cleanup was attempted. Thus this record makes no blanket no-hidden-runtime-state-change claim. The unchanged canonical producer also owns its normal per-worktree Git-directory ingest lock and atomic YAML temporary publication; I29 did not inspect, modify or clean that state manually.

All process logs and complete command receipts remain in the runner attempt artifacts. Only scoped source/report/JSON changes and the 40 actual canonical paths are returned, unstaged. No certificate, historical 131/152 audit, test, mathematical search, old ingest, GPU/runtime campaign, Lean or external literature retrieval was executed. No other physical target, peer output, caller transcript/registry or opaque log content was accessed, and no worker delegation or Git/PR/lifecycle action was performed. The inherited mixed-prefix, actual C82 proof/full S19 migration, complete pure-predecessor integration, fresh full-source review and S19-before-S20 MERGED obligations remain pending; this is section31 preparation only.
