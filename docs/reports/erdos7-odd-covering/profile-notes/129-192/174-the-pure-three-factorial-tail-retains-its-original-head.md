[Index](../../marked_head_profile.md) · [Original full factorial partition](../065-128/128-the-complete-factorial-tail-retains-its-head-off-the-face.md) · [Joint pure-five block](168-the-first-five-support-lowers-the-complete-factorial-bound.md) · [Joint pure-three moments](171-the-pure-three-path-has-a-joint-complete-moment-bound.md)

# The pure-three factorial tail retains its original head

On both complete saturated actual K faces, retaining the same
original head in the deep-three cross and pair terms improves
the complete factorial-tail bound from3091/3600 to2303/2700.
The exact additional saving is61/10800.

Using this head bound inside every original mean/factorial
objective, together with171's complete square2203/450, gives

    K<=458.6841170772124... .                       (T3F1)

The complete comparison improves171 by0.2400453677118394... .
All52 independent original tests, the same actual measure,
every other pair class and the full denominator remain. This
is an ordinary complete-face upper-bound theorem, not an
off-face or global result, Lean theorem, or unrestricted
Erdős7 resolution.

## 1. Isolate one actual pair block

For one independent original head layout ell write

    B=1+I3+I9+I5+I15+I45, h4(B)=max(B-4,0),
    R3=sum_(a>=3)I_(3^a).

The block to replace is exactly

    X3(ell)=integral[h4(B)*R3+binom(R3,2)].        (T3F2)

The existing128 pure-three head operator supplies, before its
maximum over cells, the coefficients

    A_l(ell)=sum_s pre(l,s)*w(l,s)*h4(B(l,s)).     (T3F3)

The table is the original pure-three `pre` table, not the
five-descendant table. Its actual measure inequality gives

    integral h4(B)*I_(J_a)<=A_l(ell)*3^-a

for every independent depth-a cylinder J_a in cell l. Separately,
171's projected complete-family proof gives

    mu(J_a)<=c_l*3^-a,
    c=(7/10,11/20,3/10,3/10,3/10).               (T3F4)

The cell permutation on the second K face transports both tables.
The three root1 coefficients agree, so the first-beta permutation
does not require concentrating the rest of the beta source.

## 2. A whole-path Bellman bound

Let n_l count the preceding deep-three labels that chose cell l.
Different cells are disjoint. For two tests in the same cell,
their intersection is bounded by the deeper cylinder whether or
not their residues are compatible. Thus the terms with largest
exponent a are bounded by

    [A_l(ell)+c_l*n_l]*3^-a.                     (T3F5)

This allows an independently changing cell at every exponent.
With q=1/3 define

    V_l(n)=(A_l+c_l*n_l)/(1-q)+c_l*q/(1-q)^2,
    V(n)=max_l V_l(n).

For the chosen cell l,

    A_l+c_l*n_l+q*V_l(n+e_l)=V_l(n).

For another cell k, V_k(n+e_l)=V_k(n), and
A_l+c_l*n_l<=(1-q)*V_l(n). Hence

    A_l+c_l*n_l+q*V(n+e_l)<=V(n).               (T3F6)

Starting at n=0 and a=3, the complete discounted value is

    X3(ell)<=Q3(ell)
      :=max_l[A_l(ell)/18+c_l/36].              (T3F7)

The terminal potential is O(N*3^-N) and tends to zero. For a
fixed actual source, nonnegative monotone convergence gives the
infinite pair sum. For varying finite-source approximants, the
global raw cap mu_N(J_a)<=3^-a and h4<=2 give the uniform tail
bound sum_(a>A)(a-1)*3^-a, which vanishes. Stabilizing each finite
set of residue labels then passes the inherited face limit.

## 3. Replace the old unordered-pair term exactly once

The original128 scalar pure-three/deep-three pair allowance is

    (7/10)*sum_(a>=3)(a-3)*3^-a=7/360.          (T3F8)

The certificate's ordered block is7/180 before halving. The
original head cross is max_l A_l/18, so the correction is

    Delta3(ell)=Q3(ell)-max_l A_l(ell)/18-7/360.

Each c_l<=7/10 implies Delta3<=0 for every head. This correction
replaces only(T3F2). The independent pure-five correction in168
replaces a disjoint head-cross/pair block, so both are added to
the same original head. Mixed-prime, root-five, cell-five,
old/seven and seven/seven classes remain unchanged.

The complete pair complement2539/3600 stays in the assembly;
the corrections subtract7/360 and1/200 internally exactly once.
The original128 disjoint partition is checked directly before
either subtraction is accepted.

One cannot replace A_l by min(A_l,c_l): h4 can equal2. For
example, layout(1,3,2,1,2,3,2) gives A3=8/25>c3=3/10.
The density cap controls mass, while A3 is already weighted by
the head multiplicity. The new proof keeps these roles separate.

## 4. The same original layout carries both improvements

Across all12500 original layouts, the exact pure-three changes are

| Delta3 | Number of layouts |
| --- | ---: |
| -1/90 |2|
| -2/225 |88|
| -1/225 |240|
| -1/240 |164|
| 0 |12006|

The isolated Q3 block still has maximum1/24, so maximizing it
separately would conceal the improvement. Retaining the same
layout in the entire factorial head gives

    max_ell[J168(ell)+Delta3(ell)]=319/2160.

The unique maximizing layout is(0,1,2,0,2,1,2). There

    A=(0,8/25,0,0,0), Q3=119/3600,
    old_three_block=67/1800, Delta3=-1/240.

With the complete pair complement, this proves

    T5<=319/2160+2539/3600=2303/2700.            (T3F9)

For every positive factorial cost expansion, the consumer
maximizes the mean expression and this new head term together,
using the same original ell and the same independent positive7
test. It does not insert(T3F9)'s scalar maximum into an unrelated
mean head. All1,250,000 combined objectives are evaluated exactly.
The raw81 row with signed coefficients keeps its previous bound.

## 5. Complete comparison and reproduction

The consumer starts from171's full52 vector and Q=2203/450.
After reaggregating the same original costs and running the
existing majorant propagation, the complete bound is(T3F1).
The mass53/360, mean1151/1800 and complete denominator
50511415637/632754738000 remain. All AP11 blocks, the AP13 loss
and the remaining count tail are retained.

The [helper](../../frontier/moments-survival/pure_three_joint_factorial_comparison.py)
pins171 and168, uses168's original pure-five operator directly,
and reconstructs the disjoint128 pair partition. The
[certificate](../../certificates/source_norms/moments-survival/pure_three_joint_factorial_comparison.json)
records every cost, maximizing witness, complete numerator and
the exact comparison. Multipart artifacts are read through
certificate_io.read_artifact_bytes.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/moments-survival/pure_three_joint_factorial_comparison.py --check
```

The result remains above403. It establishes a strict complete
comparison improvement, without claiming actual-family sharpness
of the relaxed head bounds.
