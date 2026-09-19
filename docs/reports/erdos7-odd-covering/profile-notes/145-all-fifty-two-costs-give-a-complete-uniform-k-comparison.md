[Index](../marked_head_profile.md) · [Face comparison](113-quadratic-hinges-and-the-factorial-tail-share-one-head.md) · [Complete denominator](139-a-complete-ap-denominator-stays-positive-on-the-k-neighborhood.md) · [Globalization boundary](144-a-small-local-comparison-leaves-the-outer-escape-bottleneck.md)

# All fifty-two costs give a complete uniform K comparison

For every actual source in either K orientation satisfying

    qK>=1-sigma, sigma<=1/10000,
    rho<=1/100000, r<=1/520,                         (UC1)

the original complete comparison obeys

    C0+N/E <=460.46808262656754... <461.              (UC2)

Here N and E are the original numerator and AP11/AP13 survival
denominator. All52 original costs, the signed actual mass, the full
LCM square complement and all exponent/count tails remain included.
The first-beta distribution varies over its entire feasible domain;
different original tests retain independent residues. The exact
rational value in(UC2), not its displayed decimal, is stored in the
[certificate](../certificates/source_norms/uniform_complete_k_comparison.json).

This is a source-uniform neighborhood theorem, extending113's exact
face comparison459.13982857475636.... It is still above403. The
neighborhood does not contain144's middle-region bottleneck, so this
result alone does not improve118's global K or solve unrestricted
Erdos #7.

## 1. The original inventory is a disjoint partition

Let w_i>0 be113's original outside weights and C_i the corresponding
independently labelled complete costs. The following partition uses
only proved uniform continuations of the adopted controllers:

| Source | Number of original costs | Treatment |
| --- | ---: | --- |
|137|11|mean and positive hinges in one original head|
|140|10|nine quadratic head bounds and the retained raw81 second row|
|141|28|27 exact two-hinge expansions and the affine first moment|
|142|2|the two adopted vector controllers, indices0 and16|
|143|1|the original raw81 first row, index46|

The indices are pairwise disjoint and their union is0,...,51. Every
weight and zero-radius value matches113 exactly. In particular,
indices46 and47 keep their actual raw controllers; an unadopted
positive expansion does not replace either reference value.

Each cited theorem is uniform for its own original test on(UC1).
Consequently its inequality holds simultaneously with the other51
inequalities for the same actual source and measure. This does not
assert that the52 relaxed maximizers can be realized simultaneously,
and does not identify residues between costs. Summing positive upper
bounds is valid without either assertion.

The two common-allocation portfolios137 and140 have zero sharing
gain at these parameters: their computed common-source bounds equal
the sums of the individual adopted uniform bounds. The consumer
checks those equalities before using the original per-index inventory.
No minimum with an untransported face-only bound is taken.

## 2. The signed mass has the opposite substitution direction

Write the original complete numerator as

    N=cS*S+sum_(i=0..51)w_i*C_i+cQ*Q,
    Q=integral_mu A^2,                              (UC3)

where

    cS=-4518624276643341182459/59927719166078690646720,
    cQ=2061512697931813067/15514910048663625600.

Thus cS<0<cQ. On(UC1),137 supplies

    Slo=53/360-101*delta/180 <= S
        <=53/360+5*delta/9+rho0=Shi,
    delta=1/10000, rho0=1/100000.                    (UC4)

The lower bound is a conservative consequence of the sharper
S>=53/360-101*delta/180+rho; no unknown actual rho is inserted in
the negative mass term. Therefore cS*S<=cS*Slo. The positive affine
mass inside141 uses Shi separately, with its correct positive sign.
These two substitutions remain valid for the same actual S.

For Q use143's complete square bound

    Qbar=67565983358140295359/13499100000000000000.

The unit-unit mass in that square is already included in143. It is
not removed or reinserted when forming(UC3). All old/seven ordered
pairs have their original LCM multiplicities and complete tails.
Combining the52 bounds and(UC4) gives

    N<=Nbar=34.97213489991657... .                   (UC5)

The exact numerator is reconstructed from the original weights,
not rounded component decimals. At zero radius the same expression
returns113's Nbar_face=34.92830853753444... exactly.

## 3. The full denominator stays positive

Profile139 proves, on the same source rectangle,

    E>=dbar
      =91885945376775823449884846527429
       /1153099411660494594450000000000000
      =0.07968605694148916... >0.                  (UC6)

The consumer checks its original formula

    dbar=(1-1/(7*87846))*Slo
         -shared_finite_penalty-H1bar/(7*7986),     (UC7)

where shared_finite_penalty comprises all four AP11 original blocks
and the independent AP13 fourth hinge. The remaining AP11 count tail
has already been summed in(UC7), including its constant term. Its
mass coefficient was combined before applying Slo. Thus there is no
unbounded remainder requiring a later finite-height assumption.

Since Nbar>0 and E>=dbar>0,

    C0+N/E <= C0+Nbar/E <= C0+Nbar/dbar.             (UC8)

With113's unchanged C0, this is(UC2). Even if an actual N were
negative, the first inequality still holds; positivity is needed
only for the bound Nbar in the second inequality.

At zero radius, the complete denominator returns

    dbar_face=50511415637/632754738000.

Together with the recovered numerator, it gives113's exact complete
comparison. This checks the whole adopted inventory, not merely a
few sampled cost rows.

## 4. Exact loss attribution and scope

The increase over the face comparison can be separated without
introducing a second source measure:

    Nbar/dbar-Nbar_face/dbar_face
      =(Nbar-Nbar_face)/dbar
       +Nbar_face*(dbar_face-dbar)/(dbar*dbar_face). (UC9)

Every numerator change is also recorded separately: the five cost
groups, the signed mass and the square complement. Their exact sum
is Nbar-Nbar_face; all seven changes are nonnegative. This provides
a quantitative guide for expanding the source radius, while keeping
the same comparison and weights.

The assertion is conditional on the original actual-source model
and(UC1), with all its arbitrary residue and height choices. No
additional uniformity outside that domain follows by continuity or
by the numerical room below461. Profile144 gives the precise case
split required for joining it to a global estimate. In particular,
the large local margin cannot pay for another configuration in the
middle region.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/uniform_complete_k_comparison.py --check
```

The consumer verifies logical certificate hashes through the split
artifact reader, inherited input identities, the full52-index
partition, original coefficients, both mass signs, positive division
and exact face recovery. The ordinary proofs in137 and139--143
supply the continuous-source and arbitrary-height inequalities;
aggregation does not re-prove them. This is ordinary mathematics
with exact rational verification, without a Lean or required-CI claim.
