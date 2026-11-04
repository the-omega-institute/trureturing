---
bibkey: simon1986compact
authors: Jacques Simon
year: 1986
title: Compact sets in the space Lp(0,T;B)
doi: 10.1007/BF01762360
url: https://doi.org/10.1007/BF01762360
claim: Theorem 1 characterizes finite-exponent Lp compactness by interval integrals and internal translations; Section 8 Theorem 5 gives intermediate-space compactness from a compact spatial embedding and weaker-space translations, including continuous compactness at infinity.
strata_touched: []
license: citation-only
triage: anchor
---

# Interval-integral compactness and internal translations

Simon, Annali di Matematica Pura ed Applicata 146, 65–96, states an
if-and-only-if compactness criterion for Banach-valued functions. Section 3,
Theorem 1, printed page 71, assumes compactness of the integral sets only
for strictly interior subintervals, 0 < a < b < T. The finite-exponent
range includes p = 1. The sufficiency proof on pages 72–74 uses averaging
and time reversal to handle both interval ends. Remark 3.4 explains why
an interior averaging argument alone does not settle the whole interval.

The sufficiency specialization with observations on all 0 ≤ a < b ≤ T
has stronger hypotheses than Simon's original theorem. It is not the full
original equivalence. Right-closed instead of open intervals represent
the same Lebesgue almost-everywhere classes.

The same Theorem 1 also has a compactness conclusion in C(0,T;B) for
p = infinity. Section 1 defines this continuous-function space on the
closed interval [0,T], while L-infinity is a space of almost-everywhere
classes. The proof uses right means and opposite time directions. The
theorem does not separately state an arbitrary-family continuous lifting
with a common modulus and uniqueness in the absence of the integral
compactness premise. The local-window consistency and representative
construction in `IntervalLInfinityRepresentative` are derived arguments,
without an originality claim or exact separate literature attestation.

The equal-mesh estimate bounds the whole-interval power error by
2 divided by the cell width times the integral, over positive shifts
up to that width, of the internal translation power error. Its cells
include the first and last portions of the original interval. This
particular restricted-domain assembly is a derived proof route; the
compactness criterion itself is literature-attested. No optimal-constant
or mathematical originality claim is made.

The selected analytic source supplier is TauCetiProject/TauCeti revision
`ef2b35da80dbe9f123fd200fcf160a036fe69813`,
`TauCeti/MeasureTheory/Integral/Average.lean` (SHA256
`cd2ede6573aaf1c5c80fd56e048f70859a5fb94c97b9a944e33b292374af2c67`)
and `TauCeti/MeasureTheory/Function/Lp/LIntegralRpow.lean` (SHA256
`6954ce124fb51025e4afe01c0992d2afedfb83740ee5f2835471f09f6f9c4c77`).
Its Hölder and average-norm proofs are reused with original attribution.
The full Apache-2.0 license is retained at
`docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`.
The source pin uses Lean 4.36.0-rc1 and a different Mathlib revision, so
these selected leaves are ports rather than a direct package dependency.
Each port is replaced by a direct application when this repository's
adopted Mathlib revision contains an equivalent declaration.

The total-boundedness transfer proof is reused from
uda-lab/leray-hopf revision `e704400f2fb2f26b2ee7f4372c3e1ecbbc82f3dc`,
`LerayHopf/Bochner/StepFunctionCompactness.lean`, SHA256
`6dcaf556f129c58d31f9ff6ba442da592723c6cbbfe6de54513951f21916f26f`.
The selected theorem is general over pseudometric spaces; its original
p = 2 mesh-compactness neighbors are not used as an all-p result.
The original Apache-2.0 license is retained at
`docs/reports/licenses/leray-hopf-interval-LICENSE.txt`.
The source pins Lean 4.31.0-rc2 and Mathlib
`15a89b2468bc01f1a6230d6e49ef5efc5286e502`; the selected proof is a port,
not a package dependency. Replace the port when this repository's adopted
Mathlib revision supplies the equivalent transfer theorem.

## Verified locator

DOI: https://doi.org/10.1007/BF01762360.
Primary publication: https://link.springer.com/article/10.1007/BF01762360.
Theorem 1 is in Section 3, printed page 71; the sufficiency proof and
boundary discussion are on printed pages 72–74, including Remark 3.4.
The consulted original PDF has SHA256
`86b81eb6be3be81afd97fd43f185f63929f552fdaaaf13ee7a9d89f6483a3db3`.
The article is cited and paraphrased; no publisher text or PDF is redistributed.

Selected Lean sources:
https://github.com/TauCetiProject/TauCeti/blob/ef2b35da80dbe9f123fd200fcf160a036fe69813/TauCeti/MeasureTheory/Integral/Average.lean
and
https://github.com/TauCetiProject/TauCeti/blob/ef2b35da80dbe9f123fd200fcf160a036fe69813/TauCeti/MeasureTheory/Function/Lp/LIntegralRpow.lean.

Uniform-approximation transfer source:
https://github.com/uda-lab/leray-hopf/blob/e704400f2fb2f26b2ee7f4372c3e1ecbbc82f3dc/LerayHopf/Bochner/StepFunctionCompactness.lean,
`LerayHopf.totallyBounded_of_uniform_approx'`.

## Section 8: compactness in an intermediate Banach space

Section 8, Theorem 5, printed page 84, assumes Banach spaces
X compactly embedded in B, with B continuously embedded in Y. A family
bounded in Lp(0,T;X), for 1 <= p <= infinity, whose positive internal time
translations tend uniformly to zero in Lp(0,T-h;Y), is relatively compact
in Lp(0,T;B), and also in C([0,T];B) when p = infinity. The closed-interval
interpretation of Simon's C(0,T;B) is the convention in Section 1. The
spatial estimate is Lemma 8, equation (8.4), on pages 84–85, credited there
to J. L. Lions. These statements do not require reflexivity.

The corresponding application uses arbitrary real Banach X, B and Y in
independent universes, continuous injective linear maps i:X->B and j:B->Y
with i compact, T>0, and any possibly empty norm-bounded set S of actual
X-valued Lp classes. Its sole time premise says that, for every epsilon>0,
some delta>0 makes the Lp seminorm of
t mapped to j(i(f(t+h)-f(t))) on Ioc(0,T-h) less than epsilon, simultaneously
for f in S and 0<h<min(delta,T). Right-closed and open intervals give the
same Lebesgue almost-everywhere classes. The conclusion concerns compact
closure of the actual image under i.compLpL. At infinity, a map from the
original subtype S to C([0,T];B) additionally assigns the unique continuous
almost-everywhere representative of i(f), and its range has compact
closure for the uniform norm.

The general Ehrling Lean proof used as external supply is authored by
Nickrobbins95 in prove2me/formalpedia, immutable revision
`e82fff3d729d46e3ddaf6b51f4bb376b16554bae`,
[`envs/0df444a/Solutions/Sol_HunterPDE_Parabolic_ehrling.lean`](https://github.com/prove2me/formalpedia/blob/e82fff3d729d46e3ddaf6b51f4bb376b16554bae/envs/0df444a/Solutions/Sol_HunterPDE_Parabolic_ehrling.lean),
Apache-2.0, SHA256
`f8fa04fd3e3b739baee4f88e36e7af15f64423f95fa77d846cc8111865419ac9`.
It supplies, for each a>0, a real C_a with
norm(i(x)) <= a*norm(x) + C_a*norm(j(i(x))). Independent universes are
received through the faithful external telescope with the proof body
unchanged. This is external proof supply, not new mathematical content;
no external proof code or port module is retained for this application.

Choose M>0 bounding the Lp norms of S and put c=max(C_a,0). The shifted
and unshifted restrictions each have X-valued seminorm at most M, so the
internal B- and Y-valued translation seminorms satisfy
D_B <= 2*a*M + c*D_Y. Taking a small and then using the uniform Y
translation premise gives uniform B translation control, also at
p=infinity. Positive translation maps Ioc(0,T-h) measure-preservingly
onto Ioc(h,T). Restricting and transporting the almost-everywhere
compLpL identity is essential: it identifies the internal differences of
actual image classes without assuming pointwise equality of chosen
representatives.

For finite p, Bochner integrals of S on each 0<=a<b<=T form a bounded
set in X: their norms are at most M*(b-a)^(1-1/p). Compactness of i gives
compact closures of their B images. Commutation of i with the Bochner
integral and the restricted compLpL identity turn these into the
interval-integral sets required by
`IntervalLpCompactness.isCompact_closure_of_integrals_translations`,
applied with E=B. Thus that endpoint's stronger interval-integral premise
is derived from the spatial hypothesis; it is not an added assumption
of the complete Section 8 application.

At infinity,
`IntervalLInfinityRepresentative.exists_continuous_representatives`
provides the representative map, uniqueness and a common modulus for
the B-valued image family. Compact closure requires an additional
spatial step. The compact set K=closure(i '' closedBall(0,M)) contains
every representative value. Indeed, the almost-everywhere X norm bound
puts the values in K almost everywhere; the continuous distance to K
vanishes almost everywhere and hence throughout the closed interval,
using the equivalence of Ioc and Icc for Lebesgue almost-everywhere
equality and equality of continuous functions on a nondegenerate closed
interval. This includes both endpoints and assumes no pointwise X lift
of a B-valued representative. Ascoli gives uniform-norm compact closure
of the representative family. Clamped extension and the continuous map
to actual L-infinity identify its image with the original compLpL image;
containment in the compact image of the representative closure gives
compact closure there too.

The owning `IntervalLpCompactness` Blueprint exposition gives this
derived application of the two existing D5 endpoints. Their private mesh,
averaging, Fubini, almost-everywhere and endpoint constructions, the
Tau Ceti and leray-hopf ports described above, and pinned Mathlib's
seminorm, Bochner, measure-preservation, compact-operator, infDist,
closed-interval equality, Ascoli, isometry and continuous-to-Lp results
receive full credit. No newly retained Lean declaration, greater
mathematical generality or literature originality is claimed. Neither
endpoint alone states the complete application. It adds no separability,
finite-dimensionality, time derivative, extra pointwise modulus,
prechosen continuous representative, endpoint value, boundary-tail,
whole-line translation or family-nonemptiness hypothesis.
