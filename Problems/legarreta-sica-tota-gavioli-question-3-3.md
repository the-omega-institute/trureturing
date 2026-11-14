---
slug: legarreta-sica-tota-gavioli-question-3-3
bibkey: legarreta2010normalizers
doi: null
url: https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli.result
---

# Normalizer counts do not bound the centre index

## Problem

Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli, *On the Number of Normalizers and Conjugacy Classes of Normalizers*, International Journal of Algebra 4(24) (2010), 1169–1175, Question 3.3, printed p. 1174:

> Let G be a group satisfying the normalizer condition, and suppose that ω(G) is finite. If s(G) > ω(G), is |G : Z(G)| ω(G)-bounded? Is this true at least for finite p-groups?

This settlement refutes the first question, with a natural-valued bound, as specified in preregistration [#27021](https://github.com/the-omega-institute/trureturing/issues/27021). The second question is separate.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| A bound depending only on $\omega(G)$ | One $B:\mathbb N\to\mathbb N$ precedes the quantification over groups in `claim`. |
| Every group $G$ | $G:\mathrm{Type}$ with a group instance; no finiteness restriction on the claim's group. |
| NC: every proper subgroup is properly contained in its normalizer | The literal quantified subgroup condition is inlined in `claim`; the proof uses Mathlib's normalizer condition. |
| Distinct normalizer subgroups, including $G$ itself | `ModularNormalizerFactors.NormalizerWitness`, with equality of subgroup values. |
| Conjugacy classes of normalizers | `ConjEquivalent`, `normalizerSetoid` and `NormalizerClass` use inner conjugation. |
| $\omega(G)$ finite | Explicit `Finite (NormalizerClass G)`; `omega` is its natural cardinality. |
| $s(G)>\omega(G)$ | Cardinal comparison with `sCard G`; infinite normalizer families are retained. |
| $|G:Z(G)|$ bounded | `centreIndex` is the cardinality of the quotient by the centre, compared with the cardinal cast of $B(\omega(G))$. |
| Refutation | `LegarretaSicaTotaGavioli.result` has literal type $\neg\mathrm{claim}$. |

No source clause is dropped. Natural-valued boundedness is the quantitative interpretation of the source; an arbitrary cardinal-valued bound is a different assertion. Both modules have `generality: G`.

## Motivation

Normalizer count and conjugacy-class count retain different information. A fixed factor supplies a strict gap between them; a coprime factor preserves the gap while increasing the centre index without bound.

## Gap

There is no natural-valued bound on centre index in terms of the finite number of normalizer conjugacy classes under the stated hypotheses. The failure already occurs among finite nilpotent groups, with the class count fixed at eight.

## Route

For every odd prime $p$, let

$$S=\langle a,b\mid a^8=b^2=1,\ b^{-1}ab=a^3\rangle,\qquad P_p=\langle x,y\mid x^{p^2}=y^p=1,\ yxy^{-1}=x^{1+p}\rangle.$$

The actual Lean carriers are semidirect products of multiplicative copies of $\mathbb Z/8$, $\mathbb Z/2$, $\mathbb Z/p^2$ and $\mathbb Z/p$. The fixed subgroup table gives $s(S)=5$, $\omega(S)=4$ and $|S:Z(S)|=8$. The modular factor has $s(P_p)=\omega(P_p)=2$ and centre index $p^2$.

The frozen `SubgroupConjugacyRatio.subgroupProductEquiv` supplies coprime subgroup splitting. It is used in the supporting module's equivalences for normalizers and their conjugacy classes. Consequently $G_p=S\times P_p$ has

$$s(G_p)=10,\qquad\omega(G_p)=8,\qquad |G_p:Z(G_p)|=8p^2.$$

The theorem `result` applies a hypothetical bound at eight and chooses a prime larger than that bound. The resulting natural-number inequality is impossible.

## Falsifier

The family keeps every hypothesis of the first question: the groups are finite nilpotent, satisfy NC, have finite normalizer-class quotient, and have ten normalizers against eight classes. Its centre indices are unbounded. A bound depending on $p$, on group order, or on an additional invariant does not answer the source question.

## Evidence

The settling declaration is `D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli.result`. Its module admission basis is `open-problem-resolution (#27021; Refuted)`. The supporting module's admission basis is `escape-witness`, with the uniform power formula `Modular.pow_elt` feeding its normalizer classification. Supporting finite certificates are consumed proof organization and carry no separate novelty claim.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The eight public supporting theorems have an unfinished escape audit at [#27333](https://github.com/the-omega-institute/trureturing/issues/27333): `counts_prod`, `finite_product_classes`, and `Modular.finiteP`, `Modular.card_p`, `Modular.center_card`, `Modular.s_card`, `Modular.omega_card`, `Modular.finite_classes`. No Reg mirror or validated registration is claimed. Missing evidence is a faithful actual-observation realization, reconstruction, variation, sensitivity and an enrolled readout; parameter-only Unit-state realizations do not establish actual observational dependence.

### Independent finite computation

The experiment is [normalizer-centre-index check at `ce5cb5acb1dc7013292f5e83e3f2f1c0c62ba8f7`](https://github.com/the-omega-institute/trureturing-experiments/tree/ce5cb5acb1dc7013292f5e83e3f2f1c0c62ba8f7/docs/reports/legarreta-sica-tota-gavioli-2010-normalizer-centre-index). Its `check.py` SHA-256 is `f3f27809964ac38b7a4c948aedf3556760974f54be365f863dfdfe55d7b8313a`. The command `python3 check.py` exits 0 and concludes `ALL_CHECKS_OK`. The script was obtained with `git show` from that immutable revision and executed in external scratch storage.

| Tested group | Order | Subgroups | Normalizers | Classes | Centre order | Centre index |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| $S$ | 16 | 15 | 5 | 4 | 2 | 8 |
| $P_3$ | 27 | 10 | 2 | 2 | 3 | 9 |
| $P_5$ | 125 | 14 | 2 | 2 | 5 | 25 |
| $S\times P_3$ | 432 | 150 | 10 | 8 | 6 | 72 |

The product enumeration uses coprime subgroup splitting; for each of its 150 subgroups the script also checks the normalizer directly from generators. Inspection of the same script's enumerated `p3_subs` with `python3 -m pdb check.py` exits 0: there are four order-three subgroups, three noncentral, with normalizer orders $9,9,9$. These computations cover exactly $S,P_3,P_5,S\times P_3$; the uniform family is supplied by the Lean argument, not by extrapolating samples.

## Triage

### What the settlement shows

1. **Proved, kernel-checked mechanism.** The fixed-factor counts are the private proof declarations `Small.s_card` and `Small.omega_card`. The public supporting declarations `Modular.s_card` and `Modular.omega_card` give two for every odd prime. The private `family_s_card`, `family_omega`, `family_center_index` and `family_nc` establish the exact family values and NC used by `result`. The strict gap comes from $S$; the modular factor makes $8p^2$ unbounded.
2. **Proved in prose, finite nilpotent scope.** The factors have orders $16=2^4$ and $p^3$ (`Small.card_S`, `Modular.card_p`), so their product has order $16p^3$. Both finite prime-power factors are nilpotent; their direct product is nilpotent. These are the prime-power and product steps inside `family_nc`. Thus the counterexamples are already finite nilpotent groups. This prose consequence is not an additional public Lean theorem.
3. **Computed, finite samples.** The immutable checker and exit-0 command in Evidence give the four displayed rows exactly: $S,P_3,P_5,S\times P_3$. No other prime or product is part of this computation's tested scope.
4. **Computed, noncentral-line correction.** At $p=3$, inspection of the immutable checker's subgroup enumeration gives four order-three subgroups. The three noncentral ones are $\{(0,0),(0,1),(0,2)\}$, $\{(0,0),(3,1),(6,2)\}$ and $\{(0,0),(3,2),(6,1)\}$; each normalizer has order nine. The claim that there are two noncentral lines is false at this tested prime. The uniform Lean classification uses neither that sentence nor an asserted count of two lines.
5. **Open, finite prime-power question.** The separately posed finite-$p$-group question is not settled: $G_p$ has both prime divisors $2$ and $p$.
6. **Open, neighbouring assertions.** Question 3.2 and the unrestricted cardinal-valued boundedness assertion are outside this settlement. No source theorem depending on the first question is identified in the checked literature; the source's separate proved results are not refuted by this family. Completeness of that literature reading is ASSUMED-UNVERIFIED.
7. **Proved in prose, cardinal boundary.** Every finite quotient has finite cardinality, hence cardinality less than $\aleph_0$. In particular every natural $8p^2$ is less than $\aleph_0$. Therefore the constant cardinal-valued function $B(n)=\aleph_0$ bounds every finite centre index. It is not a natural-valued bound and does not settle the unrestricted assertion on infinite groups.

## ASSUMED-UNVERIFIED

The limited literature screen is recorded in #27021. It includes the 2010 source, the 2006 Cambridge paper, the 2013 Brandl–Sica–Tota abstract and metadata, and the listed normalizer/centralizer follow-ups and survey. No checked item supplies a settlement of the first question. Completeness is ASSUMED-UNVERIFIED: paywalled later full texts remain unread; rate limits and access challenges prevented some citation and review searches. No worldwide priority or exhaustive Lean-ecosystem claim is made.
