# Newton coefficient-to-root bridge: bind-only

Issue: https://github.com/the-omega-institute/trureturing/issues/6377.

Provenance: no local skill; one Codex implementation worker; zero delegated
or independent review seats. All build readings below were obtained by this
worker. Independent semantic review: ASSUMED-UNVERIFIED.

`verdict: bind-only`. The full arbitrary-order bridge is proved using pinned
Mathlib, frozen public theorems, and normalization. The user's hard requirement
#1 therefore stops implementation without a new D5 module or deposit. This
report archives the complete source; it is not a new frozen API.

Base: `c919205ec307d24ecffe742380b5a8823828ba4f`.
Branch: `lane/math/newton-bridge-0908`.
The prescribed fetch/checkout succeeded, and
`git merge-base --is-ancestor c919205ec3 HEAD` returned EXIT 0 before proof work.

## Predecessor and Route

`predecessor_read`: CLAUDE.md and
`docs/reports/hermite-parity-split-0908/report.md` were read in full before
proof work. The archived unfinished source and the two raw log readings were
also inspected.

| Predecessor log | make lean EXIT | Seconds | Maximum RSS (bytes) | Failure |
| --- | --- | --- | --- | --- |
| newton-attempt-2.log | 2 | 13.21 | 3,194,683,392 | simpa did not align opposite-sign endpoints |
| newton-normalization.log | 2 | 15.21 | 3,197,435,904 | ring left the cast/distributivity goal |

The latter goal was exactly:

```text
up(1+r) * E * (-1)^r = E * up(r) * (-1)^r + E * (-1)^r
E = (Finset.univ.val.map roots).esymm (1+r)
```

This attempt retained the Mathlib Newton primitive but addressed that recorded
cause before ring normalization:
`simp only [Nat.cast_add, Nat.cast_one, pow_succ]`.
The recurrence uniqueness and antidiagonal reindexing are now frozen
prerequisites. No new induction or combinatorial construction is needed.
The route was recorded before the probe in the attempt's
`preregistration.md`.

## Bridge and Multiplicity

`bridge_statement`: the literal five statements, including the fully
quantified terminal theorem `real_monic_newton_bridge`, are in the complete
source below.

The field theorem quantifies over any field F, any monic polynomial p,
any degree d equal to its natural degree, any root family whose mapped
multiset equals p.roots, and every r : Nat. It does not assume that an
arbitrary field is algebraically closed; its root-family hypothesis includes
splitting.

The real terminal theorem quantifies over every monic p : Real[X], with no
real-rootedness or positivity hypothesis. It supplies a complex root family
and proves, simultaneously, every recursive Newton sum, every normalized
rootPowerMoment, and equality of the normalized complete matrix entries with
the frozen newtonHankel. All natural degrees and moment orders are included;
there is no upper bound on r. At degree zero Lean's division-by-zero
convention is retained; for positive degrees normalization is division by
the actual root count.

`multiplicity`: `Finset.univ.val.map roots = (p.map Complex.ofRealHom).roots`
is multiset equality, not equality of a deduplicated set. Each root occurs
as often as its algebraic multiplicity. The terminal theorem obtains this
family from frozen `exists_root_enumeration`; the field theorem uses frozen
Vieta including its zero tail. Zeroth moment is d, as required by frozen
recursion uniqueness. No distinct-root assumption occurs.

`type_separation_preserved: true`. FullHermiteMatrix and TruncatedHankelMatrix
remain distinct unchanged structures, each with its own explicit entries
projection. Both directions of an attempted implicit conversion at dimension
3 over Real are rejected by the probe's #check_failure commands. These
expected diagnostics print an internal error placeholder; no delivered
theorem depends on sorryAx. No coercion or unified type name was added.

## Bind-Only Accounting

`bind_only_attempt`: the first route instantiated
`MvPolynomial.psum_eq_mul_esymm_sub_sum`, evaluated it at the roots,
used frozen `newton_inner_antidiagonal_sum`, normalized casts and signs,
and applied frozen `newton_sum_unique` and Vieta. The real transport
instantiates frozen `map_newton_sum`; the normalized result is its real-part
projection. The explicit `sq_nonneg` plus `linarith only` diagnostic is
guarded by fail_if_success: those facts alone do not prove the cross-interface
identity. It is not counted as a proof dependency or escape witness.

| Local log | make lean EXIT | Seconds | Maximum RSS (bytes) | Outcome |
| --- | --- | --- | --- | --- |
| bind-only-make-lean-1.log | 2 | 115.23 | 4,398,448,640 | Field bridge accepted; real/complex type inference and cast under if failed |
| bind-only-make-lean-2.log | 0 | 18.45 | 3,224,190,976 | All five theorems and both type-rejection checks accepted |

The first local failure is archived in `bind-only-attempt-1.lean`.
Its field theorem already had only the standard three axioms; the four
downstream declarations were not accepted and their temporary sorryAx
closures are not delivered. An explicit inner Real type annotation and
case simplification of the coefficient conditional resolved those errors.
The predecessor's Newton endpoint failure recurred zero times.

`escape_witness: none`.
`admission_basis: not-applicable(bind-only-stop)`.
`proof_shape: bind-only`.
`utility: none`.

All five declarations have proof_shape bind-only, escape_witness none, and
the same no-deposit admission basis:

| Declaration | Direct frozen theorem dependencies | Why utility is none |
| --- | --- | --- |
| newton_sum_eq_root_sum | Vieta, uniqueness, antidiagonal reindexing | General equality for arbitrary fields and all orders |
| real_newton_sum_eq_root_sum | map_newton_sum | General scalar transport, not a numerical premise |
| coefficient_moment_eq_rootPowerMoment | None beyond its preceding probe theorem | General real-part projection and normalization |
| coefficient_fullHermite_eq_newtonHankel | None beyond its preceding probe theorem | General equality of explicit matrix entries |
| real_monic_newton_bridge | exists_root_enumeration | General existence from frozen splitting and assembly of the bridge |

None certifies a fixed instance, enumerates bounded candidates, checks a
certificate, or reduces a problem to numerical premises. Utility-specific
consumer, instance, premises, claim and result fields are
`not-applicable(kind=none)`.

Frozen theorem identities (GIDs are relative to
`D5/S3/Constants/Moments/CoefficientNewtonSums.`):

| GID suffix | statement_id |
| --- | --- |
| descending_coeff_eq_root_esymm | sha256:d2cc0062ba6ab0afb1f38d7065a792ba1c3d927370108623cb9f9d45066eb3e0 |
| newton_sum_unique | sha256:d745ba0eff8aab2a5e3320d392a0e275c027a613906a7323d9120cdb182866e4 |
| newton_inner_antidiagonal_sum | sha256:87dc6ddd7999fbb9a7cbd8779bfe3adb4ad48a99e043ad545e5661882e1aee9d |
| map_newton_sum | sha256:4db1f1803abc8d8d37164a4e945686a39d4cca9e239675ffc0b99289f6ab76ec |
| exists_root_enumeration | sha256:558a53a6f8534e6d8b5a6c93f830c1889b21c4e625e915c8af6de64542b2850d |

These were read from frozen event
`98abbda2bcb7f6fd8bd002784480a485d613306472ca3e3ed70378ace72da202`.
The imported module pins are
`sha256:2eaa9526bade862a1a821b87daf78426f82845dc681d9a7dc8f637cb255c66c6`
(CoefficientNewtonSums) and
`sha256:18b030426106ba093ef4ec58fbba090c162f365f32ed6b291aaa0eeba9a358a9`
(NewtonHankelRealRootCriterion). The latter supplies definitions of the target
moment and matrix; its PSD iff is not needed to prove this equality.

## Search and Scope

`question_answered`: issue #6377 L1's coefficient/root-list interface, as
specified in the user's brief and recorded before probing in preregistration.md.

`dominating_theorem_search: not-found-in-searched-scope` for an already
packaged bridge; the exact Mathlib Newton primitive was found and reused.
The initial D5 search and its final repeat used:

```sh
git grep -n -P '(newton_sum_eq_root|newtonSum.*rootPowerMoment|root.*power.*recurs|recurs.*root.*power)' origin/dev -- D5
git grep -n -P '\b(newton_sum_unique|newtonHankel_posSemidef_iff_roots_real)\b' origin/dev -- D5
```

At final dev `45e7b20dd95dd8b2d7b8784392c1814193b80515`, the candidate
search returned one hit, the predecessor's comment describing the unproved
bridge, and the PCRE word-boundary positive control returned seven lines
including both declarations. Initial search at the pinned base had the
same result. The broader constant-theorem search found the frozen recurrence
and real-root criterion, with no packaged bridge among those candidates.

The analogous backfill search found one unrelated Ramanujan receipt; the
criterion control found the absorbed 5040 atom
`1e21ee079033e912ad84630f5a5372b6952f5cee87a1ad985ed6035ac36e7be3`.
No matching bridge anchor was found in that searched scope; no coverage edge
is claimed. Pinned Mathlib v4.33.0 source was read directly, and an online
Loogle query for "psum_eq_mul_esymm_sub_sum" returned exactly one matching
declaration. No exhaustive third-party ecosystem absence is claimed.

`scope_not_claimed`: H0 positive semidefiniteness and the complete Hermite
parity block identity are unproved here. This is not a proof of the remaining
FFC target. The matching-SOS formula (2) is not used. No algebraic VV-transpose
factorization is replaced with a conjugate-transpose Gram factorization.

Text searches for FiniteAdditiveSymbol.additive_splits and
FiniteSymbolCriterion returned zero hits in the final probe and its two D5
imports. The positive control for FiniteSymbolCriterion found its definition
and additive_splits in D5/S3/Zeros/Convolution/FiniteAdditiveSymbol.lean.
The printed quantified statements also have no such assumption.

## Validation and Delivery

`axioms`: all five printed theorem closures are exactly
`[propext, Classical.choice, Quot.sound]`.
`local_make_lean_EXIT: 0`.
The final build reported `Build completed successfully (12585 jobs)`.
Both runs used `/usr/bin/time -l make lean`, with the normal make wrapper;
the cache receipt reported present, project warm, Mathlib warm, no missing
Mathlib oleans. No maxHeartbeats, maxRecDepth, or constants were changed.
The probe used Elab.async false. Trureturing.lean was not changed.

`frozen_output: none (bind-only archive; no new freeze or coverage)`.
`pushed`: this complete report and source are committed and pushed on the
named branch; the exact SHA and remote verification are in result.json.
`pr: null`: the bind-only stop applies before deposit/pr-open; no standalone
mathematical module is admitted. This branch is an archival handoff, not a
merged new library interface. No make lean-report, deposit, or PR CI run is
claimed.
`assumed_unverified`: independent semantic review and external orchestrator
replay are ASSUMED-UNVERIFIED. The general bridge itself is kernel-verified.

All worker-owned artifacts are in:
`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/newton-bridge-0908/attempt-1`.

The standalone source is `newton-bridge-bind-only.lean`, SHA-256
`419c4ea96cd6fd09470b0dbd890f7e3de4f6d07337a5f24667c44ab1294bd7f0`.
The following fenced source is byte-for-byte identical. It was temporarily
built at `D5/S3/Constants/Moments/NewtonBridgeBindProbe.lean` and removed from
D5 after success, as required by the bind-only stopping rule.

## Complete Source

```lean
/- Temporary bind-only probe for issue #6377, not a deposit candidate.
   utility: none
   General algebraic equalities only; no certified-instance, bounded-enumeration,
   checker, or numeric-reduction. See the attempt preregistration. -/

import D5.S3.Constants.Moments.CoefficientNewtonSums
import D5.S3.Constants.NewtonHankelRealRootCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

noncomputable section
open Polynomial
open scoped BigOperators
open D5.S3.Constants.Moments.CoefficientNewtonSums
open D5.S3.Constants.NewtonHankelRealRootCriterion

namespace NewtonBridgeBindProbe

theorem newton_sum_eq_root_sum {F : Type*} [Field F]
    {d : Nat} (p : F[X]) (hp : p.Monic) (hd : p.natDegree = d)
    (roots : Fin d -> F) (hroots : Finset.univ.val.map roots = p.roots) (r : Nat) :
    newtonSum d (descendingCoeff d p) r = ∑ i, roots i ^ r := by
  classical
  rw [descending_coeff_eq_root_esymm p hp hd roots hroots]
  apply newton_sum_unique d (rootElementaryCoeff roots) (fun n => ∑ i, roots i ^ n)
  · simp
  · intro n
    have h := congrArg (MvPolynomial.aeval roots)
      (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin d) F (n + 1) (by omega))
    simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
      MvPolynomial.aeval_esymm_eq_multiset_esymm] at h
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X] at h
    rw [newton_inner_antidiagonal_sum n (fun a b => (-1 : F)^a *
      (Finset.univ.val.map roots).esymm a * ∑ i, roots i ^ b)] at h
    rw [h]
    simp only [rootElementaryCoeff]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring

theorem real_newton_sum_eq_root_sum {d : Nat} (p : Real[X])
    (hp : p.Monic) (hd : p.natDegree = d) (roots : Fin d -> Complex)
    (hroots : Finset.univ.val.map roots = (p.map Complex.ofRealHom).roots) (r : Nat) :
    ((newtonSum d (descendingCoeff d p) r : Real) : Complex) = ∑ i, roots i ^ r := by
  have hcoeff : (fun k => Complex.ofRealHom (descendingCoeff d p k)) =
      descendingCoeff d (p.map Complex.ofRealHom) := by
    funext k
    by_cases hk : k ≤ d <;> simp [descendingCoeff, hk]
  change Complex.ofRealHom (newtonSum d (descendingCoeff d p) r) = _
  rw [map_newton_sum, hcoeff]
  exact newton_sum_eq_root_sum (p.map Complex.ofRealHom) (hp.map _)
    (by simpa using hd) roots hroots r

theorem coefficient_moment_eq_rootPowerMoment {d : Nat} (p : Real[X])
    (hp : p.Monic) (hd : p.natDegree = d) (roots : Fin d -> Complex)
    (hroots : Finset.univ.val.map roots = (p.map Complex.ofRealHom).roots) (r : Nat) :
    newtonSum d (descendingCoeff d p) r / d = rootPowerMoment roots r := by
  fail_if_success solve
    | have hs := sq_nonneg (newtonSum d (descendingCoeff d p) r)
      linarith only [hs]
  have h := congrArg Complex.re (real_newton_sum_eq_root_sum p hp hd roots hroots r)
  simp only [Complex.ofReal_re] at h
  exact congrArg (fun x : Real => x / d) h

theorem coefficient_fullHermite_eq_newtonHankel {d : Nat} (p : Real[X])
    (hp : p.Monic) (hd : p.natDegree = d) (roots : Fin d -> Complex)
    (hroots : Finset.univ.val.map roots = (p.map Complex.ofRealHom).roots) :
    (fullHermiteFromMoments d (fun r => newtonSum d (descendingCoeff d p) r / d)).entries =
      newtonHankel roots := by
  funext i j
  exact coefficient_moment_eq_rootPowerMoment p hp hd roots hroots (i.val + j.val)

theorem real_monic_newton_bridge (p : Real[X]) (hp : p.Monic) :
    ∃ roots : Fin p.natDegree -> Complex,
      Finset.univ.val.map roots = (p.map Complex.ofRealHom).roots ∧
      (∀ r : Nat, ((newtonSum p.natDegree (descendingCoeff p.natDegree p) r : Real) : Complex) =
        ∑ i, roots i ^ r) ∧
      (∀ r : Nat, newtonSum p.natDegree (descendingCoeff p.natDegree p) r / p.natDegree =
        rootPowerMoment roots r) ∧
      (fullHermiteFromMoments p.natDegree
        (fun r => newtonSum p.natDegree (descendingCoeff p.natDegree p) r / p.natDegree)).entries =
        newtonHankel roots := by
  obtain ⟨roots, hroots⟩ := exists_root_enumeration (p.map Complex.ofRealHom)
    (d := p.natDegree) (by simp)
  exact ⟨roots, hroots, real_newton_sum_eq_root_sum p hp rfl roots hroots,
    coefficient_moment_eq_rootPowerMoment p hp rfl roots hroots,
    coefficient_fullHermite_eq_newtonHankel p hp rfl roots hroots⟩

#check_failure (fun x : FullHermiteMatrix 3 Real =>
  (show TruncatedHankelMatrix 3 Real from x))
#check_failure (fun x : TruncatedHankelMatrix 3 Real =>
  (show FullHermiteMatrix 3 Real from x))

#print axioms newton_sum_eq_root_sum
#print axioms real_newton_sum_eq_root_sum
#print axioms coefficient_moment_eq_rootPowerMoment
#print axioms coefficient_fullHermite_eq_newtonHankel
#print axioms real_monic_newton_bridge

end NewtonBridgeBindProbe
```
