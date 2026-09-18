/- GID: D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.claim; result=D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.result; claim=D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.claim
   digest: Six even four-element edges on eight vertices give inverse coefficient -14. -/

/- proof_shape: content
   escape_witness: the finite 256-subset certificate recurrence and its squarefree inverse-coefficient induction
   admission_basis: open-problem-resolution (issue #8613)
   Direct frozen dependencies: none.
-/

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The signed independence series includes the empty independent set. Its inverse is
Mathlib's multivariate formal power series inverse over the rationals.

The six four-element edges below have an inverse coefficient of -14 at the
product of all eight variables. The finite integer recurrence is transferred to
the actual inverse by squarefree antidiagonal reindexing and strong induction.
-/

open scoped BigOperators
open MvPowerSeries

namespace D5.S0.Certificates.Hypergraphs.EvenInversePositivityRefutation

attribute [local instance 2000] Finset.decidableDforallFinset

set_option maxRecDepth 8192
set_option maxHeartbeats 0

noncomputable def indicator {n : ℕ} (S : Finset (Fin n)) : Fin n →₀ ℕ :=
  Finsupp.onFinset S (fun v => if v ∈ S then 1 else 0) (by simp)

noncomputable def signedIndependence {n : ℕ} (E : Finset (Finset (Fin n))) :
    MvPowerSeries (Fin n) ℚ :=
  ∑ S ∈ Finset.univ.powerset.filter (fun S => ∀ e ∈ E, ¬e ⊆ S),
    monomial (indicator S) ((-1 : ℚ) ^ S.card)

def SourceSimple {n : ℕ} (E : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ E, 2 ≤ e.card) ∧ (∀ e ∈ E, ∀ f ∈ E, e ⊆ f → e = f)

def claim : Prop :=
  ∀ n : ℕ, 0 < n → ∀ E : Finset (Finset (Fin n)), SourceSimple E →
    ((∀ m : Fin n →₀ ℕ, 0 ≤ coeff m (signedIndependence E)⁻¹) ↔
      ∀ e ∈ E, Even e.card)

private def candidate : Finset (Finset (Fin 8)) :=
  {{6,7,0,1}, {6,7,1,2}, {6,7,2,0}, {6,7,3,4}, {6,7,4,5}, {6,7,5,3}}

private def d (i : ℕ) : ℤ :=
  if i < 2 then 1 else if i = 2 then 0 else -4

private def cert (T : Finset (Fin 8)) : ℤ :=
  if 6 ∈ T ∧ 7 ∈ T then
    2 - d (T ∩ {0,1,2}).card * d (T ∩ {3,4,5}).card
  else 1

private def fromBits (a b c d e f g h : Bool) : Finset (Fin 8) :=
  (if a then {0} else ∅) ∪ (if b then {1} else ∅) ∪
  (if c then {2} else ∅) ∪ (if d then {3} else ∅) ∪
  (if e then {4} else ∅) ∪ (if f then {5} else ∅) ∪
  (if g then {6} else ∅) ∪ (if h then {7} else ∅)

theorem result : Not claim := by
  have indicator_apply {n} (S : Finset (Fin n)) (v : Fin n) :
      indicator S v = if v ∈ S then 1 else 0 := rfl

  have indicator_inj {n} {S T : Finset (Fin n)} :
      indicator S = indicator T ↔ S = T := by
    constructor
    · intro h
      ext v
      have hv := DFunLike.congr_fun h v
      simp only [indicator_apply] at hv
      by_cases hs : v ∈ S <;> by_cases ht : v ∈ T <;> simp_all
    · rintro rfl; rfl

  have indicator_empty {n} : indicator (∅ : Finset (Fin n)) = 0 := by
    ext v
    simp [indicator_apply]

  have indicator_le {n} {S T : Finset (Fin n)} :
      indicator S ≤ indicator T ↔ S ⊆ T := by
    constructor
    · intro h v hv
      have := h v
      by_contra ht
      simp [indicator_apply, hv, ht] at this
    · intro h v
      simp only [indicator_apply]
      split_ifs with hs ht
      all_goals simp_all
      exact ht (h hs)

  have indicator_lt {n} {S T : Finset (Fin n)} :
      indicator S < indicator T ↔ S ⊂ T := by
    rw [lt_iff_le_not_ge, indicator_le, indicator_le]
    exact Iff.rfl

  have indicator_of_le {n} {m : Fin n →₀ ℕ} {T : Finset (Fin n)}
      (hm : m ≤ indicator T) : indicator m.support = m := by
    ext v
    have hv := hm v
    simp only [indicator_apply] at hv ⊢
    simp only [Finsupp.mem_support_iff]
    split_ifs <;> split_ifs at hv <;> omega

  have indicator_complement {n} {U T : Finset (Fin n)} (h : U ⊆ T) :
      indicator U + indicator (T \ U) = indicator T := by
    ext v
    simp only [Finsupp.add_apply, indicator_apply, Finset.mem_sdiff]
    by_cases hu : v ∈ U <;> by_cases ht : v ∈ T <;> simp_all
    exact ht (h hu)

  have sum_antidiagonal_indicator {n} (T : Finset (Fin n))
      (f : (Fin n →₀ ℕ) × (Fin n →₀ ℕ) → ℚ) :
      ∑ p ∈ Finset.antidiagonal (indicator T), f p =
        ∑ U ∈ T.powerset, f (indicator U, indicator (T \ U)) := by
    symm
    apply Finset.sum_bij (fun U _ => (indicator U, indicator (T \ U)))
    · intro U hU
      rw [Finset.mem_antidiagonal]
      exact indicator_complement (Finset.mem_powerset.mp hU)
    · intro U hU V hV h
      exact indicator_inj.mp (congrArg Prod.fst h)
    · intro p hp
      have heq : p.1 + p.2 = indicator T := Finset.mem_antidiagonal.mp hp
      have hle : p.1 ≤ indicator T := by rw [← heq]; exact le_self_add
      have hrepr := indicator_of_le hle
      have hsub : p.1.support ⊆ T := indicator_le.mp (hrepr.trans_le hle)
      refine ⟨p.1.support, Finset.mem_powerset.mpr hsub, ?_⟩
      apply Prod.ext hrepr
      apply add_left_cancel (a := p.1)
      change p.1 + indicator (T \ p.1.support) = p.1 + p.2
      calc
        p.1 + indicator (T \ p.1.support) =
            indicator p.1.support + indicator (T \ p.1.support) := by rw [hrepr]
        _ = indicator T := indicator_complement hsub
        _ = p.1 + p.2 := heq.symm
    · intros; rfl

  have signed_coeff {n} (E : Finset (Finset (Fin n)))
      (T : Finset (Fin n)) :
      coeff (indicator T) (signedIndependence E) =
        if ∀ e ∈ E, ¬e ⊆ T then (-1 : ℚ) ^ T.card else 0 := by
    classical
    simp only [signedIndependence, map_sum, coeff_monomial, indicator_inj]
    rw [Finset.sum_ite_eq]
    simp

  have signed_constant {n} (E : Finset (Finset (Fin n)))
      (hE : SourceSimple E) : constantCoeff (signedIndependence E) = 1 := by
    have hempty : ∀ e ∈ E, ¬e ⊆ (∅ : Finset (Fin n)) := by
      intro e he h
      have hc := hE.1 e he
      have : e = ∅ := Finset.subset_empty.mp h
      simp [this] at hc
    rw [← coeff_zero_eq_constantCoeff_apply, ← indicator_empty, signed_coeff,
      if_pos hempty]
    simp

  have inverse_squarefree_certificate {n}
      (E : Finset (Finset (Fin n))) (hE : SourceSimple E)
      (c : Finset (Fin n) → ℚ)
      (hc : ∀ T, c T = if T = ∅ then 1 else
        - ∑ U ∈ T.powerset, if U = ∅ then 0 else
          (if ∀ e ∈ E, ¬e ⊆ U then (-1 : ℚ) ^ U.card else 0) * c (T \ U))
      (T : Finset (Fin n)) :
      coeff (indicator T) (signedIndependence E)⁻¹ = c T := by
    classical
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      rw [coeff_inv, signed_constant E hE, inv_one, hc T]
      by_cases hT : T = ∅
      · subst T
        simp [indicator_empty]
      · have hi : indicator T ≠ 0 := by
          rw [← indicator_empty, ne_eq, indicator_inj]
          exact hT
        rw [if_neg hi, if_neg hT]
        simp only [neg_mul, one_mul]
        rw [sum_antidiagonal_indicator]
        congr 1
        apply Finset.sum_congr rfl
        intro U hU
        dsimp only
        by_cases hU0 : U = ∅
        · subst U
          simp
        · have hstrict : T \ U ⊂ T :=
            Finset.sdiff_ssubset (Finset.mem_powerset.mp hU) (Finset.nonempty_iff_ne_empty.mpr hU0)
          rw [if_pos (indicator_lt.mpr hstrict), if_neg hU0, signed_coeff, ih _ hstrict]


  have hcert : ∀ T : Finset (Fin 8),
      cert T = if T = ∅ then 1 else
        - ∑ U ∈ T.powerset,
          if U = ∅ then 0 else
            (if ∀ e ∈ candidate, ¬e ⊆ U then (-1 : ℤ) ^ U.card else 0) *
              cert (T \ U) := by
    have hb : ∀ a b c d e f g h : Bool,
        let T := fromBits a b c d e f g h
        cert T = if T = ∅ then 1 else
          - ∑ U ∈ T.powerset,
            if U = ∅ then 0 else
              (if ∀ e ∈ candidate, ¬e ⊆ U then (-1 : ℤ) ^ U.card else 0) *
                cert (T \ U) := by
      intro a b c d e f g h
      cases a <;> cases b <;> cases c <;> cases d <;>
        cases e <;> cases f <;> cases g <;> cases h <;> decide +kernel
    intro T
    have ht : fromBits (decide (0 ∈ T)) (decide (1 ∈ T)) (decide (2 ∈ T))
        (decide (3 ∈ T)) (decide (4 ∈ T)) (decide (5 ∈ T))
        (decide (6 ∈ T)) (decide (7 ∈ T)) = T := by
      have mem_bit (v w : Fin 8) (b : Bool) :
          v ∈ (if b then ({w} : Finset (Fin 8)) else ∅) ↔ b = true ∧ v = w := by
        cases b <;> simp
      ext v
      fin_cases v <;> simp only [fromBits, Finset.mem_union, mem_bit] <;> simp
    simpa only [ht] using hb (decide (0 ∈ T)) (decide (1 ∈ T)) (decide (2 ∈ T))
      (decide (3 ∈ T)) (decide (4 ∈ T)) (decide (5 ∈ T))
      (decide (6 ∈ T)) (decide (7 ∈ T))
  have hrecQ : ∀ T : Finset (Fin 8),
      (cert T : ℚ) = if T = ∅ then 1 else
        - ∑ U ∈ T.powerset,
          if U = ∅ then 0 else
            (if ∀ e ∈ candidate, ¬e ⊆ U then (-1 : ℚ) ^ U.card else 0) *
              (cert (T \ U) : ℚ) := by
    intro T
    exact_mod_cast hcert T
  have hs : SourceSimple candidate := by unfold SourceSimple; decide
  have he : ∀ e ∈ candidate, Even e.card := by decide
  have hvalue : cert Finset.univ = -14 := by decide
  have hcoeff : coeff (indicator Finset.univ) (signedIndependence candidate)⁻¹ = -14 := by
    rw [inverse_squarefree_certificate candidate hs (fun T => (cert T : ℚ)) hrecQ,
      hvalue]
    norm_num
  intro hc
  have hpos := (hc 8 (by decide) candidate hs).mpr he (indicator Finset.univ)
  rw [hcoeff] at hpos
  norm_num at hpos

end D5.S0.Certificates.Hypergraphs.EvenInversePositivityRefutation
