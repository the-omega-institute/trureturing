/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySuffix
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySuffix
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Lp.lpSpace]
   utility: none
   digest: Strict suffix restrictions and disjoint energy for the actual biased boundary trace. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace
import Mathlib.Data.List.Infix

/-! Strict descendant coordinates and their common infinite boundary traces. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffix

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (Edge H P)
open FiniteSourceMass (a)
open BiasedBoundaryTrace (G J indicator boundary_trace_hardy)
open scoped BigOperators ENNReal

/-- Appending a nonempty suffix selects a strict descendant edge. -/
def descendant (p : Address) (u : Edge) : Edge :=
  ⟨p ++ u.val, by
    intro he
    have hl := congrArg List.length he
    have hu := List.length_pos_of_ne_nil u.property
    simp only [List.length_append, List.length_nil] at hl
    omega⟩

private theorem descendant_injective (p : Address) : Function.Injective (descendant p) := by
  intro u v h
  apply Subtype.ext
  exact List.append_cancel_left (congrArg Subtype.val h)

/-- Restriction to nonempty suffix coordinates, still in the original edge ell2. -/
def suffixLinear (p : Address) : H →ₗ[ℝ] H where
  toFun z := ⟨fun u => z (descendant p u), memℓp_gen
    (((lp.memℓp z).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).comp_injective
      (descendant_injective p))⟩
  map_add' z w := by ext u; rfl
  map_smul' c z := by ext u; rfl

private theorem norm_sq (z : H) : ‖z‖^2 = ∑' u : Edge, ‖z u‖^2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) z

private theorem suffix_norm_sq (p : Address) (z : H) :
    ‖suffixLinear p z‖^2 ≤ ‖z‖^2 := by
  have h := tsum_comp_le_tsum_of_inj
    ((lp.memℓp z).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal))
    (fun u => Real.rpow_nonneg (norm_nonneg (z u)) _) (descendant_injective p)
  rw [norm_sq, norm_sq]
  simpa only [Function.comp_def, ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- The bounded strict-suffix coordinate map. -/
def S (p : Address) : H →L[ℝ] H :=
  (suffixLinear p).mkContinuous 1 fun z => by
    simpa only [one_mul] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (suffix_norm_sq p z)

/-- The original infinite boundary trace applied to strict suffix increments. -/
def suffixTrace (p : Address) : H →L[ℝ] G := J.comp (S p)

/-- No two distinct addresses in the family are comparable prefixes. -/
def PrefixFree (A : Finset Address) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p <+: q → p = q

private theorem family_injective (A : Finset Address) (hA : PrefixFree A) :
    Function.Injective (fun x : {p // p ∈ A} × Edge => descendant x.1.val x.2) := by
  rintro ⟨p, u⟩ ⟨q, v⟩ h
  have he : p.val ++ u.val = q.val ++ v.val := congrArg Subtype.val h
  have hc := List.prefix_or_prefix_of_prefix (p.val.prefix_append u.val)
    (he.symm ▸ q.val.prefix_append v.val)
  have hpq : p.val = q.val := hc.elim
    (hA _ p.property _ q.property) (fun h => (hA _ q.property _ p.property h).symm)
  have hp : p = q := Subtype.ext hpq
  subst q
  exact Prod.ext rfl (descendant_injective p.val h)

private theorem disjoint_energy (A : Finset Address) (hA : PrefixFree A) (z : H) :
    ∑ p ∈ A, ‖S p z‖^2 ≤ ‖z‖^2 := by
  classical
  have hs := (lp.memℓp z).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have hi := family_injective A hA
  have hb := tsum_comp_le_tsum_of_inj hs
    (fun u => Real.rpow_nonneg (norm_nonneg (z u)) _) hi
  have hc := hs.comp_injective hi
  have ht := hc.tsum_prod'
  simp only [Function.comp_def] at hb ht
  rw [ht] at hb
  rw [← Finset.sum_attach A (fun p => ‖S p z‖^2)]
  simp_rw [norm_sq]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, tsum_fintype,
    Finset.univ_eq_attach] using hb

/-- Strict suffixes retain their actual coordinates, omit all ancestors, and
have disjoint total energy. Their traces are the original infinite J. -/
theorem strict_suffix_energy :
    (∀ (p : Address) (z : H) (u : Edge), S p z u = z (descendant p u)) ∧
    (∀ (p : Address) (u : Edge), p.length < (descendant p u).val.length) ∧
    (∀ z : H, S [] z = z) ∧
    (∀ (A : Finset Address), PrefixFree A → ∀ z : H,
      ∑ p ∈ A, ‖S p z‖^2 ≤ ‖z‖^2) ∧
    (∀ (p : Address) (z : H),
      HasSum (fun u : Edge => z (descendant p u) • indicator u) (suffixTrace p z)) ∧
    (∀ (A : Finset Address), PrefixFree A → ∀ (h : ℕ) (z : H),
      ∑ p ∈ A, ‖J (S p z - P h (S p z))‖^2 ≤
        (a^(h+1)/(1-a))*‖z‖^2) := by
  refine ⟨fun _ _ _ => rfl, ?_, ?_, disjoint_energy, ?_, ?_⟩
  · intro p u
    have hu := List.length_pos_of_ne_nil u.property
    simpa only [descendant, List.length_append] using Nat.lt_add_of_pos_right hu
  · intro z
    ext u
    change z (descendant [] u) = z u
    rfl
  · intro p z
    exact boundary_trace_hardy.1 (S p z)
  · intro A hA h z
    have ha : 0 < a := inv_pos.mpr Real.goldenRatio_pos
    have ha1 : a < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
    calc
      _ ≤ ∑ p ∈ A, (a^(h+1)/(1-a))*‖S p z‖^2 :=
        Finset.sum_le_sum fun p _ => boundary_trace_hardy.2 h (S p z)
      _ = (a^(h+1)/(1-a)) * ∑ p ∈ A, ‖S p z‖^2 := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (disjoint_energy A hA z)
        (div_nonneg (pow_pos ha _).le (sub_pos.mpr ha1).le)

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySuffix
