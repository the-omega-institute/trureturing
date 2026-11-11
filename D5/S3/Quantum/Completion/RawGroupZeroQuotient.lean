/- GID: D5/S3/Quantum/Completion/RawGroupZeroQuotient
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/RawGroupZeroQuotient
   mirror-E: none(waiver:abstract-group-quotient)
   anchors: []
   utility: none
   digest: Actual zero-cost normal subgroups support total marker and cost descent. -/

import D5.S3.Quantum.Completion.RawGroupZeroDrift
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open D5.S3.Quantum.Completion.RawUnanchoredReplication
namespace D5.S3.Quantum.Completion.RawGroupZeroQuotient
universe u
variable {G : Type u} [Group G] {U : G → G} {c : G → G → ℝ}

lemma right_diff (h : RawCost U c) (a b : G) :
    c a b = c (a * b⁻¹) 1 := by
  simpa only [mul_inv_cancel] using (D5.S3.Quantum.Completion.RawGroupZeroDrift.right_invariant h a b b⁻¹).symm

def zeroSubgroup (h : RawCost U c) (hs : ∀ a b, c a b = c b a) : Subgroup G where
  carrier := {z | c z 1 = 0}
  one_mem' := h.diagonal 1
  mul_mem' := by
    intro x y hx hy
    change c x 1 = 0 at hx
    change c y 1 = 0 at hy
    change c (x*y) 1 = 0
    have ht := single h x 1 y 1
    simp only [one_mul, hx, hy] at ht
    exact le_antisymm (by linarith) (h.nonneg _ _)
  inv_mem' := by
    intro x hx
    change c x⁻¹ 1 = 0
    exact (D5.S3.Quantum.Completion.RawGroupZeroDrift.inverse_budget h hs x).trans hx

instance zeroNormal (h : RawCost U c) (hs : ∀ a b, c a b = c b a) :
    (zeroSubgroup h hs).Normal where
  conj_mem := by
    intro z hz a
    change c z 1 = 0 at hz
    change c (a*z*a⁻¹) 1 = 0
    rw [← right_diff h (a*z) a]
    have ht := single h a a z 1
    simp only [mul_one, h.diagonal, hz] at ht
    exact le_antisymm (by linarith) (h.nonneg _ _)

/-- Constancy on the full zero coset follows from its finite three-term averaging law. -/
lemma zero_coset (h : RawCost U c) (hs : ∀ a b, c a b = c b a)
    (x z : G) (hz : z ∈ zeroSubgroup h hs) : c (x*z) 1 = c x 1 := by
  let Z := zeroSubgroup h hs
  let F : Z → ℝ := fun t => c (x*t) 1
  let R : Set ℝ := Set.range F
  have hne : R.Nonempty := ⟨F 1, ⟨1, rfl⟩⟩
  have hbd : BddBelow R := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact h.nonneg _ _
  have hm (t : Z) : sInf R ≤ F t := csInf_le hbd ⟨t, rfl⟩
  let T (n : ℕ) (w : Z) : Z :=
    ⟨U^[n] (w:G) * (U^[n] 1)⁻¹, by
      change c (U^[n] (w:G) * (U^[n] 1)⁻¹) 1 = 0
      rw [← right_diff h (U^[n] (w:G)) (U^[n] 1), sync_iter h]
      exact w.property⟩
  have ht (s w : Z) : F (s*w) ≤ 3*F s - 2*sInf R := by
    have hfirst : c ((x*(s:G))*(w:G)) (1*1) = F (s*w) := by
      simp only [F, Subgroup.coe_mul, one_mul, mul_assoc]
    have hmark (n : ℕ) :
        c ((x*(s:G))*U^[n] (w:G)) (1*U^[n] 1) = F (s*T n w) := by
      rw [right_diff h]
      simp only [F, T, Subgroup.coe_mul, Subgroup.coe_mk, one_mul, mul_assoc]
    have hb := h.balance (x*(s:G)) 1 (w:G) 1
    rw [hfirst, show c ((x*(s:G))*U (w:G)) (1*U 1) = F (s*T 1 w) from hmark 1,
      show c ((x*(s:G))*U (U (w:G))) (1*U (U 1)) = F (s*T 2 w) from hmark 2] at hb
    have hw : c (w:G) 1 = 0 := w.property
    change F (s*w) + F (s*T 1 w) + F (s*T 2 w) = 3*F s + 3*c (w:G) 1 at hb
    rw [hw] at hb
    linarith [hm (s*T 1 w), hm (s*T 2 w)]
  have heq (s : Z) : F s = sInf R := by
    have hlow : (F s + 2*sInf R)/3 ≤ sInf R := by
      apply le_csInf hne
      rintro _ ⟨t, rfl⟩
      have hh := ht t (t⁻¹*s)
      rw [mul_inv_cancel_left] at hh
      linarith
    exact le_antisymm (by linarith) (hm s)
  have hh := (heq ⟨z,hz⟩).trans (heq 1).symm
  simpa only [F, Subgroup.coe_mk, Subgroup.coe_one, mul_one] using hh

lemma independent_representatives (h : RawCost U c) (hs : ∀ a b, c a b = c b a)
    (a b z w : G) (hz : z ∈ zeroSubgroup h hs) (hw : w ∈ zeroSubgroup h hs) :
    c (a*z) (b*w) = c a b := by
  let Z := zeroSubgroup h hs
  have hp : b*(z*w⁻¹)*b⁻¹ ∈ Z :=
    (zeroNormal h hs).conj_mem _ (Z.mul_mem hz (Z.inv_mem hw)) b
  rw [right_diff h (a*z) (b*w), right_diff h a b]
  have he : (a*z)*(b*w)⁻¹ = (a*b⁻¹)*(b*(z*w⁻¹)*b⁻¹) := by group
  rw [he]
  exact zero_coset h hs (a*b⁻¹) _ hp

lemma zero_iff_class (h : RawCost U c) (hs : ∀ a b, c a b = c b a) (a b : G) :
    c a b = 0 ↔ (QuotientGroup.mk a : G ⧸ zeroSubgroup h hs) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq_iff_div_mem]
  change c a b = 0 ↔ c (a/b) 1 = 0
  rw [div_eq_mul_inv, ← right_diff h a b]

lemma marker_classes (h : RawCost U c) (hs : ∀ a b, c a b = c b a) (a b : G)
    (hab : (QuotientGroup.mk a : G ⧸ zeroSubgroup h hs) = QuotientGroup.mk b) :
    (QuotientGroup.mk (U a) : G ⧸ zeroSubgroup h hs) = QuotientGroup.mk (U b) := by
  apply (zero_iff_class h hs _ _).mp
  have he := sync_iter h 1 a b
  exact he.trans ((zero_iff_class h hs _ _).mpr hab)

def quotientMarker (h : RawCost U c) (hs : ∀ a b, c a b = c b a) :
    G ⧸ zeroSubgroup h hs → G ⧸ zeroSubgroup h hs :=
  Quotient.lift (fun a => QuotientGroup.mk (U a))
    (fun a b hab => marker_classes h hs a b (Quotient.sound hab))

def quotientCost (h : RawCost U c) (hs : ∀ a b, c a b = c b a) :
    G ⧸ zeroSubgroup h hs → G ⧸ zeroSubgroup h hs → ℝ :=
  Quotient.lift₂ c (by
    intro a b a' b' ha hb
    have hza := QuotientGroup.leftRel_apply.mp ha
    have hzb := QuotientGroup.leftRel_apply.mp hb
    have hi := independent_representatives h hs a b (a⁻¹*a') (b⁻¹*b') hza hzb
    simpa only [mul_inv_cancel_left] using hi.symm)

lemma quotientMarker_mk (h : RawCost U c) (hs : ∀ a b, c a b = c b a) (a : G) :
    quotientMarker h hs (QuotientGroup.mk a) = QuotientGroup.mk (U a) := rfl

lemma quotientCost_mk (h : RawCost U c) (hs : ∀ a b, c a b = c b a) (a b : G) :
    quotientCost h hs (QuotientGroup.mk a) (QuotientGroup.mk b) = c a b := rfl

lemma quotient_raw (h : RawCost U c) (hs : ∀ a b, c a b = c b a) :
    RawCost (quotientMarker h hs) (quotientCost h hs) := by
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    exact h.nonneg x y
  · intro a
    refine Quotient.inductionOn a ?_
    intro x
    exact h.diagonal x
  · intro a b x y
    refine Quotient.inductionOn₂ a b ?_
    intro a b
    refine Quotient.inductionOn₂ x y ?_
    intro x y
    exact h.balance a b x y

lemma quotient_symmetric (h : RawCost U c) (hs : ∀ a b, c a b = c b a) :
    ∀ a b, quotientCost h hs a b = quotientCost h hs b a := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  exact hs

/-- All clauses of original 19.2 on the actual arbitrary group and its actual normal quotient. -/
theorem group19_2 (U : G → G) (c : G → G → ℝ) (h : RawCost U c)
    (hs : ∀ a b, c a b = c b a) :
    ∃ f : G → ℝ,
      (∀ g, 0 ≤ f g) ∧ (∀ g, f g = c g 1) ∧
      (∀ a b, c a b = f (a*b⁻¹)) ∧ f 1 = 0 ∧ (∀ g, f g⁻¹ = f g) ∧
      (∀ a b z, c (a*z) (b*z) = c a b) ∧
      ∃ Z : Subgroup G, (∀ z, z ∈ Z ↔ f z = 0) ∧
        ∃ hn : Z.Normal, letI : Z.Normal := hn
          (∀ a b z w, z ∈ Z → w ∈ Z → c (a*z) (b*w) = c a b) ∧
          (∀ a b, (QuotientGroup.mk a : G ⧸ Z) = QuotientGroup.mk b →
            (QuotientGroup.mk (U a) : G ⧸ Z) = QuotientGroup.mk (U b)) ∧
          ∃ (V : G ⧸ Z → G ⧸ Z) (d : G ⧸ Z → G ⧸ Z → ℝ),
            (∀ a b, d (QuotientGroup.mk a) (QuotientGroup.mk b) = c a b) ∧
            (∀ a, V (QuotientGroup.mk a) = QuotientGroup.mk (U a)) ∧
            RawCost V d ∧ (∀ a b, d a b = d b a) ∧
            (∀ a b, c a b = 0 ↔ (QuotientGroup.mk a : G ⧸ Z) = QuotientGroup.mk b) := by
  refine ⟨fun g => c g 1, fun g => h.nonneg g 1, fun _ => rfl,
    right_diff h, h.diagonal 1, D5.S3.Quantum.Completion.RawGroupZeroDrift.inverse_budget h hs,
    D5.S3.Quantum.Completion.RawGroupZeroDrift.right_invariant h, zeroSubgroup h hs, fun _ => Iff.rfl,
    zeroNormal h hs, independent_representatives h hs, marker_classes h hs,
    quotientMarker h hs, quotientCost h hs, quotientCost_mk h hs,
    quotientMarker_mk h hs, quotient_raw h hs, quotient_symmetric h hs, zero_iff_class h hs⟩

end D5.S3.Quantum.Completion.RawGroupZeroQuotient
