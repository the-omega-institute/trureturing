/- GID: D5/S3/Geometry/Hyperideal/ActualAnglePolynomialCarrier
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/ActualAnglePolynomialCarrier
   mirror-E: none(waiver:original-physical-edge-quotient)
   anchors: []
   utility: none
   digest: Exact polynomial stationarity of original clipped angles on a whole actual face pairing. -/

import D5.S3.Geometry.Hyperideal.ActualCornerTransport
import D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Exact nonwinding certificate allowing flat endpoints, repeated leaves, and arbitrary rebracketing. -/

namespace D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier

noncomputable section
open Real

inductive Circuit where
  | leaf (angle : ℝ)
  | mul (left right : Circuit)

def angle : Circuit → ℝ
  | .leaf a => a
  | .mul l r => angle l + angle r

def phase : Circuit → ℝ × ℝ
  | .leaf a => (cos (a / 2), sin (a / 2))
  | .mul l r =>
      let p := phase l
      let q := phase r
      (p.1 * q.1 - p.2 * q.2, p.2 * q.1 + p.1 * q.2)

def leaves : Circuit → Prop
  | .leaf a => 0 ≤ a ∧ a ≤ π
  | .mul l r => leaves l ∧ leaves r

def valid : Circuit → Prop
  | .leaf a => 0 ≤ a ∧ a ≤ π
  | .mul l r => valid l ∧ valid r ∧
      0 ≤ (phase (.mul l r)).2 ∧
      ¬ ((phase l).1 = -1 ∧ (phase r).1 = -1)

theorem phase_exact (t : Circuit) :
    phase t = (cos (angle t / 2), sin (angle t / 2)) := by
  induction t with
  | leaf => rfl
  | mul l r hl hr =>
    have h : (angle l + angle r) / 2 = angle l / 2 + angle r / 2 := by ring
    simp only [phase, hl, hr, angle, h, cos_add, sin_add]

private theorem cos_neg_one_closed {x : ℝ} (hx₀ : 0 ≤ x) (hxπ : x ≤ π) :
    cos x = -1 ↔ x = π := by
  constructor
  · intro h
    have h' : cos x = cos π := h.trans cos_pi.symm
    simpa only [arccos_cos hx₀ hxπ, arccos_cos pi_pos.le le_rfl] using congrArg arccos h'
  · rintro rfl
    exact cos_pi

private theorem sin_neg_second {x : ℝ} (h₁ : π < x) (h₂ : x < 2 * π) :
    sin x < 0 := by
  have hp : 0 < x - π := by linarith
  have hq : x - π < π := by linarith
  have h := sin_pos_of_pos_of_lt_pi hp hq
  rw [sin_sub, sin_pi, cos_pi] at h
  linarith

theorem valid_iff (t : Circuit) :
    valid t ↔ leaves t ∧ 0 ≤ angle t ∧ angle t ≤ 2 * π := by
  induction t with
  | leaf a =>
    change (0 ≤ a ∧ a ≤ π) ↔ (0 ≤ a ∧ a ≤ π) ∧ 0 ≤ a ∧ a ≤ 2 * π
    grind [pi_pos]
  | mul l r hl hr =>
    change (valid l ∧ valid r ∧ 0 ≤ (phase (.mul l r)).2 ∧
      ¬ ((phase l).1 = -1 ∧ (phase r).1 = -1)) ↔
      (leaves l ∧ leaves r) ∧ 0 ≤ angle l + angle r ∧ angle l + angle r ≤ 2 * π
    rw [phase_exact (.mul l r), phase_exact l, phase_exact r, hl, hr]
    simp only [angle]
    constructor
    · rintro ⟨⟨hlv, hl₀, hl₂⟩, ⟨hrv, hr₀, hr₂⟩, hs, hn⟩
      refine ⟨⟨hlv, hrv⟩, by linarith, ?_⟩
      by_contra! hc
      by_cases he : (angle l + angle r) / 2 = 2 * π
      · apply hn
        refine ⟨?_, ?_⟩
        · have : angle l / 2 = π := by linarith
          rw [this, cos_pi]
        · have : angle r / 2 = π := by linarith
          rw [this, cos_pi]
      · have ht : (angle l + angle r) / 2 < 2 * π := lt_of_le_of_ne (by linarith) he
        exact (not_lt_of_ge hs) (sin_neg_second (by linarith) ht)
    · rintro ⟨⟨hlv, hrv⟩, hsum₀, hsum₂⟩
      have leaf_nonneg (t : Circuit) : leaves t → 0 ≤ angle t := by
        induction t with
        | leaf a => exact fun h => h.1
        | mul a b ha hb => exact fun h => add_nonneg (ha h.1) (hb h.2)
      have hl₀ := leaf_nonneg l hlv
      have hr₀ := leaf_nonneg r hrv
      refine ⟨⟨hlv, hl₀, by linarith⟩, ⟨hrv, hr₀, by linarith⟩,
        sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith), ?_⟩
      rintro ⟨hle,hre⟩
      have he₁ := (cos_neg_one_closed (by linarith) (by linarith)).mp hle
      have he₂ := (cos_neg_one_closed (by linarith) (by linarith)).mp hre
      linarith [pi_pos]

theorem stationary_iff (t : Circuit) :
    valid t ∧ phase t = (-1, 0) ↔ leaves t ∧ angle t = 2 * π := by
  rw [valid_iff, phase_exact]
  constructor
  · rintro ⟨⟨h₁,h₂,h₃⟩, hp⟩
    have hc := congrArg Prod.fst hp
    have h := (cos_neg_one_closed (by linarith) (by linarith)).mp hc
    exact ⟨h₁, by linarith⟩
  · rintro ⟨hl, h⟩
    refine ⟨⟨hl, by linarith [pi_pos], h.le⟩, ?_⟩
    have hh : angle t / 2 = π := by linarith
    rw [hh, cos_pi, sin_pi]

#print axioms stationary_iff

end
end D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier

namespace D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier

noncomputable section
open Real

def clip (x : ℝ) : ℝ := max (-1) (min 1 x)

def leafPoly (n d u v : ℝ) : Prop :=
  0 ≤ u ∧ 0 ≤ v ∧ u ^ 2 + v ^ 2 = 1 ∧
    ((n ≤ -d ∧ u = 0) ∨ (d ≤ n ∧ v = 0) ∨
      (-d ≤ n ∧ n ≤ d ∧ (u ^ 2 - v ^ 2) * d = n))

theorem leafPoly_iff (n d u v : ℝ) (hd : 0 < d) :
    leafPoly n d u v ↔
      (u,v) = phase (.leaf (arccos (clip (n / d)))) := by
  let c := clip (n / d)
  have hc₁ : -1 ≤ c := le_max_left ..
  have hc₂ : c ≤ 1 := max_le (by norm_num) (min_le_left ..)
  let a := arccos c / 2
  have ha₀ : 0 ≤ a := by dsimp [a]; positivity [arccos_nonneg c]
  have ha₂ : a ≤ π / 2 := by dsimp [a]; linarith [arccos_le_pi c]
  have hca := cos_nonneg_of_mem_Icc (show a ∈ Set.Icc (-(π / 2)) (π / 2) from
    ⟨by linarith [pi_pos], ha₂⟩)
  have hsa := sin_nonneg_of_nonneg_of_le_pi ha₀ (by linarith [pi_pos])
  have hsq := cos_sq_add_sin_sq a
  have ha2 : 2 * a = arccos c := by dsimp [a]; ring
  have hdiff : cos a ^ 2 - sin a ^ 2 = c := by
    calc
      _ = cos (2 * a) := (cos_two_mul' a).symm
      _ = c := by rw [ha2, cos_arccos hc₁ hc₂]
  have hlow (h : n ≤ -d) : c = -1 := by
    have hm : n / d ≤ -1 := (div_le_iff₀ hd).mpr (by linarith)
    dsimp [c, clip]
    rw [min_eq_right (by linarith), max_eq_left hm]
  have hhigh (h : d ≤ n) : c = 1 := by
    have hm : 1 ≤ n / d := (le_div_iff₀ hd).mpr (by linarith)
    dsimp [c, clip]
    rw [min_eq_left hm, max_eq_right (by norm_num)]
  have hmid (h₁ : -d ≤ n) (h₂ : n ≤ d) : c = n / d := by
    have hm₁ : -1 ≤ n / d := (le_div_iff₀ hd).mpr (by linarith)
    have hm₂ : n / d ≤ 1 := (div_le_iff₀ hd).mpr (by linarith)
    dsimp [c, clip]
    rw [min_eq_right hm₂, max_eq_right hm₁]
  change _ ↔ (u,v) = (cos a, sin a)
  constructor
  · rintro ⟨hu,hv,hs,h⟩
    have hUV : u ^ 2 - v ^ 2 = c := by
      rcases h with ⟨hn, rfl⟩ | ⟨hn,rfl⟩ | ⟨hn₁,hn₂,hn⟩
      · rw [hlow hn]; nlinarith
      · rw [hhigh hn]; nlinarith
      · rw [hmid hn₁ hn₂]; exact (eq_div_iff hd.ne').mpr hn
    have hu2 : u ^ 2 = cos a ^ 2 := by linarith
    have hv2 : v ^ 2 = sin a ^ 2 := by linarith
    exact Prod.ext ((sq_eq_sq_iff_eq_or_eq_neg.mp hu2).elim id (by intro h; linarith))
      ((sq_eq_sq_iff_eq_or_eq_neg.mp hv2).elim id (by intro h; linarith))
  · intro hp
    cases hp
    refine ⟨hca,hsa,hsq,?_⟩
    by_cases hn₁ : n ≤ -d
    · left
      rw [hlow hn₁] at hdiff
      exact ⟨hn₁, by nlinarith⟩
    by_cases hn₂ : d ≤ n
    · right; left
      rw [hhigh hn₂] at hdiff
      exact ⟨hn₂, by nlinarith⟩
    · right; right
      refine ⟨by linarith, by linarith, ?_⟩
      rw [hdiff, hmid (by linarith) (by linarith)]
      field_simp

#print axioms leafPoly_iff

end
end D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier

namespace D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier
noncomputable section
open Real

/-- Leaf labels may repeat; each occurrence contributes its original angle. -/
inductive Fan where
  | leaf (n d : ℝ)
  | mul (left right : Fan)

def decode : Fan → Circuit
  | .leaf n d => .leaf (arccos (clip (n / d)))
  | .mul l r => .mul (decode l) (decode r)

def denominatorsPos : Fan → Prop
  | .leaf _ d => 0 < d
  | .mul l r => denominatorsPos l ∧ denominatorsPos r

/-- This is polynomial evaluation only: multiplication gates use two auxiliary
real variables per child, with no trigonometric atoms in the certificate. -/
def polyEval : Fan → ℝ → ℝ → Prop
  | .leaf n d, u, v => leafPoly n d u v
  | .mul l r, u, v =>
      ∃ a b c d : ℝ,
        polyEval l a b ∧ polyEval r c d ∧
        u = a * c - b * d ∧ v = b * c + a * d ∧
        0 ≤ v ∧ ¬ (a = -1 ∧ c = -1)

theorem decoded_leaves (f : Fan) : leaves (decode f) := by
  induction f with
  | leaf n d => exact ⟨arccos_nonneg _, arccos_le_pi _⟩
  | mul l r hl hr => exact ⟨hl, hr⟩

theorem polyEval_iff (f : Fan) (hd : denominatorsPos f) (u v : ℝ) :
    polyEval f u v ↔ valid (decode f) ∧ (u,v) = phase (decode f) := by
  induction f generalizing u v with
  | leaf n d =>
    rw [polyEval, leafPoly_iff n d u v hd]
    exact ⟨fun h => ⟨decoded_leaves (.leaf n d), h⟩, And.right⟩
  | mul l r hl hr =>
    have hdl := hd.1
    have hdr := hd.2
    change (∃ a b c d, polyEval l a b ∧ polyEval r c d ∧
        u = a * c - b * d ∧ v = b * c + a * d ∧ 0 ≤ v ∧ ¬ (a = -1 ∧ c = -1)) ↔ _
    constructor
    · rintro ⟨a,b,c,d,hab,hcd,hu,hv,hsgn,hn⟩
      obtain ⟨hlv,hpl⟩ := (hl hdl a b).mp hab
      obtain ⟨hrv,hpr⟩ := (hr hdr c d).mp hcd
      refine ⟨⟨hlv,hrv,?_,?_⟩,?_⟩
      · simp only [phase, ← hpl, ← hpr]
        rw [← hv]
        exact hsgn
      · simpa only [← hpl, ← hpr] using hn
      · simp only [decode, phase, ← hpl, ← hpr]
        rw [hu,hv]
    · rintro ⟨⟨hlv,hrv,hsgn,hn⟩,hp⟩
      let p := phase (decode l)
      let q := phase (decode r)
      have hu : u = p.1 * q.1 - p.2 * q.2 := congrArg Prod.fst hp
      have hv : v = p.2 * q.1 + p.1 * q.2 := congrArg Prod.snd hp
      refine ⟨p.1,p.2,q.1,q.2,(hl hdl _ _).mpr ⟨hlv,Prod.eta _⟩,
        (hr hdr _ _).mpr ⟨hrv,Prod.eta _⟩,hu,hv,?_,hn⟩
      rw [hv]
      exact hsgn

/-- Exact original-angle stationary test for one physical edge fan, including
arbitrary repetition and flat 0/π slots, with no winding alias. -/
theorem algebraic_fan_iff_stationary (f : Fan) (hd : denominatorsPos f) :
    polyEval f (-1) 0 ↔ angle (decode f) = 2 * π := by
  rw [polyEval_iff f hd]
  simp only [eq_comm (a := ((-1 : ℝ), (0 : ℝ))), stationary_iff]
  exact ⟨And.right, fun h => ⟨decoded_leaves f, h⟩⟩

#print axioms algebraic_fan_iff_stationary

end
end D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier

namespace D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier

noncomputable section
open Real
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface

/-- The fixed local order is (01, 02, 03, 23, 13, 12), as in the protected
original-cosine supplier. Each marked view makes its target the first slot. -/
def marked (z : Fin 6 → ℝ) (j : Fin 6) : Fin 6 → ℝ :=
  ![z, ![z 1,z 0,z 2,z 4,z 3,z 5], ![z 2,z 0,z 1,z 5,z 3,z 4],
       ![z 3,z 1,z 5,z 0,z 4,z 2], ![z 4,z 0,z 5,z 1,z 3,z 2],
       ![z 5,z 0,z 4,z 2,z 3,z 1]] j

def numerator (z : Fin 6 → ℝ) : ℝ := N (z 0) (z 1) (z 2) (z 3) (z 4) (z 5)
def leftRad (z : Fin 6 → ℝ) : ℝ := D1 (z 0) (z 1) (z 5)
def rightRad (z : Fin 6 → ℝ) : ℝ := D2 (z 0) (z 2) (z 4)
def denom (z : Fin 6 → ℝ) : ℝ := √(leftRad z) * √(rightRad z)
def originalAngle (z : Fin 6 → ℝ) : ℝ := arccos (clip (numerator z / denom z))

theorem marked_gt_one {z : Fin 6 → ℝ} (h : ∀ k, 1 < z k)
    (j k : Fin 6) : 1 < marked z j k := by
  fin_cases j <;> fin_cases k <;> simpa [marked] using h _

theorem face_rad_pos {z : Fin 6 → ℝ} (h : ∀ k, 1 < z k) :
    0 < leftRad z ∧ 0 < rightRad z :=
  (original_cosine_interface _ _ _ _ _ _ (h 0) (h 1) (h 2) (h 3) (h 4) (h 5)).1

theorem root_poly_iff {r : ℝ} (hr : 0 < r) (s : ℝ) :
    0 < s ∧ s ^ 2 = r ↔ s = √r := by
  constructor
  · rintro ⟨hs, h⟩
    have hs2 : s^2 = (√r)^2 := h.trans (sq_sqrt hr.le).symm
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hs2).elim id (by intro q; linarith [sqrt_nonneg r])
  · rintro rfl
    exact ⟨sqrt_pos.2 hr, sq_sqrt hr.le⟩

abbrev Slot (T : Type*) := T × Fin 6
variable {T E : Type*}

inductive OccurrenceTree (T : Type*) where
  | leaf (slot : Slot T)
  | mul (left right : OccurrenceTree T)

def occurrenceList : OccurrenceTree T → List (Slot T)
  | .leaf a => [a]
  | .mul l r => occurrenceList l ++ occurrenceList r

def occurrenceFan (owner : T → Fin 6 → E) (x : E → ℝ) :
    OccurrenceTree T → Fan
  | .leaf (t,j) =>
      let z := marked (fun k => x (owner t k)) j
      .leaf (numerator z) (denom z)
  | .mul l r => .mul (occurrenceFan owner x l) (occurrenceFan owner x r)

def physicalPoly (owner : T → Fin 6 → E) (x : E → ℝ) :
    OccurrenceTree T → ℝ → ℝ → Prop
  | .leaf (t,j), u,v =>
      let z := marked (fun k => x (owner t k)) j
      ∃ s₁ s₂ : ℝ, (0 < s₁ ∧ s₁ ^ 2 = leftRad z) ∧
        (0 < s₂ ∧ s₂ ^ 2 = rightRad z) ∧ leafPoly (numerator z) (s₁*s₂) u v
  | .mul l r, u,v =>
      ∃ a b c d : ℝ, physicalPoly owner x l a b ∧ physicalPoly owner x r c d ∧
        u = a * c - b * d ∧ v = b * c + a * d ∧
        0 ≤ v ∧ ¬ (a = -1 ∧ c = -1)

theorem occurrenceFan_pos (owner : T → Fin 6 → E) (x : E → ℝ)
    (hx : ∀ e, 1 < x e) (t : OccurrenceTree T) : denominatorsPos (occurrenceFan owner x t) := by
  induction t with
  | leaf p =>
    obtain ⟨l,r⟩ := face_rad_pos (marked_gt_one (fun k => hx (owner p.1 k)) p.2)
    exact mul_pos (sqrt_pos.2 l) (sqrt_pos.2 r)
  | mul l r hl hr => exact ⟨hl,hr⟩

theorem physicalPoly_iff (owner : T → Fin 6 → E) (x : E → ℝ) (hx : ∀ e, 1 < x e)
    (t : OccurrenceTree T) (u v : ℝ) :
    physicalPoly owner x t u v ↔ polyEval (occurrenceFan owner x t) u v := by
  induction t generalizing u v with
  | leaf p =>
    obtain ⟨l,r⟩ := face_rad_pos (marked_gt_one (fun k => hx (owner p.1 k)) p.2)
    simp only [physicalPoly, occurrenceFan, polyEval, root_poly_iff l, root_poly_iff r, denom]
    exact ⟨by rintro ⟨s₁,s₂,rfl,rfl,h⟩; exact h, fun h => ⟨_,_,rfl,rfl,h⟩⟩
  | mul l r hl hr => simp only [physicalPoly, occurrenceFan, polyEval, hl,hr]

def localPhysicalAngle (owner : T → Fin 6 → E) (x : E → ℝ) (p : Slot T) : ℝ :=
  originalAngle (marked (fun k => x (owner p.1 k)) p.2)

theorem occurrenceFan_sum (owner : T → Fin 6 → E) (x : E → ℝ) (t : OccurrenceTree T) :
    angle (decode (occurrenceFan owner x t)) =
      ((occurrenceList t).map (localPhysicalAngle owner x)).sum := by
  induction t with
  | leaf a => simp [occurrenceList, occurrenceFan, localPhysicalAngle, originalAngle, angle,decode]
  | mul l r hl hr =>
    simp only [occurrenceFan, decode, angle, occurrenceList, List.map_append, List.sum_append, hl, hr]

/-- The polynomial certificate for a literal marked tree exactly checks its
clipped-original-angle sum, with repeated physical owners counted by occurrence. -/
theorem physical_poly_iff_original_stationary
    (owner : T → Fin 6 → E) (x : E → ℝ) (hx : ∀ e, 1 < x e) (t : OccurrenceTree T) :
    physicalPoly owner x t (-1) 0 ↔
      ((occurrenceList t).map (localPhysicalAngle owner x)).sum = 2 * π := by
  rw [physicalPoly_iff owner x hx, algebraic_fan_iff_stationary _ (occurrenceFan_pos owner x hx t),
    occurrenceFan_sum]

#print axioms physical_poly_iff_original_stationary

end
end D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier

namespace D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier

noncomputable section
open Real
variable {T E : Type*} [Fintype T] [DecidableEq T] [DecidableEq E]

def physicalSlots (owner : T → Fin 6 → E) (e : E) : Finset (Slot T) :=
  Finset.univ.filter (fun p => owner p.1 p.2 = e)

def carrierStationary (owner : T → Fin 6 → E) (x : E → ℝ) : Prop :=
  ∀ e, (∑ p ∈ physicalSlots owner e, localPhysicalAngle owner x p) = 2 * π

def treeCarrierPoly (owner : T → Fin 6 → E) (x : E → ℝ)
    (trees : E → OccurrenceTree T) : Prop :=
  ∀ e, physicalPoly owner x (trees e) (-1) 0

/-- Certificate completeness is invariant under rebracketing and ordering.
No assumption prohibits repeated physical edges within a tetrahedron: the
verification is over the *slots* of the labelled carrier, not the owner set. -/
theorem physical_carrier_poly_iff (owner : T → Fin 6 → E) (x : E → ℝ) (hx : ∀ e, 1 < x e)
    (trees : E → OccurrenceTree T)
    (ht : ∀ e, (occurrenceList (trees e)).Nodup ∧
      (occurrenceList (trees e)).toFinset = physicalSlots owner e) :
    treeCarrierPoly owner x trees ↔ carrierStationary owner x := by
  have h (e : E) :
      ((occurrenceList (trees e)).map (localPhysicalAngle owner x)).sum =
        ∑ p ∈ physicalSlots owner e, localPhysicalAngle owner x p := by
    rw [← (ht e).2]
    exact (List.sum_toFinset (f := localPhysicalAngle owner x) (ht e).1).symm
  unfold treeCarrierPoly carrierStationary
  simp only [physical_poly_iff_original_stationary owner x hx, h]

#print axioms physical_carrier_poly_iff

end
end D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier

namespace D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier
noncomputable section
open Real
open scoped Classical
open D5.S3.Geometry.Hyperideal.ActualCornerTransport (Pairing GlobalEdge P M)

variable {T : Type*} [Fintype T]

def foldOccurrences (a : D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier.Slot T) (l : List (D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier.Slot T)) :
    OccurrenceTree T :=
  match l with
  | [] => .leaf a
  | b :: bs => .mul (.leaf a) (foldOccurrences b bs)

omit [Fintype T] in
theorem foldOccurrences_list (a : D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier.Slot T) (l : List (D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier.Slot T)) :
    occurrenceList (foldOccurrences a l) = a :: l := by
  induction l generalizing a with
  | nil => rfl
  | cons b bs h => simp [foldOccurrences, occurrenceList, h]

def ownerOf (q : Pairing T) (t : T) (j : Fin 6) : GlobalEdge q := P q (t,j)

theorem actual_slots_nonempty (q : Pairing T) (e : GlobalEdge q) :
    (physicalSlots (ownerOf q) e).Nonempty := by
  classical
  refine Quotient.inductionOn e ?_
  intro p
  exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- No fan enumeration assumptions are left at the public endpoint. The
finite list for each true quotient edge is obtained from the actual pairing. -/
theorem actual_pairing_algebraic_stationary (q : Pairing T) (x : GlobalEdge q → ℝ)
    (hx : ∀ e, 1 < x e) :
    (∃ trees : GlobalEdge q → OccurrenceTree T,
        (∀ e, (occurrenceList (trees e)).Nodup ∧
          (occurrenceList (trees e)).toFinset = physicalSlots (ownerOf q) e) ∧
        treeCarrierPoly (ownerOf q) x trees) ↔
      ∀ e, M q (localPhysicalAngle (ownerOf q) x) e = 2 * π := by
  classical
  have hsets (e : GlobalEdge q) :
      (∑ p ∈ physicalSlots (ownerOf q) e, localPhysicalAngle (ownerOf q) x p) =
      M q (localPhysicalAngle (ownerOf q) x) e := by
    unfold physicalSlots M
    exact Finset.sum_filter _ (localPhysicalAngle (ownerOf q) x)
  have hs : carrierStationary (ownerOf q) x ↔
      ∀ e, M q (localPhysicalAngle (ownerOf q) x) e = 2 * π := by
    unfold carrierStationary
    simp only [hsets]
  rw [← hs]
  constructor
  · rintro ⟨trees, htrees, hpoly⟩
    exact (physical_carrier_poly_iff (ownerOf q) x hx trees htrees).mp hpoly
  · intro hc
    have ht (e : GlobalEdge q) :
        ∃ t : OccurrenceTree T, (occurrenceList t).Nodup ∧
          (occurrenceList t).toFinset = physicalSlots (ownerOf q) e := by
      let L := (physicalSlots (ownerOf q) e).toList
      have hnd : L.Nodup := Finset.nodup_toList _
      have hfin : L.toFinset = physicalSlots (ownerOf q) e := Finset.toList_toFinset _
      cases he : L with
      | nil =>
        rw [he] at hfin
        rcases actual_slots_nonempty q e with ⟨a,ha⟩
        rw [← hfin] at ha
        simp at ha
      | cons a l =>
        refine ⟨foldOccurrences a l, ?_⟩
        simpa only [foldOccurrences_list, ← he] using And.intro hnd hfin
    choose trees htrees using ht
    exact ⟨trees, htrees, (physical_carrier_poly_iff (ownerOf q) x hx trees htrees).mpr hc⟩

#print axioms actual_pairing_algebraic_stationary

end
end D5.S3.Geometry.Hyperideal.ActualAnglePolynomialCarrier
