/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The weighted Huang boundary kernels of both star parities recover the base kernel. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridSignedCompression

/-! The weighted Huang exterior-row kernels on the two parities of a three-axis star lift. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift

open BalancedCriticalSpectrum (Q flip)
open Q9IsotropicHuang (flipSign parity weightedAction weightedLinear
  weightedLinear_apply weightedLinear_square)
open SixAxisGridSignedCompression (empty single flip_append_left flip_append_right)

variable {F : Type*} [Field F]

/-- Functions with support in the given set of vertices. -/
def supported {X : Type*} (S : Set X) : Submodule F (X → F) where
  carrier := {f | ∀ x ∉ S, f x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x hx
    change f x + g x = 0
    rw [hf x hx, hg x hx, add_zero]
  smul_mem' := by
    intro a f hf x hx
    change a * f x = 0
    rw [hf x hx, mul_zero]

/-- The incidence kernel from the allowed input columns to the exterior output rows. -/
def boundaryKernel {X : Type*} (H : Module.End F (X → F)) (M B : Set X) :
    Submodule F (X → F) :=
  supported M ⊓ (supported B).comap H

private theorem mem_boundary {X : Type*} {H : Module.End F (X → F)} {M B : Set X}
    {f : X → F} : f ∈ boundaryKernel H M B ↔
      (∀ x ∉ M, f x = 0) ∧ (∀ x ∉ B, H f x = 0) := Iff.rfl

private def orientation (b : Bool) : ℤ := if b then 1 else -1

/-- The false-prefix sign contributed by the entire six-axis block. -/
def baseSign (x : Q 6) : ℤ :=
  (if x 0 then 1 else -1) * ((if x 1 then 1 else -1) *
  ((if x 2 then 1 else -1) * ((if x 3 then 1 else -1) *
  ((if x 4 then 1 else -1) * (if x 5 then 1 else -1)))))

private theorem orientation_ne (b : Bool) : orientation b ≠ orientation (!b) := by
  cases b <;> decide

private theorem orientation_not (b : Bool) : orientation (!b) = -orientation b := by
  cases b <;> decide

private theorem baseSign_cases (x : Q 6) : baseSign x = 1 ∨ baseSign x = -1 := by
  unfold baseSign
  split <;> split <;> split <;> split <;> split <;> split <;> decide

private theorem baseSign_flip (x : Q 6) (i : Fin 6) :
    baseSign (flip x i) = -baseSign x := by
  have negSign (t : Bool) :
      (if !t then (1 : ℤ) else -1) = -(if t then 1 else -1) := by cases t <;> decide
  fin_cases i <;> first
    | change baseSign (flip x 0) = -baseSign x
    | change baseSign (flip x 1) = -baseSign x
    | change baseSign (flip x 2) = -baseSign x
    | change baseSign (flip x 3) = -baseSign x
    | change baseSign (flip x 4) = -baseSign x
    | change baseSign (flip x 5) = -baseSign x
  all_goals
    simp (disch := decide) only [baseSign, BalancedCriticalSpectrum.flip,
      Function.update_self, Function.update_of_ne, negSign] <;> ring

private theorem flipSign_left (x : Q 6) (z : Q 3) (i : Fin 6) :
    flipSign (i.castAdd 3) (Fin.append x z) = flipSign i x := by
  fin_cases i <;> rfl

private theorem flipSign_right (x : Q 6) (z : Q 3) (i : Fin 3) :
    flipSign (Fin.natAdd 6 i) (Fin.append x z) = baseSign x * flipSign i z := by
  fin_cases i <;> simp only [baseSign, mul_assoc] <;> rfl

/-- The six-axis weighted Huang action with the same prefix convention. -/
def baseAction (a : Fin 6 → F) : Module.End F (Q 6 → F) :=
  ∑ i, a i • LinearMap.pi fun x => (flipSign i x : F) • LinearMap.proj (flip x i)

private theorem baseAction_apply (a : Fin 6 → F) (f : Q 6 → F) (x : Q 6) :
    baseAction a f x = ∑ i, a i * (flipSign i x : F) * f (flip x i) := by
  simp [baseAction, Finset.sum_apply, mul_assoc]

private def starRow {X : Type*} (w : Fin 3 → F) (f : Q 3 → X → F) (z : Q 3) (x : X) : F :=
  ∑ i, w i * (flipSign i z : F) * f (flip z i) x

private theorem huang_row (a : Fin 6 → F) (w : Fin 3 → F) (f : Q 9 → F) (x : Q 6) (z : Q 3) :
    weightedLinear (Fin.append a w) f (Fin.append x z) =
      baseAction a (fun y => f (Fin.append y z)) x +
      (baseSign x : F) * starRow w (fun t y => f (Fin.append y t)) z x := by
  rw [weightedLinear_apply]
  simp only [weightedAction, Fin.sum_univ_add (a := 6) (b := 3), Fin.append_left,
    Fin.append_right, flipSign_left, flipSign_right, Int.cast_mul, flip_append_left,
    flip_append_right, baseAction_apply, starRow, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem baseAction_square (a : Fin 6 → F) (f : Q 6 → F) (x : Q 6) :
    baseAction a (baseAction a f) x = (∑ i, a i ^ 2) * f x := by
  let g : Q 9 → F := fun v => f (fun i => v (i.castAdd 3))
  have hg (y : Q 6) (z : Q 3) : g (Fin.append y z) = f y := by simp [g]
  have hz (p : Q 9 → F) (y : Q 6) (z : Q 3) :
      weightedLinear (Fin.append a (0 : Fin 3 → F)) p (Fin.append y z) =
      baseAction a (fun t => p (Fin.append t z)) y := by
    rw [huang_row]
    simp [starRow]
  have hs := congrArg (fun H : Module.End F (Q 9 → F) => H g (Fin.append x empty))
    (weightedLinear_square (Fin.append a (0 : Fin 3 → F)))
  change weightedLinear _ (weightedLinear _ g) (Fin.append x empty) =
    ((∑ i, (Fin.append a (0 : Fin 3 → F) i) ^ 2) • (1 : Module.End F (Q 9 → F))) g
      (Fin.append x empty) at hs
  rw [hz] at hs
  simp only [hz, hg, LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_add (a := 6) (b := 3), Fin.append_left, Fin.append_right, Pi.zero_apply,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero] at hs
  exact hs

private theorem baseAction_zero_on_parity (a : Fin 6 → F) (b : Bool) (M : Set (Q 6))
    (hM : ∀ x ∈ M, baseSign x = orientation b) (f : Q 6 → F)
    (hf : ∀ x ∉ M, f x = 0) (x : Q 6) (hx : baseSign x = orientation b) :
    baseAction a f x = 0 := by
  rw [baseAction_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi : flip x i ∉ M := by
    intro h
    apply orientation_ne b
    have he := hM _ h
    rwa [baseSign_flip, hx, ← orientation_not, eq_comm] at he
  rw [hf _ hi, mul_zero]

private def double (i j : Fin 3) : Q 3 := flip (single i) j
private def triple : Q 3 := fun _ => false

private theorem star_cases (z : Q 3) :
    z = empty ∨ (∃ i, z = single i) ∨ (∃ i j, i < j ∧ z = double i j) ∨ z = triple := by
  exact (by decide : ∀ z : Q 3,
    z = empty ∨ (∃ i, z = single i) ∨ (∃ i j, i < j ∧ z = double i j) ∨ z = triple) z

private def starIndex (z : Q 3) : Option (Option (Fin 3)) :=
  match z 0, z 1, z 2 with
  | true, true, true => some none
  | false, true, true => some (some 0)
  | true, false, true => some (some 1)
  | true, true, false => some (some 2)
  | _, _, _ => none

private theorem starIndex_single (i : Fin 3) : starIndex (single i) = some (some i) := by
  fin_cases i <;> decide

private theorem starIndex_double {i j : Fin 3} (h : i < j) :
    starIndex (double i j) = none := by
  fin_cases i <;> fin_cases j <;> first | decide | (exfalso; omega)

private def fill {A : Type*} [Zero A] (p : A) (s : Fin 3 → A) (z : Q 3) : A :=
  match starIndex z with
  | some none => p
  | some (some i) => s i
  | none => 0

private theorem fill_empty {A : Type*} [Zero A] (p : A) (s : Fin 3 → A) :
    fill p s empty = p := rfl

private theorem fill_single {A : Type*} [Zero A] (p : A) (s : Fin 3 → A) (i : Fin 3) :
    fill p s (single i) = s i := by simp [fill, starIndex_single]

private theorem fill_double {A : Type*} [Zero A] (p : A) (s : Fin 3 → A)
    {i j : Fin 3} (h : i < j) : fill p s (double i j) = 0 := by
  simp [fill, starIndex_double h]

private theorem fill_triple {A : Type*} [Zero A] (p : A) (s : Fin 3 → A) :
    fill p s triple = 0 := rfl

private theorem starRow_empty {X : Type*} (w : Fin 3 → F)
    (p : X → F) (s : Fin 3 → X → F) (x : X) :
    starRow w (fill p s) empty x = ∑ i, w i * s i x := by
  unfold starRow
  apply Finset.sum_congr rfl
  intro i _
  have hi : flipSign i empty = 1 := by fin_cases i <;> decide
  change w i * (flipSign i empty : F) * fill p s (single i) x = _
  rw [hi, Int.cast_one, mul_one, fill_single]

private theorem starRow_single {X : Type*} (w : Fin 3 → F)
    (p : X → F) (s : Fin 3 → X → F) (i : Fin 3) (x : X) :
    starRow w (fill p s) (single i) x = w i * p x := by
  fin_cases i <;> rw [starRow, Fin.sum_univ_three]
  · change w 0 * (↑(1 : ℤ) : F) * p x + w 1 * (↑(-1 : ℤ) : F) * 0 +
      w 2 * (↑(-1 : ℤ) : F) * 0 = w 0 * p x
    norm_num
  · change w 0 * (↑(1 : ℤ) : F) * 0 + w 1 * (↑(1 : ℤ) : F) * p x +
      w 2 * (↑(-1 : ℤ) : F) * 0 = w 1 * p x
    norm_num
  · change w 0 * (↑(1 : ℤ) : F) * 0 + w 1 * (↑(1 : ℤ) : F) * 0 +
      w 2 * (↑(1 : ℤ) : F) * p x = w 2 * p x
    norm_num

private theorem starRow_double {X : Type*} (w : Fin 3 → F)
    (p : X → F) (s : Fin 3 → X → F) {i j : Fin 3} (h : i < j) (x : X) :
    starRow w (fill p s) (double i j) x = w i * s j x - w j * s i x := by
  fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at h
  all_goals rw [starRow, Fin.sum_univ_three]
  · change w 0 * (↑(1 : ℤ) : F) * s 1 x + w 1 * (↑(-1 : ℤ) : F) * s 0 x +
      w 2 * (↑(1 : ℤ) : F) * 0 = w 0 * s 1 x - w 1 * s 0 x
    norm_num
    ring
  · change w 0 * (↑(1 : ℤ) : F) * s 2 x + w 1 * (↑(-1 : ℤ) : F) * 0 +
      w 2 * (↑(-1 : ℤ) : F) * s 0 x = w 0 * s 2 x - w 2 * s 0 x
    norm_num
    ring
  · change w 0 * (↑(1 : ℤ) : F) * 0 + w 1 * (↑(1 : ℤ) : F) * s 2 x +
      w 2 * (↑(-1 : ℤ) : F) * s 1 x = w 1 * s 2 x - w 2 * s 1 x
    norm_num
    ring

private theorem starRow_triple {X : Type*} (w : Fin 3 → F)
    (p : X → F) (s : Fin 3 → X → F) (x : X) :
    starRow w (fill p s) triple x = 0 := by
  norm_num [starRow, Fin.sum_univ_three, fill, starIndex, triple, flipSign,
    BalancedCriticalSpectrum.flip, Sensitivity.π, Fin.cases]

private def first (v : Q 9) : Q 6 := fun i => v (i.castAdd 3)
private def last (v : Q 9) : Q 3 := fun i => v (Fin.natAdd 6 i)

private theorem append_parts (v : Q 9) : Fin.append (first v) (last v) = v :=
  funext (Fin.addCases (fun i => by simp [first]) fun i => by simp [last])

/-- Allowed columns or rows of a fixed total parity, via their vacuum and singleton sets. -/
def starSet (P S : Set (Q 6)) : Set (Q 9) :=
  {v | match starIndex (last v) with
    | some none => first v ∈ P
    | some (some _) => first v ∈ S
    | none => False}

private theorem mem_star_append (P S : Set (Q 6)) (x : Q 6) (z : Q 3) :
    Fin.append x z ∈ starSet P S ↔
      match starIndex z with
      | some none => x ∈ P
      | some (some _) => x ∈ S
      | none => False := by
  have hx : first (Fin.append x z) = x := funext fun i => Fin.append_left _ _ _
  have hz : last (Fin.append x z) = z := funext fun i => Fin.append_right _ _ _
  change (match starIndex (last (Fin.append x z)) with
    | some none => first (Fin.append x z) ∈ P
    | some (some _) => first (Fin.append x z) ∈ S
    | none => False) ↔ _
  rw [hx, hz]

private theorem append_fill (P S : Set (Q 6)) (f : Q 9 → F)
    (hf : ∀ v ∉ starSet P S, f v = 0) (z : Q 3) :
    (fun x => f (Fin.append x z)) =
      fill (fun x => f (Fin.append x empty)) (fun i x => f (Fin.append x (single i))) z := by
  rcases star_cases z with rfl | ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩ | rfl
  · rfl
  · rw [fill_single]
  · rw [fill_double _ _ hij]
    funext x
    apply hf
    simp [mem_star_append, starIndex_double hij]
  · rw [fill_triple]
    funext x
    apply hf
    simp [mem_star_append, show starIndex triple = none from rfl]

private theorem sign_ne_zero (x : Q 6) : (baseSign x : F) ≠ 0 := by
  rcases baseSign_cases x with h | h <;> simp [h]

private theorem exterior_rows (a : Fin 6 → F) (w : Fin 3 → F)
    (P S : Set (Q 6)) (f : Q 9 → F) (p : Q 6 → F) (s : Fin 3 → Q 6 → F)
    (hf : ∀ z, (fun x => f (Fin.append x z)) = fill p s z) :
    (∀ v ∉ starSet P S, weightedLinear (Fin.append a w) f v = 0) ↔
      (∀ x ∉ P, baseAction a p x + (baseSign x : F) * (∑ i, w i * s i x) = 0) ∧
      (∀ i x, x ∉ S → baseAction a (s i) x + (baseSign x : F) * (w i * p x) = 0) ∧
      (∀ i j, i < j → ∀ x, w i * s j x = w j * s i x) := by
  have hr (x : Q 6) (z : Q 3) :
      weightedLinear (Fin.append a w) f (Fin.append x z) =
        baseAction a (fill p s z) x + (baseSign x : F) * starRow w (fill p s) z x := by
    rw [huang_row]
    rw [hf z, show (fun t y => f (Fin.append y t)) = fill p s from funext hf]
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun i x hx => ?_, fun i j hij x => ?_⟩
    · simpa only [hr, fill_empty, starRow_empty] using
        h (Fin.append x empty) (by
          simpa [mem_star_append, show starIndex empty = some none from rfl])
    · simpa only [hr, fill_single, starRow_single] using
        h (Fin.append x (single i)) (by simpa [mem_star_append, starIndex_single])
    · have hz := h (Fin.append x (double i j)) (by simp [mem_star_append, starIndex_double hij])
      rw [hr, fill_double _ _ hij, starRow_double w p s hij,
        map_zero, Pi.zero_apply, zero_add] at hz
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (sign_ne_zero x))
  · rintro ⟨h₀, h₁, h₂⟩ v hv
    rw [← append_parts v] at hv ⊢
    generalize first v = x at hv ⊢
    generalize last v = z at hv ⊢
    rw [mem_star_append] at hv
    rcases star_cases z with rfl | ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩ | rfl
    · simpa only [hr, fill_empty, starRow_empty] using h₀ x hv
    · rw [starIndex_single] at hv
      simpa only [hr, fill_single, starRow_single] using h₁ i x hv
    · simp [hr, fill_double _ _ hij, starRow_double w p s hij, h₂ i j hij x]
    · simp [hr, fill_triple, starRow_triple]

private def assemble (p : Q 6 → F) (s : Fin 3 → Q 6 → F) (v : Q 9) : F :=
  fill p s (last v) (first v)

private theorem assemble_append (p : Q 6 → F) (s : Fin 3 → Q 6 → F) (z : Q 3) :
    (fun x => assemble p s (Fin.append x z)) = fill p s z := by
  funext x
  have hx : first (Fin.append x z) = x := funext fun i => Fin.append_left _ _ _
  have hz : last (Fin.append x z) = z := funext fun i => Fin.append_right _ _ _
  rw [assemble, hx, hz]

private theorem assemble_supported (P S : Set (Q 6)) (p : Q 6 → F) (s : Fin 3 → Q 6 → F)
    (hp : ∀ x ∉ P, p x = 0) (hs : ∀ i x, x ∉ S → s i x = 0) :
    ∀ v ∉ starSet P S, assemble p s v = 0 := by
  intro v hv
  change ¬ (match starIndex (last v) with
    | some none => first v ∈ P
    | some (some _) => first v ∈ S
    | none => False) at hv
  unfold assemble fill
  cases h : starIndex (last v) with
  | none => rfl
  | some k =>
    cases k with
    | none => exact hp _ (by simpa [h] using hv)
    | some i => exact hs i _ (by simpa [h] using hv)

private theorem vac_support {P S : Set (Q 6)} {f : Q 9 → F}
    (hf : ∀ v ∉ starSet P S, f v = 0) : ∀ x ∉ P, f (Fin.append x empty) = 0 := by
  intro x hx
  exact hf _ (by simpa [mem_star_append, show starIndex empty = some none from rfl])

private theorem single_support {P S : Set (Q 6)} {f : Q 9 → F}
    (hf : ∀ v ∉ starSet P S, f v = 0) :
    ∀ i x, x ∉ S → f (Fin.append x (single i)) = 0 := by
  intro i x hx
  exact hf _ (by simpa [mem_star_append, starIndex_single])

private theorem pivot (w : Fin 3 → F) (hw : ∑ i, w i ^ 2 ≠ 0) :
    ∃ k, w k ≠ 0 := by
  by_contra! h
  exact hw (by simp [h])

private theorem common_slice (w : Fin 3 → F) (k : Fin 3) (hk : w k ≠ 0)
    (s : Fin 3 → Q 6 → F) (h : ∀ i j, i < j → ∀ x, w i * s j x = w j * s i x) :
    ∀ j, s j = w j • ((w k)⁻¹ • s k) := by
  intro j
  funext x
  have hj : w k * s j x = w j * s k x := by
    rcases lt_trichotomy k j with hlt | rfl | hgt
    · exact h _ _ hlt _
    · rfl
    · exact (h _ _ hgt _).symm
  change s j x = w j * ((w k)⁻¹ * s k x)
  apply mul_left_cancel₀ hk
  calc
    w k * s j x = w j * s k x := hj
    _ = w k * (w j * ((w k)⁻¹ * s k x)) := by
      rw [mul_left_comm (w k) (w j), ← mul_assoc (w k), mul_inv_cancel₀ hk, one_mul]

private theorem sum_scaled (w : Fin 3 → F) (q : Q 6 → F) (x : Q 6) :
    (∑ i, w i * (w i • q) x) = (∑ i, w i ^ 2) * q x := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.smul_apply, smul_eq_mul, pow_two, mul_assoc]

private theorem sign_sq (b : Bool) : (orientation b : F) * (orientation b : F) = 1 := by
  cases b <;> norm_num [orientation]

private def liftMap (a : Fin 6 → F) (w : Fin 3 → F) (b vacuum : Bool) :
    (Q 6 → F) →ₗ[F] (Q 9 → F) :=
  let P : Module.End F (Q 6 → F) := if vacuum then 1 else 0
  let S (i : Fin 3) : Module.End F (Q 6 → F) :=
    w i • (if vacuum then ((orientation b : F) / ∑ j, w j ^ 2) • baseAction a else 1)
  LinearMap.pi fun v => match starIndex (last v) with
    | some none => (LinearMap.proj (first v)).comp P
    | some (some i) => (LinearMap.proj (first v)).comp (S i)
    | none => 0

private theorem liftMap_singletons (a : Fin 6 → F) (w : Fin 3 → F) (b : Bool) (m : Q 6 → F) :
    liftMap a w b false m = assemble 0 (fun i => w i • m) := by
  funext v
  simp only [liftMap, LinearMap.pi_apply]
  unfold assemble fill
  cases h : starIndex (last v) with
  | none => rfl
  | some k => cases k <;> rfl

private theorem liftMap_vacuum (a : Fin 6 → F) (w : Fin 3 → F) (b : Bool) (m : Q 6 → F) :
    liftMap a w b true m =
      assemble m (fun i => w i • (((orientation b : F) / ∑ j, w j ^ 2) • baseAction a m)) := by
  funext v
  simp only [liftMap, LinearMap.pi_apply]
  unfold assemble fill
  cases h : starIndex (last v) with
  | none => rfl
  | some k => cases k <;> rfl

private theorem liftMap_injective (a : Fin 6 → F) (w : Fin 3 → F) (b vacuum : Bool)
    (hw : ∑ i, w i ^ 2 ≠ 0) : Function.Injective (liftMap a w b vacuum) := by
  intro m n h
  cases vacuum
  · obtain ⟨k, hk⟩ := pivot w hw
    rw [liftMap_singletons, liftMap_singletons] at h
    have h' := congrArg (fun f : Q 9 → F => fun x => f (Fin.append x (single k))) h
    rw [assemble_append, assemble_append, fill_single, fill_single] at h'
    funext x
    exact mul_left_cancel₀ hk (congrFun h' x)
  · rw [liftMap_vacuum, liftMap_vacuum] at h
    have h' := congrArg (fun f : Q 9 → F => fun x => f (Fin.append x empty)) h
    simpa only [assemble_append, fill_empty] using h'

private theorem singletons_mem_iff (a : Fin 6 → F) (w : Fin 3 → F) (b : Bool)
    (M B : Set (Q 6)) (hw : ∑ i, w i ^ 2 ≠ 0) (m : Q 6 → F) :
    liftMap a w b false m ∈ boundaryKernel (weightedLinear (Fin.append a w))
      (starSet ∅ M) (starSet M B) ↔ m ∈ boundaryKernel (baseAction a) M B := by
  obtain ⟨k, hk⟩ := pivot w hw
  rw [liftMap_singletons, mem_boundary, mem_boundary, exterior_rows a w _ _
    _ 0 (fun i => w i • m) (assemble_append _ _)]
  constructor
  · rintro ⟨hS, _, h₁, _⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have h := single_support hS k x hx
      change (fun y => assemble 0 (fun i => w i • m) (Fin.append y (single k))) x = 0 at h
      rw [assemble_append, fill_single] at h
      exact (mul_eq_zero.mp h).resolve_left hk
    · have h := h₁ k x hx
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hk
  · rintro ⟨hM, hB⟩
    refine ⟨assemble_supported _ _ _ _ (by simp) (fun i x hx => ?_), ?_, ?_, ?_⟩
    · simp [hM x hx]
    · intro x hx
      simp [hM x hx]
    · intro i x hx
      simp [hB x hx]
    · intro i j _ x
      change w i * (w j * m x) = w j * (w i * m x)
      ring

private theorem vacuum_mem (a : Fin 6 → F) (w : Fin 3 → F) (b : Bool)
    (M B : Set (Q 6)) (hB : ∀ x ∈ B, baseSign x = orientation (!b))
    (hw : ∑ i, w i ^ 2 ≠ 0) (m : Q 6 → F) (hm : m ∈ boundaryKernel (baseAction a) M B) :
    liftMap a w b true m ∈ boundaryKernel (weightedLinear (Fin.append a w))
      (starSet M B) (starSet ∅ M) := by
  obtain ⟨hmM, hmB⟩ := mem_boundary.mp hm
  let c : F := (orientation b : F) / ∑ j, w j ^ 2
  let q := c • baseAction a m
  rw [liftMap_vacuum, mem_boundary, exterior_rows a w _ _
    _ m (fun i => w i • q) (assemble_append _ _)]
  refine ⟨assemble_supported _ _ _ _ hmM (fun i x hx => ?_), ?_, ?_, ?_⟩
  · simp [hmB x hx]
  · intro x _
    rw [sum_scaled]
    by_cases hx : x ∈ B
    · rw [hB x hx, orientation_not, Int.cast_neg]
      change baseAction a m x + -(orientation b : F) *
        ((∑ j, w j ^ 2) * (c * baseAction a m x)) = 0
      have hc : (∑ j, w j ^ 2) * c = (orientation b : F) := by
        simp [c, div_eq_mul_inv, mul_left_comm, hw]
      rw [← mul_assoc _ c, hc, ← mul_assoc, neg_mul, sign_sq, neg_one_mul, add_neg_cancel]
    · simp [q, hmB x hx]
  · intro i x hx
    simp only [q, map_smul, Pi.smul_apply, smul_eq_mul, baseAction_square, hmM x hx, mul_zero,
      add_zero]
  · intro i j _ x
    change w i * (w j * q x) = w j * (w i * q x)
    ring

private theorem liftMap_surj (a : Fin 6 → F) (w : Fin 3 → F) (b vacuum : Bool)
    (M B : Set (Q 6)) (hM : ∀ x ∈ M, baseSign x = orientation b)
    (hB : ∀ x ∈ B, baseSign x = orientation (!b)) (hw : ∑ i, w i ^ 2 ≠ 0)
    (f : Q 9 → F)
    (hf : f ∈ if vacuum then
      boundaryKernel (weightedLinear (Fin.append a w)) (starSet M B) (starSet ∅ M)
      else boundaryKernel (weightedLinear (Fin.append a w)) (starSet ∅ M) (starSet M B)) :
    ∃ m ∈ boundaryKernel (baseAction a) M B, liftMap a w b vacuum m = f := by
  obtain ⟨k, hk⟩ := pivot w hw
  let p : Q 6 → F := fun x => f (Fin.append x empty)
  let s (i : Fin 3) : Q 6 → F := fun x => f (Fin.append x (single i))
  let q := (w k)⁻¹ • s k
  cases vacuum
  · obtain ⟨hfS, hfH⟩ := mem_boundary.mp hf
    have hs (z : Q 3) : (fun x => f (Fin.append x z)) = fill p s z :=
      append_fill _ _ f hfS z
    obtain ⟨_, _, h₂⟩ := (exterior_rows a w M B f p s hs).mp hfH
    have hs_eq := common_slice w k hk s h₂
    have hp : p = 0 := by funext x; exact vac_support hfS x (by simp)
    have heq : liftMap a w b false q = f := by
      rw [liftMap_singletons]
      funext v
      rw [← append_parts v]
      change (fun x => assemble 0 (fun i => w i • q) (Fin.append x (last v))) (first v) = _
      rw [assemble_append]
      rw [← hp, ← show s = (fun i => w i • q) from funext hs_eq, ← hs]
    exact ⟨q, (singletons_mem_iff a w b M B hw q).mp (heq ▸ hf), heq⟩
  · obtain ⟨hfS, hfH⟩ := mem_boundary.mp hf
    have hs (z : Q 3) : (fun x => f (Fin.append x z)) = fill p s z :=
      append_fill _ _ f hfS z
    obtain ⟨h₀, _, h₂⟩ := (exterior_rows a w ∅ M f p s hs).mp hfH
    have hs_eq := common_slice w k hk s h₂
    have hqB (x : Q 6) (hx : x ∉ B) : q x = 0 := by
      change (w k)⁻¹ * s k x = 0
      have hk0 : s k x = 0 := single_support hfS k x hx
      rw [hk0, mul_zero]
    have hpM (x : Q 6) (hx : x ∉ M) : p x = 0 := vac_support hfS x hx
    have hvac (x : Q 6) (hx : x ∉ M) :
        baseAction a p x + (baseSign x : F) * ((∑ i, w i ^ 2) * q x) = 0 := by
      have h := h₀ x (by simp)
      rw [funext hs_eq, sum_scaled] at h
      exact h
    have hpB (x : Q 6) (hx : x ∉ B) : baseAction a p x = 0 := by
      by_cases hm : x ∈ M
      · exact baseAction_zero_on_parity a b M hM p hpM x (hM x hm)
      · simpa [hqB x hx] using hvac x hm
    have hq : q = ((orientation b : F) / ∑ j, w j ^ 2) • baseAction a p := by
      funext x
      by_cases hx : x ∈ B
      · have hxM : x ∉ M := fun h => orientation_ne b ((hM x h).symm.trans (hB x hx))
        have h := hvac x hxM
        rw [hB x hx, orientation_not, Int.cast_neg] at h
        have he : baseAction a p x = (orientation b : F) * ((∑ j, w j ^ 2) * q x) := by
          linear_combination h
        change q x = ((orientation b : F) / ∑ j, w j ^ 2) * baseAction a p x
        rw [he]
        field_simp
        linear_combination -q x * sign_sq (F := F) b
      · simp [hqB x hx, hpB x hx]
    refine ⟨p, mem_boundary.mpr ⟨hpM, hpB⟩, ?_⟩
    rw [liftMap_vacuum]
    funext v
    rw [← append_parts v]
    change (fun x => assemble p _ (Fin.append x (last v))) (first v) = _
    rw [assemble_append]
    rw [← hq, ← show s = (fun i => w i • q) from funext hs_eq, ← hs]

/-- The usual cube parity of the six base coordinates. -/
def baseParity (x : Q 6) : Bool := ∑ i, x i

private theorem baseSign_parity (x : Q 6) : baseSign x = orientation (!baseParity x) := by
  simp only [baseParity, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change baseSign x = orientation (!(x 0 + (x 1 + (x 2 + (x 3 + (x 4 + x 5))))))
  cases h₀ : x 0 <;> cases h₁ : x 1 <;> cases h₂ : x 2 <;>
    cases h₃ : x 3 <;> cases h₄ : x 4 <;> cases h₅ : x 5 <;>
    simp only [baseSign, h₀, h₁, h₂, h₃, h₄, h₅] <;> decide

private theorem parity_append (x : Q 6) (z : Q 3) :
    parity (Fin.append x z) = baseParity x + (∑ i, z i) := by
  change (∑ j, Fin.append x z j) = _
  rw [Fin.sum_univ_add (a := 6) (b := 3)]
  simp [baseParity]

/-- Appending the three-axis vacuum toggles the base cube parity. -/
theorem parity_append_empty (x : Q 6) :
    parity (Fin.append x empty) = !baseParity x := by
  rw [parity_append, show (∑ i, empty i) = true from by decide]
  cases baseParity x <;> rfl

private theorem parity_single (x : Q 6) (i : Fin 3) :
    parity (Fin.append x (single i)) = baseParity x := by
  rw [parity_append]
  have hi : (∑ j, single i j) = false := by fin_cases i <;> decide
  rw [hi, show false = (0 : Bool) from rfl, add_zero]

/-- Retain the base middle class at the vacuum and both base classes at each singleton. -/
def starLift (M B : Set (Q 6)) : Set (Q 9) := starSet M (M ∪ B)

/-- The exterior-row kernel on one parity of the actual nine-axis Huang action. -/
abbrev parityBoundaryKernel (t : Fin 9 → F) (C : Set (Q 9)) (b : Bool) :
    Submodule F (Q 9 → F) :=
  boundaryKernel (weightedLinear t) (C ∩ {v | parity v = b}) (C ∩ {v | parity v = !b})

private theorem starLift_parities (M B : Set (Q 6)) (b : Bool)
    (hM : ∀ x ∈ M, baseParity x = !b) (hB : ∀ x ∈ B, baseParity x = b) :
    starLift M B ∩ {v | parity v = b} = starSet M B ∧
      starLift M B ∩ {v | parity v = !b} = starSet ∅ M := by
  have hp (v : Q 9) (c : Bool) : v ∈ starLift M B ∩ {v | parity v = c} ↔
      v ∈ starSet M (M ∪ B) ∧ parity v = c := Iff.rfl
  constructor <;> ext v <;> rw [← append_parts v, hp] <;>
    generalize first v = x <;> generalize last v = z <;>
    simp only [mem_star_append] <;>
    rcases star_cases z with rfl | ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩ | rfl
  · change (x ∈ M ∧ parity (Fin.append x empty) = b) ↔ x ∈ M
    exact ⟨And.left, fun h => ⟨h, by rw [parity_append_empty, hM x h]; simp⟩⟩
  · simp only [starIndex_single, parity_single, Set.mem_union]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact ((Bool.not_eq_self b).mp ((hM x h).symm.trans hx)).elim
      · exact h
    · exact fun h => ⟨Or.inr h, hB x h⟩
  · simp [starIndex_double hij]
  · simp [show starIndex triple = none from rfl]
  · change (x ∈ M ∧ parity (Fin.append x empty) = !b) ↔ False
    refine ⟨fun ⟨h, hx⟩ => (Bool.not_eq_self b).mp (hx.symm.trans ?_), False.elim⟩
    rw [parity_append_empty, hM x h, Bool.not_not]
  · simp only [starIndex_single, parity_single, Set.mem_union]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact h
      · exact ((Bool.not_eq_self b).mp (hx.symm.trans (hB x h))).elim
    · exact fun h => ⟨Or.inl h, hM x h⟩
  · simp [starIndex_double hij]
  · simp [show starIndex triple = none from rfl]

/-- Both lifted kernels are linearly isomorphic to the same six-axis exterior-row kernel.
The vacuum parity is `b`. The complementary parity has singleton slices only. -/
noncomputable def weightedStarLiftEquiv (a : Fin 6 → F) (w : Fin 3 → F)
    (M B : Set (Q 6)) (b : Bool)
    (hM : ∀ x ∈ M, baseParity x = !b) (hB : ∀ x ∈ B, baseParity x = b)
    (hw : ∑ i, w i ^ 2 ≠ 0) (vacuum : Bool) :
    boundaryKernel (baseAction a) M B ≃ₗ[F]
      parityBoundaryKernel (Fin.append a w) (starLift M B) (if vacuum then b else !b) := by
  have hsignM (x : Q 6) (hx : x ∈ M) : baseSign x = orientation b := by
    rw [baseSign_parity, hM x hx, Bool.not_not]
  have hsignB (x : Q 6) (hx : x ∈ B) : baseSign x = orientation (!b) := by
    rw [baseSign_parity, hB x hx]
  obtain ⟨hv, hs⟩ := starLift_parities M B b hM hB
  let K := parityBoundaryKernel (Fin.append a w) (starLift M B) (if vacuum then b else !b)
  have hK : K = if vacuum then
      boundaryKernel (weightedLinear (Fin.append a w)) (starSet M B) (starSet ∅ M)
      else boundaryKernel (weightedLinear (Fin.append a w)) (starSet ∅ M) (starSet M B) := by
    cases vacuum <;> simp [K, parityBoundaryKernel, hv, hs]
  have hmem (m : boundaryKernel (baseAction a) M B) : liftMap a w b vacuum m ∈ K := by
    rw [hK]
    cases vacuum
    · exact (singletons_mem_iff a w b M B hw m).mpr m.property
    · exact vacuum_mem a w b M B hsignB hw m m.property
  let L := LinearMap.codRestrict K
    ((liftMap a w b vacuum).comp (boundaryKernel (baseAction a) M B).subtype) hmem
  refine LinearEquiv.ofBijective L ⟨?_, ?_⟩
  · intro m n h
    apply Subtype.ext
    exact liftMap_injective a w b vacuum hw (congrArg Subtype.val h)
  · intro f
    obtain ⟨m, hm, heq⟩ :=
      liftMap_surj a w b vacuum M B hsignM hsignB hw f (hK ▸ f.property)
    exact ⟨⟨m, hm⟩, Subtype.ext heq⟩

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift.weightedStarLiftEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms weightedStarLiftEquiv

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift
