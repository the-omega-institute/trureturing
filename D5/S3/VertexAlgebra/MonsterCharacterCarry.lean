/- GID: D5/S3/VertexAlgebra/MonsterCharacterCarry
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/MonsterCharacterCarry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eight sign tables have a shared determinant character carry. -/

/-
proof_shape: classification_and_carry: content
escape_witness: The sign-table equations force the difference from the explicit cubic
  table to be symmetric and alternating, hence bilinear in both variables. Polarizing
  the cubic terms computes the common carry as a determinant; three independent
  coefficient evaluations give a bijection with all eight sign tables.
admission_basis: escape-witness
Direct frozen dependencies: none.
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.VertexAlgebra.MonsterCharacterCarry

abbrev F := ZMod 2
abbrev E := Fin 3 → F

/-- The rank-three finite sign table from the FC calculation. -/
def f0 (g h : E) : F :=
  g 0 * h 0 + g 1 * h 1 + g 2 * h 2 +
  g 0 * h 1 + g 0 * h 2 + g 1 * h 2 +
  g 0 * g 1 * h 2 + g 0 * g 2 * h 1 + g 1 * g 2 * h 0

def det3 (g h k : E) : F :=
  (g 1 * h 2 + h 1 * g 2) * k 0 +
  (g 0 * h 2 + h 0 * g 2) * k 1 +
  (g 0 * h 1 + h 0 * g 1) * k 2

def rows (g h k : E) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => if i = 0 then g j else if i = 1 then h j else k j

/-- Exactly the finite equations FC.1, without a VOA realization assumption. -/
structure IsSignTable (f : E → E → F) : Prop where
  zero_left : ∀ h, f 0 h = 0
  zero_right : ∀ g, f g 0 = 0
  right_add : ∀ g h k, f g (h + k) = f g h + f g k
  diagonal : ∀ g, g ≠ 0 → f g g = 1
  opposite : ∀ g h, g ≠ 0 → h ≠ 0 → g ≠ h → f g h + f h g = 1

structure IsAltBilinear (b : E → E → F) : Prop where
  left_add : ∀ g h k, b (g + h) k = b g k + b h k
  right_add : ∀ g h k, b g (h + k) = b g h + b g k
  left_smul : ∀ a g h, b (a • g) h = a * b g h
  right_smul : ∀ a g h, b g (a • h) = a * b g h
  diagonal : ∀ g, b g g = 0

private theorem classification (f : E → E → F) (hf : IsSignTable f) :
    ∃! b : E → E → F, IsAltBilinear b ∧
      ∀ g h, f g h = f0 g h + b g h := by
  have hf0 : IsSignTable f0 := by
    constructor <;> decide
  have htwo : (2 : F) = 0 := by decide
  let b : E → E → F := fun g h => f g h + f0 g h
  have hr : ∀ g h k, b g (h + k) = b g h + b g k := by
    intro g h k
    simp only [b, hf.right_add, hf0.right_add]
    ring
  have hsum : ∀ g h, f g h + f h g = f0 g h + f0 h g := by
    intro g h
    by_cases hg : g = 0
    · subst g
      simp [hf.zero_left, hf.zero_right, hf0.zero_left, hf0.zero_right]
    by_cases hh : h = 0
    · subst h
      simp [hf.zero_left, hf.zero_right, hf0.zero_left, hf0.zero_right]
    by_cases hgh : g = h
    · subst h
      ring_nf
      simp [htwo]
    · rw [hf.opposite g h hg hh hgh, hf0.opposite g h hg hh hgh]
  have hsym : ∀ g h, b g h = b h g := by
    intro g h
    have hs := hsum g h
    dsimp [b]
    have hz : (f g h + f0 g h) + (f h g + f0 h g) = 0 := by
      calc
        _ = (f g h + f h g) + (f0 g h + f0 h g) := by ring
        _ = (f0 g h + f0 h g) + (f0 g h + f0 h g) := by rw [hs]
        _ = 0 := CharTwo.add_self_eq_zero _
    exact (add_eq_zero_iff_eq_neg.mp hz).trans (CharTwo.neg_eq _)
  have hl : ∀ g h k, b (g + h) k = b g k + b h k := by
    intro g h k
    rw [hsym, hr, hsym k g, hsym k h]
  have hd : ∀ g, b g g = 0 := by
    intro g
    by_cases hg : g = 0
    · subst g
      simp [b, hf.zero_left, hf0.zero_left]
    · change f g g + f0 g g = 0
      rw [hf.diagonal g hg, hf0.diagonal g hg]
      decide
  have hls : ∀ a g h, b (a • g) h = a * b g h := by
    intro a g h
    have hcases : ∀ z : F, z = 0 ∨ z = 1 := by decide
    rcases hcases a with rfl | rfl
    · simp [b, hf.zero_left, hf0.zero_left]
    · simp
  have hrs : ∀ a g h, b g (a • h) = a * b g h := by
    intro a g h
    have hcases : ∀ z : F, z = 0 ∨ z = 1 := by decide
    rcases hcases a with rfl | rfl
    · simp [b, hf.zero_right, hf0.zero_right]
    · simp
  have hrec : ∀ g h, f g h = f0 g h + b g h := by
    intro g h
    dsimp [b]
    ring_nf
    simp [htwo]
  refine ⟨b, ⟨⟨hl, hr, hls, hrs, hd⟩, hrec⟩, ?_⟩
  intro c hc
  funext g h
  exact add_left_cancel ((hc.2 g h).symm.trans (hrec g h))

private theorem classification_and_carry_core (f : E → E → F) (hf : IsSignTable f) :
    (∀ b : E → E → F, IsAltBilinear b →
      IsSignTable (fun g h => f0 g h + b g h)) ∧
    (∃! b : E → E → F, IsAltBilinear b ∧
      ∀ g h, f g h = f0 g h + b g h) ∧
    (∀ g h k, f g k + f h k + f (g + h) k = Matrix.det (rows g h k)) := by
  have hclass := classification f hf
  refine ⟨?_, hclass, ?_⟩
  · intro b hb
    have hf0 : IsSignTable f0 := by constructor <;> decide
    have hzeroLeft : ∀ h, b 0 h = 0 := by
      intro h
      have hz := hb.left_add (0 : E) 0 h
      simpa [CharTwo.add_self_eq_zero] using hz
    have hzeroRight : ∀ g, b g 0 = 0 := by
      intro g
      have hz := hb.right_add g (0 : E) 0
      simpa [CharTwo.add_self_eq_zero] using hz
    have hsym : ∀ g h, b g h = b h g := by
      intro g h
      have hz := hb.diagonal (g + h)
      simp only [hb.left_add, hb.right_add, hb.diagonal, zero_add, add_zero] at hz
      exact (add_eq_zero_iff_eq_neg.mp hz).trans (CharTwo.neg_eq _)
    constructor
    · intro h
      simp [hf0.zero_left, hzeroLeft]
    · intro g
      simp [hf0.zero_right, hzeroRight]
    · intro g h k
      simp only [hf0.right_add, hb.right_add]
      ring
    · intro g hg
      simp [hf0.diagonal g hg, hb.diagonal]
    · intro g h hg hh hgh
      calc
        (f0 g h + b g h) + (f0 h g + b h g) =
            (f0 g h + f0 h g) + (b g h + b h g) := by ring
        _ = 1 := by
          rw [hf0.opposite g h hg hh hgh, hsym g h]
          simp [CharTwo.add_self_eq_zero]
  intro g h k
  obtain ⟨b, ⟨hb, hrec⟩, _⟩ := hclass
  have hbase : f0 g k + f0 h k + f0 (g + h) k = det3 g h k := by
    simp only [f0, det3, Pi.add_apply]
    ring_nf
    have htwo : (2 : F) = 0 := by decide
    simp only [htwo, mul_zero, add_zero, zero_add]
  have hdet : det3 g h k = Matrix.det (rows g h k) := by
    simp [Matrix.det_fin_three, rows, det3, CharTwo.sub_eq_add]
    ring
  calc
    f g k + f h k + f (g + h) k =
        (f0 g k + f0 h k + f0 (g + h) k) +
        (b g k + b h k + b (g + h) k) := by
          rw [hrec g k, hrec h k, hrec (g + h) k]
          ring
    _ = det3 g h k := by
      rw [hbase, hb.left_add g h k]
      simp [CharTwo.add_self_eq_zero]
    _ = Matrix.det (rows g h k) := hdet

private def e0 : E := ![1, 0, 0]
private def e1 : E := ![0, 1, 0]
private def e2 : E := ![0, 0, 1]

private theorem vector_decomp (g : E) :
    g = g 0 • e0 + g 1 • e1 + g 2 • e2 := by
  funext i
  fin_cases i <;> simp [e0, e1, e2, Pi.add_apply]

private def coeffForm (a c d : F) (g h : E) : F :=
  (g 0 * h 1 + g 1 * h 0) * a +
  (g 0 * h 2 + g 2 * h 0) * c +
  (g 1 * h 2 + g 2 * h 1) * d

private theorem coeffForm_alt (a c d : F) : IsAltBilinear (coeffForm a c d) := by
  constructor
  · intro g h k
    simp only [coeffForm, Pi.add_apply]
    ring
  · intro g h k
    simp only [coeffForm, Pi.add_apply]
    ring
  · intro t g h
    simp only [coeffForm, Pi.smul_apply, smul_eq_mul]
    ring
  · intro t g h
    simp only [coeffForm, Pi.smul_apply, smul_eq_mul]
    ring
  · intro g
    simp only [coeffForm]
    have htwo : (2 : F) = 0 := by decide
    ring_nf
    simp [htwo]

private theorem alt_reconstruct (b : E → E → F) (hb : IsAltBilinear b) :
    b = coeffForm (b e0 e1) (b e0 e2) (b e1 e2) := by
  have hsym : ∀ g h, b g h = b h g := by
    intro g h
    have hz := hb.diagonal (g + h)
    simp only [hb.left_add, hb.right_add, hb.diagonal, zero_add, add_zero] at hz
    exact (add_eq_zero_iff_eq_neg.mp hz).trans (CharTwo.neg_eq _)
  funext g h
  calc
    b g h = b (g 0 • e0 + g 1 • e1 + g 2 • e2)
        (h 0 • e0 + h 1 • e1 + h 2 • e2) := by
          rw [← vector_decomp g, ← vector_decomp h]
    _ = coeffForm (b e0 e1) (b e0 e2) (b e1 e2) g h := by
      simp only [hb.left_add, hb.right_add, hb.left_smul, hb.right_smul]
      rw [hb.diagonal e0, hb.diagonal e1, hb.diagonal e2,
        hsym e1 e0, hsym e2 e0, hsym e2 e1]
      simp only [coeffForm, mul_zero, add_zero, zero_add]
      ring

private def Alt := {b : E → E → F // IsAltBilinear b}

private def coeffEquiv : (Fin 3 → F) ≃ Alt where
  toFun p := ⟨coeffForm (p 0) (p 1) (p 2), coeffForm_alt _ _ _⟩
  invFun b := ![b.1 e0 e1, b.1 e0 e2, b.1 e1 e2]
  left_inv p := by
    funext i
    fin_cases i <;> simp [coeffForm, e0, e1, e2]
  right_inv b := by
    apply Subtype.ext
    exact (alt_reconstruct b.1 b.2).symm

/-- The finite set of all functions satisfying FC.1. -/
def Table := {f : E → E → F // IsSignTable f}

private noncomputable def tableEquiv : Table ≃ Alt where
  toFun f :=
    ⟨(classification_and_carry_core f.1 f.2).2.1.choose,
      (classification_and_carry_core f.1 f.2).2.1.choose_spec.1.1⟩
  invFun b := by
    have hf0 : IsSignTable f0 := by constructor <;> decide
    exact ⟨fun g h => f0 g h + b.1 g h,
      (classification_and_carry_core f0 hf0).1 b.1 b.2⟩
  left_inv f := by
    apply Subtype.ext
    funext g h
    exact ((classification_and_carry_core f.1 f.2).2.1.choose_spec.1.2 g h).symm
  right_inv b := by
    apply Subtype.ext
    have hf0 : IsSignTable f0 := by constructor <;> decide
    exact ((classification_and_carry_core (fun g h => f0 g h + b.1 g h)
      ((classification_and_carry_core f0 hf0).1 b.1 b.2)).2.1.choose_spec.2
        b.1 ⟨b.2, by intros; rfl⟩).symm

private noncomputable instance : Fintype Alt :=
  Fintype.ofEquiv (Fin 3 → F) coeffEquiv

private noncomputable instance : Fintype Table :=
  Fintype.ofEquiv Alt tableEquiv.symm

private theorem table_card : Nat.card Table = 8 := by
  classical
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card Table = Fintype.card Alt := Fintype.card_congr tableEquiv
    _ = Fintype.card (Fin 3 → F) := Fintype.card_congr coeffEquiv.symm
    _ = 8 := by decide

/-- The solutions of FC.1 are precisely eight alternating-bilinear corrections
of the explicit table, and all have the same determinant character carry. -/
theorem classification_and_carry (f : E → E → F) (hf : IsSignTable f) :
    (∀ b : E → E → F, IsAltBilinear b →
      IsSignTable (fun g h => f0 g h + b g h)) ∧
    (∃! b : E → E → F, IsAltBilinear b ∧
      ∀ g h, f g h = f0 g h + b g h) ∧
    (∀ g h k, f g k + f h k + f (g + h) k = Matrix.det (rows g h k)) ∧
    Nat.card Table = 8 ∧
    (∀ g h k x, Matrix.det (rows (g + h) k x) =
      Matrix.det (rows g k x) + Matrix.det (rows h k x)) ∧
    (∀ g h k x, Matrix.det (rows g (h + k) x) =
      Matrix.det (rows g h x) + Matrix.det (rows g k x)) ∧
    (∀ g x, Matrix.det (rows g g x) = 0) ∧
    (∀ g h k x,
      (f g x + f h x + f (g + h) x) +
        (f (g + h) x + f k x + f (g + h + k) x) =
      (f h x + f k x + f (h + k) x) +
        (f g x + f (h + k) x + f (g + (h + k)) x)) ∧
    (∀ g h, g ≠ 0 → h ≠ 0 → g ≠ h →
      ∃ k, Matrix.det (rows g h k) = 1) := by
  rcases classification_and_carry_core f hf with ⟨hconverse, hclass, hcarry⟩
  refine ⟨hconverse, hclass, hcarry, table_card, ?_, ?_, ?_, ?_, ?_⟩
  · intro g h k x
    simp [Matrix.det_fin_three, rows, Pi.add_apply, CharTwo.sub_eq_add]
    ring
  · intro g h k x
    simp [Matrix.det_fin_three, rows, Pi.add_apply, CharTwo.sub_eq_add]
    ring
  · intro g x
    simp [Matrix.det_fin_three, rows, CharTwo.sub_eq_add]
    ring_nf
    have htwo : (2 : F) = 0 := by decide
    simp [htwo]
  · intro g h k x
    have htwo : (2 : F) = 0 := by decide
    rw [add_assoc g h k]
    ring_nf
    simp [htwo]
  · decide

end D5.S3.VertexAlgebra.MonsterCharacterCarry
