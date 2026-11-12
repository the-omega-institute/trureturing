/- Source-only, uncompiled, unaccepted. The arbitrary-input U supplier is
   itself a pinned candidate, and is not promoted to native acceptance here.
   This file proves the coefficient diagram on the original U, including
   rational off-coset coefficients and finite presentations of both inputs.
   It does not assert any module/field hexagon or any five-field pentagon. -/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleBraiding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleBraidingField
attribute [local instance] Classical.propDecidable
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeDiscriminantTheta
open LatticeCosetCanonicalIntertwiner LatticeDualCosetConformal LatticeDualCosetModule
open LatticeSugawaraCurrents LatticeActualConformalState
open FullJacobiCurrentTransport FullJacobiIntertwiner
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleUniversalField ActualWeakModuleBraiding LatticeCosetRationalSkew
open private gram_left gram_right finite_extension bilinear_ext sumFamily presentation_support from
  D5.S3.VertexAlgebra.Modules.ActualWeakModuleUniversalField
open private shift_symmetric from D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalLaws

universe u v
variable {D : LatticeData} {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)
variable (hD : (gramReal D).PosDef)

/-- Powers of the actual target omega-zero mode on the literal insertion. -/
theorem tag_translation_pow (c d : Discriminant D)
    (x : Multiplicity A c) (y : Multiplicity B d) (j : ℕ) (v : Carrier D) :
    (translation (targetModule A B) hD ^ j) (tag A B c d x y v) =
      tag A B c d x y
        ((moduleL D (representative D c + representative D d) (inverseGram hD) (-1) ^ j) v) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    change FullJacobiCurrentTransport.mode (targetModule A B) (omega D (inverseGram hD)) 0 _ = _
    rw [target_action_tag]
    rfl

/-- Exact elementary canonical diagram, at every RAW rational exponent. -/
theorem canonical_diagram (a b : Charge D) (u v : Carrier D) (q : ℚ) :
    Omega D (1 : Matrix _ _ ℤ) a b •
      (intertwiner D (1 : Matrix _ _ ℤ) a b u).coeff q v = ∑ᶠ j : ℕ,
      (Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
        (moduleL D (a+b) (inverseGram hD) (-1) ^ j)
          ((intertwiner D (1 : Matrix _ _ ℤ) b a v).coeff (q-(j : ℚ)) u) := by
  have h := turn_coeff D (1 : Matrix _ _ ℤ) hD (inverseGram hD)
    (gram_left hD) (gram_right hD) true a b u v q
  rw [turn_eq D (1 : Matrix _ _ ℤ) hD (inverseGram hD)
    (gram_left hD) (gram_right hD)] at h
  simpa only [↓reduceIte, one_mul, Matrix.one_mulVec, LinearMap.smul_apply] using h

/-- A concrete bilinear family; the swapped canonical inputs are literal. -/
def modelTurnFamily (q : ℚ) (j : ℕ) :
    Model A →ₗ[ℂ] Model B →ₗ[ℂ] P B A :=
  (Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
    ((modelMode B A (-(q-(j : ℚ))-1)).flip.compr₂
      (translation (targetModule B A) hD ^ j))

theorem modelTurnFamily_apply (q : ℚ) (j : ℕ) (s : Model A) (t : Model B) :
    modelTurnFamily A B hD q j s t =
      (Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
        (translation (targetModule B A) hD ^ j) ((modelField B A t).coeff (q-(j : ℚ)) s) := by
  change _ • _ ((modelField B A t).coeff (-(-(q-(j : ℚ))-1)-1) s) = _
  rw [show -(-(q-(j : ℚ))-1)-1 = q-(j : ℚ) by ring]

/-- The target translation acts on the original Carrier factor, with the
    true sector-sum equality and no representative normalization. -/
theorem modelTurn_elementary (c d : Discriminant D)
    (u v : Carrier D) (x : Multiplicity A c) (y : Multiplicity B d) (q : ℚ) (j : ℕ) :
    modelTurnFamily A B hD q j (elementary A c u x) (elementary B d v y) =
      tag B A d c y x
        ((Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
          (moduleL D (representative D c + representative D d) (inverseGram hD) (-1) ^ j)
            ((C d c v).coeff (q-(j : ℚ)) u)) := by
  rw [modelTurnFamily_apply, modelField_elementary_coeff, tag_translation_pow, map_smul]
  rw [add_comm (representative D c) (representative D d)]

theorem modelTurn_elementary_finite (c d : Discriminant D)
    (u v : Carrier D) (x : Multiplicity A c) (y : Multiplicity B d) (q : ℚ) :
    Function.HasFiniteSupport (fun j : ℕ =>
      modelTurnFamily A B hD q j (elementary A c u x) (elementary B d v y)) := by
  have hf := turn_terms_finite D (1 : Matrix _ _ ℤ) (inverseGram hD) true
    (representative D c) (representative D d) u v q
  simp only [↓reduceIte, one_mul, Matrix.one_mulVec] at hf
  apply hf.subset
  intro j hj hz
  apply hj
  rw [modelTurn_elementary, hz, map_zero]

/-- Every evaluated convolution is finite by the ACTUAL two finite tensor
    presentations. This reuses the pinned source's finite-extension proof. -/
theorem modelTurn_finite (q : ℚ) (s : Model A) (t : Model B) :
    Function.HasFiniteSupport (fun j => modelTurnFamily A B hD q j s t) :=
  finite_extension A B (modelTurnFamily A B hD q)
    (fun c d u v x y => modelTurn_elementary_finite A B hD c d u v x y q) s t

/-- Elementary insertion consumes the FULL rational canonical comparison.
    Each map_finsum is justified by the particular canonical pair's support. -/
theorem model_diagram_elementary (c d : Discriminant D)
    (u v : Carrier D) (x : Multiplicity A c) (y : Multiplicity B d) (q : ℚ) :
    braid A B ((modelField A B (elementary A c u x)).coeff q (elementary B d v y)) =
      ∑ᶠ j : ℕ, modelTurnFamily A B hD q j (elementary A c u x) (elementary B d v y) := by
  rw [modelField_elementary_coeff, braid_tag]
  have hf := turn_terms_finite D (1 : Matrix _ _ ℤ) (inverseGram hD) true
    (representative D c) (representative D d) u v q
  simp only [↓reduceIte, one_mul, Matrix.one_mulVec] at hf
  calc
    _ = tag B A d c y x (phase (D := D) c d • (C c d u).coeff q v) :=
      (map_smul (tag B A d c y x) _ _).symm
    _ = tag B A d c y x (∑ᶠ j : ℕ,
        (Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
          (moduleL D (representative D c + representative D d) (inverseGram hD) (-1) ^ j)
            ((C d c v).coeff (q-(j : ℚ)) u)) := by
      exact congrArg (tag B A d c y x)
        (canonical_diagram hD (representative D c) (representative D d) u v q)
    _ = _ := by
      rw [map_finsum (tag B A d c y x) hf]
      apply finsum_congr
      intro j
      exact (modelTurn_elementary A B hD c d u v x y q j).symm

/-- The full comparison on classified vectors, by algebraic bilinear
    extensionality only AFTER the actual finsum is a bilinear map. -/
theorem model_diagram (q : ℚ) (s : Model A) (t : Model B) :
    braid A B ((modelField A B s).coeff q t) =
      ∑ᶠ j : ℕ, modelTurnFamily A B hD q j s t := by
  have he : (modelMode A B (-q-1)).compr₂ (braid A B) =
      sumFamily A B (modelTurnFamily A B hD q) (modelTurn_finite A B hD q) := by
    apply bilinear_ext A B
    intro c d u v x y
    change braid A B ((modelField A B (elementary A c u x)).coeff (-(-q-1)-1)
      (elementary B d v y)) = _
    rw [show -(-q-1)-1 = q by ring]
    exact model_diagram_elementary A B hD c d u v x y q
  have hv := congrArg (fun f : Model A →ₗ[ℂ] Model B →ₗ[ℂ] P B A => f s t) he
  change braid A B ((modelField A B s).coeff (-(-q-1)-1) t) = _ at hv
  simpa only [show -(-q-1)-1 = q by ring] using hv

/-- The exact original-U diagram, every rational raw exponent and every
    original pair of input vectors. The named diagram uses Omega, not its inverse. -/
theorem U_braiding (x : X) (y : Y) (q : ℚ) :
    braid A B ((U A B hD x).coeff q y) = ∑ᶠ j : ℕ,
      (Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
        (translation (targetModule B A) hD ^ j) ((U B A hD y).coeff (q-(j : ℚ)) x) := by
  have h := model_diagram A B hD q
    ((classificationEquiv A hD).symm x) ((classificationEquiv B hD).symm y)
  simp_rw [modelTurnFamily_apply] at h
  exact h

theorem U_braiding_finite (x : X) (y : Y) (q : ℚ) :
    Function.HasFiniteSupport (fun j : ℕ =>
      (Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
        (translation (targetModule B A) hD ^ j) ((U B A hD y).coeff (q-(j : ℚ)) x)) := by
  have h := modelTurn_finite A B hD q
    ((classificationEquiv A hD).symm x) ((classificationEquiv B hD).symm y)
  simp_rw [modelTurnFamily_apply] at h
  exact h

/-- An explicit finite-union witness for the reversal terms of ORIGINAL x,y.
    Each elementary pair in this union has the cutoff turn_terms_support;
    no bound is chosen over a family of intermediate translated vectors. -/
theorem U_braiding_support (x : X) (y : Y) (q : ℚ) :
    ∃ (l : List (ElementaryData A)) (k : List (ElementaryData B)),
      (classificationEquiv A hD).symm x = (l.map (elementaryValue A)).sum ∧
      (classificationEquiv B hD).symm y = (k.map (elementaryValue B)).sum ∧
      Function.support (fun j : ℕ =>
        (Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
          (translation (targetModule B A) hD ^ j) ((U B A hD y).coeff (q-(j : ℚ)) x)) ⊆
        ⋃ e ∈ (l.toFinset : Set (ElementaryData A)),
          ⋃ f ∈ (k.toFinset : Set (ElementaryData B)),
            Function.support (fun j => modelTurnFamily A B hD q j
              (elementaryValue A e) (elementaryValue B f)) := by
  classical
  obtain ⟨l,hl⟩ := elementary_presentation A ((classificationEquiv A hD).symm x)
  obtain ⟨k,hk⟩ := elementary_presentation B ((classificationEquiv B hD).symm y)
  refine ⟨l,k,hl,hk,?_⟩
  have h := presentation_support A B (modelTurnFamily A B hD q) l k
  rw [← hl, ← hk] at h
  simpa only [modelTurnFamily_apply] using h

/-- Original U is zero outside the finite union of literal exponent cosets
    of ANY chosen finite classified presentations of its two inputs. -/
theorem U_off_cosets (x : X) (y : Y) (q : ℚ)
    (l : List (ElementaryData A)) (k : List (ElementaryData B))
    (hl : (classificationEquiv A hD).symm x = (l.map (elementaryValue A)).sum)
    (hk : (classificationEquiv B hD).symm y = (k.map (elementaryValue B)).sum)
    (hq : ∀ e ∈ l, ∀ f ∈ k, q ∉ Set.range (exponentEmbedding
      (LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) (representative D e.1) (representative D f.1)))) :
    (U A B hD x).coeff q y = 0 := by
  change (modelField A B ((classificationEquiv A hD).symm x)).coeff q
    ((classificationEquiv B hD).symm y) = 0
  rw [hl,hk,modelField_list_coeff]
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hz
  rw [field_coeff_off D (1 : Matrix _ _ ℤ) (representative D e.1)
    (representative D f.1) e.2.1 f.2.1 q (hq e he f hf), map_zero]

/-- Every shifted reversed coefficient itself vanishes off the original
    finite union. This is a termwise readback, independent of cancellation. -/
theorem U_reversed_coeff_off_cosets (x : X) (y : Y) (q : ℚ)
    (l : List (ElementaryData A)) (k : List (ElementaryData B))
    (hl : (classificationEquiv A hD).symm x = (l.map (elementaryValue A)).sum)
    (hk : (classificationEquiv B hD).symm y = (k.map (elementaryValue B)).sum)
    (hq : ∀ e ∈ l, ∀ f ∈ k, q ∉ Set.range (exponentEmbedding
      (LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) (representative D e.1) (representative D f.1))))
    (j : ℕ) : (U B A hD y).coeff (q-(j : ℚ)) x = 0 := by
  apply U_off_cosets B A hD y x (q-(j : ℚ)) k l hk hl
  intro f hf e he
  rintro ⟨n,hn⟩
  apply hq e he f hf
  refine ⟨n+(j : ℤ), ?_⟩
  dsimp [exponentEmbedding] at hn ⊢
  rw [shift_symmetric D (1 : Matrix _ _ ℤ) (representative D e.1) (representative D f.1)]
  push_cast
  linarith

/-- Both sides of the original diagram vanish off that finite union. -/
theorem U_braiding_off_cosets (x : X) (y : Y) (q : ℚ)
    (l : List (ElementaryData A)) (k : List (ElementaryData B))
    (hl : (classificationEquiv A hD).symm x = (l.map (elementaryValue A)).sum)
    (hk : (classificationEquiv B hD).symm y = (k.map (elementaryValue B)).sum)
    (hq : ∀ e ∈ l, ∀ f ∈ k, q ∉ Set.range (exponentEmbedding
      (LatticeCosetCanonicalIntertwiner.shift D (1 : Matrix _ _ ℤ) (representative D e.1) (representative D f.1)))) :
    (∑ᶠ j : ℕ,
      (Complex.exp (Real.pi * Complex.I * ((q : ℂ)-(j : ℂ))) / (j.factorial : ℂ)) •
        (translation (targetModule B A) hD ^ j) ((U B A hD y).coeff (q-(j : ℚ)) x)) = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  rw [U_reversed_coeff_off_cosets A B hD x y q l k hl hk hq j, map_zero, smul_zero]

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleBraidingField
