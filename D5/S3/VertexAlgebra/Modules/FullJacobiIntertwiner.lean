/- GID: D5/S3/VertexAlgebra/Modules/FullJacobiIntertwiner
   generality: I
   mirror-B: none(source-only-candidate)
   mirror-E: none(source-only-candidate)
   anchors: []
   utility: Generator intertwiners extend to every actual source state.
   status: UNCOMPILED. No native evidence is asserted for this file.
-/
import D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport
import Mathlib.Algebra.FiniteSupport.Basic

/-
The imported FullJacobiCurrentTransport must be the sealed e536d048 adapter.
Source products, current recovery and finite negative generation are the
original suppliers, with their original attribution and conventions.
The source-submodule argument uses the two independently finite iterate
families, not a formal interchange of infinite sums.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Modules.FullJacobiIntertwiner
open FullJacobiCurrentTransport
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeAllStateField
open FieldNormalProduct
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section
universe u v

variable {D : LatticeData} {M : Type u} {N : Type v}
variable [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

theorem mode_state_add (J : FullJacobiLatticeModule D M)
    (a b : Carrier D) (n : ℤ) :
    mode J (a + b) n = mode J a n + mode J b n := by
  simp [mode]

theorem mode_state_smul (J : FullJacobiLatticeModule D M)
    (c : ℂ) (a : Carrier D) (n : ℤ) :
    mode J (c • a) n = c • mode J a n := by
  simp [mode]

/-- A source submodule, with all integer modes and all input vectors. -/
def intertwiningStates (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) (f : M →ₗ[ℂ] N) :
    Submodule ℂ (Carrier D) where
  carrier := {a | ∀ (n : ℤ) (x : M), f (mode J a n x) = mode K a n (f x)}
  zero_mem' := by intro n x; simp [mode]
  add_mem' := by
    intro a b ha hb n x
    simp only [mode_state_add, LinearMap.add_apply, map_add, ha n x, hb n x]
  smul_mem' := by
    intro c a ha n x
    simp only [mode_state_smul, LinearMap.smul_apply, map_smul, ha n x]

/-- Actual iterate closure: each finite source family is mapped separately. -/
theorem intertwiningStates_product (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) (f : M →ₗ[ℂ] N)
    (a b : Carrier D) (ha : a ∈ intertwiningStates J K f)
    (hb : b ∈ intertwiningStates J K f) (r : ℤ) :
    sourceProduct D a r b ∈ intertwiningStates J K f := by
  classical
  intro n x
  obtain ⟨hF, hS, hJ⟩ := module_iterate J a b x r n
  obtain ⟨_, _, hK⟩ := module_iterate K a b (f x) r n
  have first (i : ℕ) : f (jacobiFirst J.stateField a b x 0 n r i) =
      jacobiFirst K.stateField a b (f x) 0 n r i := by
    change f (_ • mode J a _ (mode J b _ x)) =
      _ • mode K a _ (mode K b _ (f x))
    rw [map_smul, ha, hb]
  have second (i : ℕ) : f (jacobiSecond J.stateField a b x 0 n r i) =
      jacobiSecond K.stateField a b (f x) 0 n r i := by
    change f (_ • (StateFieldResidueReconstruction.epsilon r •
      mode J b _ (mode J a _ x))) =
      _ • (StateFieldResidueReconstruction.epsilon r •
        mode K b _ (mode K a _ (f x)))
    rw [map_smul, map_smul, hb, ha]
  rw [hJ, map_sub, map_finsum f hF, map_finsum f hS, hK]
  exact congrArg₂ (fun x y : N => x - y)
    (finsum_congr first) (finsum_congr second)

/-- Intertwining actual current and exponential states forces intertwining
every state. Positive definiteness is used only by finite_negative_generation.
Neither carrier is required to be nonzero or graded. -/
theorem all_modes_of_generators (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) (f : M →ₗ[ℂ] N)
    (positiveG : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hcurrent : ∀ (i : Fin D.rank) (n : ℤ) (x : M),
      f (current J i n x) = current K i n (f x))
    (hexponential : ∀ (β : Charge D) (n : ℤ) (x : M),
      f (mode J (Finsupp.single β (1 : Oscillator D)) n x) =
        mode K (Finsupp.single β (1 : Oscillator D)) n (f x))
    (a : Carrier D) (n : ℤ) (x : M) :
    f (mode J a n x) = mode K a n (f x) := by
  classical
  let S := intertwiningStates J K f
  have hc (i : Fin D.rank) : currentState D i ∈ S := hcurrent i
  have he (β : Charge D) : Finsupp.single β (1 : Oscillator D) ∈ S :=
    hexponential β
  obtain ⟨B, hB⟩ := finite_negative_generation D positiveG
  have hw (w : List (Generator D B × ℕ)) : negativeWord D B w ∈ S := by
    induction w with
    | nil => simpa only [negativeWord] using he 0
    | cons z w ih =>
      rcases z with ⟨g,k⟩
      cases g with
      | inl i =>
        have h := intertwiningStates_product J K f _ _ (hc i) ih (-(k : ℤ) - 1)
        simpa only [negativeWord, generatingField, sourceProduct, current_state_field]
          using h
      | inr β =>
        have h := intertwiningStates_product J K f _ _ (he β.val) ih (-(k : ℤ) - 1)
        simpa only [negativeWord, generatingField, sourceProduct, stateField_ground]
          using h
  have hspan : negativeWordSpan D B ≤ S := Submodule.span_le.mpr (by
    rintro b ⟨w, rfl⟩
    exact hw w)
  have ha : a ∈ S := hspan (by rw [hB]; trivial)
  exact ha n x

/-- Morphisms for the actual tensor and direct-sum constructions below. -/
structure ModuleHom (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) where
  linearMap : M →ₗ[ℂ] N
  intertwines : ∀ (a : Carrier D) (n : ℤ) (x : M),
    linearMap (mode J a n x) = mode K a n (linearMap x)

def ModuleHom.ofGenerators (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) (f : M →ₗ[ℂ] N)
    (positiveG : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hcurrent : ∀ (i : Fin D.rank) (n : ℤ) (x : M),
      f (current J i n x) = current K i n (f x))
    (hexponential : ∀ (β : Charge D) (n : ℤ) (x : M),
      f (mode J (Finsupp.single β (1 : Oscillator D)) n x) =
        mode K (Finsupp.single β (1 : Oscillator D)) n (f x)) : ModuleHom J K where
  linearMap := f
  intertwines := all_modes_of_generators J K f positiveG hcurrent hexponential

/- The remaining helpers are consumed by both actual module constructions.
JacobiAt is a proposition, not a replacement module record. It retains all
three separate finite supports; its equality is equivalent to the literal
original equality by finite distributivity, proved in both directions below. -/

theorem field_ext {A B : VertexOperator ℂ M}
    (h : ∀ n : ℤ, A[[n]] = B[[n]]) : A = B := by
  apply HVertexOperator.coeff_inj
  funext k
  simpa only [VertexOperator.coeff_eq_ncoeff] using h (-k - 1)

theorem identity_field_modes (n : ℤ) :
    ((identityField : VertexOperator ℂ M)[[n]]) =
      if n = -1 then LinearMap.id else 0 := by
  rw [identityField, VertexOperator.ncoeff_of_coeff]
  simp only [show -n - 1 = 0 ↔ n = -1 by omega]

/-- Building Laurent fields from proved pointwise truncation of actual modes. -/
def fieldOfModes (A : Carrier D →ₗ[ℂ] ℤ → Module.End ℂ M)
    (hA : ∀ (a : Carrier D) (x : M),
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n → A a n x = 0) :
    Carrier D →ₗ[ℂ] VertexOperator ℂ M where
  toFun a := VertexOperator.of_coeff (fun k => A a (-k - 1)) (by
    intro x
    obtain ⟨N, hN⟩ := hA a x
    refine ⟨-N, ?_⟩
    intro k hk
    by_contra h
    exact hk (hN (-k - 1) (by omega)))
  map_add' a b := by
    apply field_ext
    intro n
    simp only [map_add, Pi.add_apply, VertexOperator.ncoeff_of_coeff]
  map_smul' c a := by
    apply field_ext
    intro n
    simp only [map_smul, Pi.smul_apply, VertexOperator.ncoeff_of_coeff, RingHom.id_apply]

@[simp] theorem fieldOfModes_mode
    (A : Carrier D →ₗ[ℂ] ℤ → Module.End ℂ M)
    (hA : ∀ (a : Carrier D) (x : M),
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n → A a n x = 0)
    (a : Carrier D) (n : ℤ) : (fieldOfModes A hA a)[[n]] = A a n := by
  dsimp only [fieldOfModes, LinearMap.coe_mk, AddHom.coe_mk]
  rw [VertexOperator.ncoeff_of_coeff, show -(-n - 1) - 1 = n by omega]

def JacobiAt (F : Carrier D →ₗ[ℂ] VertexOperator ℂ M)
    (a b : Carrier D) (x : M) (p q r : ℤ) : Prop :=
  Function.HasFiniteSupport (jacobiLeft F a b x p q r) ∧
  Function.HasFiniteSupport (jacobiFirst F a b x p q r) ∧
  Function.HasFiniteSupport (jacobiSecond F a b x p q r) ∧
    (∑ᶠ i : ℕ, jacobiLeft F a b x p q r i) =
      (∑ᶠ i : ℕ, jacobiFirst F a b x p q r i) -
      (∑ᶠ i : ℕ, jacobiSecond F a b x p q r i)

theorem jacobiAt_module (J : FullJacobiLatticeModule D M)
    (a b : Carrier D) (x : M) (p q r : ℤ) :
    JacobiAt J.stateField a b x p q r := by
  obtain ⟨hL, hF, hS, h⟩ := J.borcherds a b x p q r
  refine ⟨hL, hF, hS, ?_⟩
  simp_rw [smul_sub] at h
  change _ = ∑ᶠ i : ℕ, (jacobiFirst J.stateField a b x p q r i -
    jacobiSecond J.stateField a b x p q r i) at h
  rw [finsum_sub_distrib hF hS] at h
  exact h

/-- Returns exactly the original record equality, including epsilon r. -/
theorem JacobiAt.original {F : Carrier D →ₗ[ℂ] VertexOperator ℂ M}
    {a b : Carrier D} {x : M} {p q r : ℤ} (h : JacobiAt F a b x p q r) :
    Function.HasFiniteSupport (jacobiLeft F a b x p q r) ∧
    Function.HasFiniteSupport (jacobiFirst F a b x p q r) ∧
    Function.HasFiniteSupport (jacobiSecond F a b x p q r) ∧
      (∑ᶠ i : ℕ, jacobiLeft F a b x p q r i) =
        ∑ᶠ i : ℕ, (((-1 : ℂ)^i) * integerBinomial r i) •
          (((F a)[[p + r - i]]) (((F b)[[q + i]]) x) -
            StateFieldResidueReconstruction.epsilon r • ((F b)[[q + r - i]])
              (((F a)[[p + i]]) x)) := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  simp_rw [smul_sub]
  change _ = ∑ᶠ i : ℕ, (jacobiFirst F a b x p q r i -
    jacobiSecond F a b x p q r i)
  rw [finsum_sub_distrib h.2.1 h.2.2.1]
  exact h.2.2.2

/-- Transport a genuine finite Jacobi equality along an actual mode map.
No Jacobi or truncation hypothesis is imposed on the target by this lemma. -/
theorem JacobiAt.map {F : Carrier D →ₗ[ℂ] VertexOperator ℂ M}
    {G : Carrier D →ₗ[ℂ] VertexOperator ℂ N} (f : M →ₗ[ℂ] N)
    (hf : ∀ (a : Carrier D) (n : ℤ) (x : M),
      f (((F a)[[n]]) x) = ((G a)[[n]]) (f x))
    {a b : Carrier D} {x : M} {p q r : ℤ} (h : JacobiAt F a b x p q r) :
    JacobiAt G a b (f x) p q r := by
  classical
  have left (i : ℕ) : f (jacobiLeft F a b x p q r i) =
      jacobiLeft G a b (f x) p q r i := by
    simp only [jacobiLeft, map_smul, hf]
  have first (i : ℕ) : f (jacobiFirst F a b x p q r i) =
      jacobiFirst G a b (f x) p q r i := by
    simp only [jacobiFirst, map_smul, hf]
  have second (i : ℕ) : f (jacobiSecond F a b x p q r i) =
      jacobiSecond G a b (f x) p q r i := by
    simp only [jacobiSecond, map_smul, hf]
  have hL : Function.HasFiniteSupport (jacobiLeft G a b (f x) p q r) := by
    simpa only [left] using h.1.fun_comp (g := f) (map_zero f)
  have hF : Function.HasFiniteSupport (jacobiFirst G a b (f x) p q r) := by
    simpa only [first] using h.2.1.fun_comp (g := f) (map_zero f)
  have hS : Function.HasFiniteSupport (jacobiSecond G a b (f x) p q r) := by
    simpa only [second] using h.2.2.1.fun_comp (g := f) (map_zero f)
  have eL : f (∑ᶠ i : ℕ, jacobiLeft F a b x p q r i) =
      ∑ᶠ i : ℕ, jacobiLeft G a b (f x) p q r i := by
    rw [map_finsum f h.1]
    exact finsum_congr left
  have eF : f (∑ᶠ i : ℕ, jacobiFirst F a b x p q r i) =
      ∑ᶠ i : ℕ, jacobiFirst G a b (f x) p q r i := by
    rw [map_finsum f h.2.1]
    exact finsum_congr first
  have eS : f (∑ᶠ i : ℕ, jacobiSecond F a b x p q r i) =
      ∑ᶠ i : ℕ, jacobiSecond G a b (f x) p q r i := by
    rw [map_finsum f h.2.2.1]
    exact finsum_congr second
  refine ⟨hL, hF, hS, ?_⟩
  rw [← eL, h.2.2.2, map_sub, eF, eS]

theorem jacobiAt_zero (F : Carrier D →ₗ[ℂ] VertexOperator ℂ M)
    (a b : Carrier D) (p q r : ℤ) : JacobiAt F a b 0 p q r := by
  have hL : jacobiLeft F a b 0 p q r = 0 := by
    funext i
    simp [jacobiLeft]
  have hF : jacobiFirst F a b 0 p q r = 0 := by
    funext i
    simp [jacobiFirst]
  have hS : jacobiSecond F a b 0 p q r = 0 := by
    funext i
    simp [jacobiSecond]
  simp [JacobiAt, hL, hF, hS, Function.HasFiniteSupport]

/-- Each of the three support bounds is the union of its two original
supports (HasFiniteSupport.add), before any finsum distributivity is used. -/
theorem JacobiAt.add {F : Carrier D →ₗ[ℂ] VertexOperator ℂ M}
    {a b : Carrier D} {x y : M} {p q r : ℤ}
    (hx : JacobiAt F a b x p q r) (hy : JacobiAt F a b y p q r) :
    JacobiAt F a b (x + y) p q r := by
  classical
  have eL : jacobiLeft F a b (x + y) p q r =
      fun i => jacobiLeft F a b x p q r i + jacobiLeft F a b y p q r i := by
    funext i
    simp only [jacobiLeft, map_add, smul_add]
  have eF : jacobiFirst F a b (x + y) p q r =
      fun i => jacobiFirst F a b x p q r i + jacobiFirst F a b y p q r i := by
    funext i
    simp only [jacobiFirst, map_add, smul_add]
  have eS : jacobiSecond F a b (x + y) p q r =
      fun i => jacobiSecond F a b x p q r i + jacobiSecond F a b y p q r i := by
    funext i
    simp only [jacobiSecond, map_add, smul_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eL]; exact hx.1.add hy.1
  · rw [eF]; exact hx.2.1.add hy.2.1
  · rw [eS]; exact hx.2.2.1.add hy.2.2.1
  · rw [eL, eF, eS, finsum_add_distrib hx.1 hy.1,
      finsum_add_distrib hx.2.1 hy.2.1,
      finsum_add_distrib hx.2.2.1 hy.2.2.1, hx.2.2.2, hy.2.2.2]
    abel

theorem JacobiAt.sum {F : Carrier D →ₗ[ℂ] VertexOperator ℂ M}
    {a b : Carrier D} {p q r : ℤ} {ι : Type*} (s : Finset ι) (x : ι → M)
    (h : ∀ i ∈ s, JacobiAt F a b (x i) p q r) :
    JacobiAt F a b (∑ i ∈ s, x i) p q r := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro h
    simpa only [Finset.sum_empty] using jacobiAt_zero F a b p q r
  | @insert i s hi ih =>
    intro h
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end
end D5.S3.VertexAlgebra.Modules.FullJacobiIntertwiner
