/-
SOURCE CANDIDATE; native elaboration and kernel validation remain pending.

This file implements the approved complete native fallback plan. It consumes
the repaired, independently accepted Stage2 source exports named in the sealed
actual-stage2 closure. ActualGroundFieldReconstruction, the sector coordinates,
classification, and generic ModuleHom/tensor/direct-sum sources remain source
prerequisites, with no acceptance claim made here. No Pro answer is attributed.

The Hom carrier is the submodule of actual all-state/all-integer-mode linear
intertwiners, faithfully equivalent to FullJacobiIntertwiner.ModuleHom. Its
restriction is into the actual nested Omega/jointWeight subtypes. Naturality
of S is proved only on a true joint weight, using E_leading independently in
each module; no equality of Taylor supports or cross-carrier commute_Pi is used.
Finite creator-polynomial induction then proves raw Phi naturality. Arbitrary
families extend by literal tensor/direct-sum maps conjugated through the supplied
classificationEquiv. Both inverses and the exact [0]1 normalization are proved.

Attribution: actual mode/current/creation and weak-module law are supplied by
FullJacobiCurrentTransport; Omega by ActualCurrentTaylor; E/groundState by
ActualChargedGroundCalculus; jointWeight by ActualGroundJointWeights;
S/E_leading by ActualGroundChargedSelection; polynomialOperator and its one/X
identities by ActualGroundFieldReconstruction; Multiplicity/Sector/Model/Phi
by ActualWeakModuleSectorCoordinates; canonicalModule/classificationEquiv and
their full-mode/normalization/finite-inverse statements by
ActualWeakModuleClassification. The base-sector action/vacuum/Jacobi proofs
are literally those of LatticeDualCosetModule used inside canonicalModule.
Exact old and actual prerequisite hashes accompany this candidate's export.

This is a Hom correspondence source candidate, not a category equivalence,
string completion, independent publication, or native acceptance receipt.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleClassification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeDiscriminantTheta LatticeDualCosetModule
open FullJacobiCurrentTransport FullJacobiIntertwiner
open FullJacobiTensorModule FullJacobiDirectSum
open ActualCurrentTaylor ActualChargedGroundCalculus ActualGroundJointWeights
open ActualGroundChargedSelection ActualGroundFiniteReconstruction
open ActualGroundFieldReconstruction ActualWeakModuleSectorCoordinates
open ActualWeakModuleClassification

universe u v
variable {D : LatticeData} {M : Type u} {N : Type v}
variable [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

attribute [local instance] Classical.propDecidable

/-- The faithful linear carrier of the existing full weak-module morphisms. -/
def homSpace (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) : Submodule ℂ (M →ₗ[ℂ] N) where
  carrier := {f | ∀ (a : Carrier D) (n : ℤ) (x : M),
    f (mode J a n x) = mode K a n (f x)}
  zero_mem' := by
    intro a n x
    simp
  add_mem' := by
    intro f g hf hg a n x
    simp only [LinearMap.add_apply, map_add, hf a n x, hg a n x]
  smul_mem' := by
    intro c f hf a n x
    simp only [LinearMap.smul_apply, map_smul, hf a n x]

/-- No new morphism record: the subtype and the existing record have identical
linear maps and identical all-state/all-mode predicates. -/
def recordEquiv (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) : ModuleHom J K ≃ homSpace J K where
  toFun f := ⟨f.linearMap, f.intertwines⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

/-- All multiplicity maps, with no support or dimension restriction. -/
abbrev Families (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) :=
  ∀ c : Discriminant D, Multiplicity J c →ₗ[ℂ] Multiplicity K c

variable {J : FullJacobiLatticeModule D M} {K : FullJacobiLatticeModule D N}

private def omegaMap (f : ModuleHom J K) : Omega J →ₗ[ℂ] Omega K :=
  (f.linearMap.comp (Omega J).subtype).codRestrict (Omega K) (by
    intro z
    apply (mem_Omega K _).mpr
    intro i r
    change current K i ((r : ℤ) + 1) (f.linearMap z.val) = 0
    calc
      _ = f.linearMap (current J i ((r : ℤ) + 1) z.val) :=
        (f.intertwines (currentState D i) ((r : ℤ) + 1) z.val).symm
      _ = 0 := by
        rw [(mem_Omega J z.val).mp z.property i r, map_zero])

private theorem omegaMap_jointWeight (f : ModuleHom J K) (b : Charge D)
    (z : Omega J) (hz : z ∈ jointWeight J b) :
    omegaMap f z ∈ jointWeight K b := by
  apply (mem_jointWeight_iff K b (omegaMap f z)).mpr
  intro i
  change current K i 0 (f.linearMap z.val) = (b i : ℂ) • f.linearMap z.val
  calc
    _ = f.linearMap (current J i 0 z.val) :=
      (f.intertwines (currentState D i) 0 z.val).symm
    _ = f.linearMap ((b i : ℂ) • z.val) :=
      congrArg f.linearMap ((mem_jointWeight_iff J b z).mp hz i)
    _ = _ := f.linearMap.map_smul (b i : ℂ) z.val

private def jointWeightMap (f : ModuleHom J K) (b : Charge D) :
    jointWeight J b →ₗ[ℂ] jointWeight K b :=
  ((omegaMap f).comp (jointWeight J b).subtype).codRestrict
    (jointWeight K b) (fun z => omegaMap_jointWeight f b z.val z.property)

/-- Literal restriction of an independently given original morphism. -/
def restrict (f : ModuleHom J K) : Families J K :=
  fun c => jointWeightMap f (representative D c)

private def restrictLinear (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N) : homSpace J K →ₗ[ℂ] Families J K where
  toFun q := restrict ((recordEquiv J K).symm q)
  map_add' q r := by
    funext c
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' a q := by
    funext c
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The two leading-mode calculations are separate. This assertion is restricted
to a true joint weight; it asserts nothing about fixed-label S on other vectors. -/
private theorem map_S_jointWeight (f : ModuleHom J K)
    (hNJ : OriginalPositiveNilpotence J) (hNK : OriginalPositiveNilpotence K)
    (HJ HK : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hLJ : HJ * gramComplex D = 1) (hRJ : gramComplex D * HJ = 1)
    (hLK : HK * gramComplex D = 1) (hRK : gramComplex D * HK = 1)
    (α b : Charge D) (z : Omega J) (hz : z ∈ jointWeight J b) :
    omegaMap f (S J hNJ HJ hLJ hRJ α b z) =
      S K hNK HK hLK hRK α b (omegaMap f z) := by
  apply Subtype.ext
  change f.linearMap (S J hNJ HJ hLJ hRJ α b z : M) =
    (S K hNK HK hLK hRK α b (omegaMap f z) : N)
  rw [← E_leading J hNJ HJ hLJ hRJ α b z hz,
    ← E_leading K hNK HK hLK hRK α b (omegaMap f z)
      (omegaMap_jointWeight f b z hz)]
  exact f.intertwines (groundState D α) (-weightPairing α b - 1) z.val

private theorem map_creation (f : ModuleHom J K) (x : Index D) (z : M) :
    f.linearMap (creation J x.1 x.2 z) =
      creation K x.1 x.2 (f.linearMap z) := by
  exact f.intertwines (currentState D x.1) (-(x.2 : ℤ) - 1) z

/-- Finite polynomial naturality, proved from actual negative current modes.
The endomorphism algebra is not made commutative. -/
private theorem map_polynomialOperator (f : ModuleHom J K)
    (hNJ : OriginalPositiveNilpotence J) (hNK : OriginalPositiveNilpotence K)
    (HJ HK : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hLJ : HJ * gramComplex D = 1) (hLK : HK * gramComplex D = 1)
    (P : Oscillator D) (z : M) :
    f.linearMap (polynomialOperator J hNJ HJ hLJ P z) =
      polynomialOperator K hNK HK hLK P (f.linearMap z) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hc : (MvPolynomial.C c : Oscillator D) = c • 1 := MvPolynomial.C_eq_smul_one
    simp [hc, polynomialOperator_one]
  | add P Q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X P x hp =>
    rw [mul_comm P (MvPolynomial.X x), polynomialOperator_X_mul,
      polynomialOperator_X_mul]
    simp only [Module.End.mul_apply]
    rw [map_creation, hp]

/-- The actual base-sector record used verbatim inside canonicalModule.
Only proof fields may differ, and proof irrelevance identifies those fields. -/
private def sectorModule (D : LatticeData) (c : Discriminant D) :
    FullJacobiLatticeModule D (Carrier D) where
  stateField := action D (representative D c)
  vacuum_field := module_vacuum D (representative D c)
  borcherds := by
    intro a b z p q r
    change Function.HasFiniteSupport (moduleLeft D (representative D c) p q r a b z) ∧
      Function.HasFiniteSupport (moduleFirst D (representative D c) p q r a b z) ∧
      Function.HasFiniteSupport (moduleSecond D (representative D c) p q r a b z) ∧ _
    exact module_borcherds D (representative D c) a b z p q r

private def familyMap (g : Families J K) : Model J →ₗ[ℂ] Model K :=
  DirectSum.lmap (fun c => TensorProduct.map LinearMap.id (g c))

/-- The supplied full-mode tensor and direct-sum morphisms apply to every g. -/
private def familyHom (g : Families J K) :
    ModuleHom (canonicalModule J) (canonicalModule K) := by
  change ModuleHom
    (directSumModule (fun c : Discriminant D =>
      tensorModule (sectorModule D c) (Multiplicity J c)))
    (directSumModule (fun c : Discriminant D =>
      tensorModule (sectorModule D c) (Multiplicity K c)))
  exact directSumHom _ _ (fun c =>
    tensorHom (sectorModule D c) (sectorModule D c)
      { linearMap := LinearMap.id
        intertwines := by intro a n z; rfl } (g c))

private theorem familyMap_single (g : Families J K) (c : Discriminant D)
    (n : Charge D) (P : Oscillator D) (w : Multiplicity J c) :
    familyMap g
      (DirectSum.lof ℂ (Discriminant D) (Sector J) c
        (Finsupp.single n P ⊗ₜ[ℂ] w)) =
      DirectSum.lof ℂ (Discriminant D) (Sector K) c
        (Finsupp.single n P ⊗ₜ[ℂ] g c w) := by
  simp only [familyMap, DirectSum.lmap_lof, TensorProduct.map_tmul,
    LinearMap.id_apply]

/-- Non-binding new content: raw forward coordinates are natural for an
independently supplied actual ModuleHom, with independent Taylor witnesses. -/
private theorem Phi_naturality (f : ModuleHom J K)
    (hNJ : OriginalPositiveNilpotence J) (hNK : OriginalPositiveNilpotence K)
    (HJ HK : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hLJ : HJ * gramComplex D = 1) (hRJ : gramComplex D * HJ = 1)
    (hLK : HK * gramComplex D = 1) (hRK : gramComplex D * HK = 1)
    (x : Model J) :
    f.linearMap (Phi J hNJ HJ hLJ hRJ x) =
      Phi K hNK HK hLK hRK (familyMap (restrict f) x) := by
  have h : f.linearMap.comp (Phi J hNJ HJ hLJ hRJ) =
      (Phi K hNK HK hLK hRK).comp (familyMap (restrict f)) := by
    apply DirectSum.linearMap_ext
    intro c
    apply TensorProduct.ext
    apply Finsupp.lhom_ext'
    intro n
    apply LinearMap.ext
    intro P
    apply LinearMap.ext
    intro w
    change f.linearMap (Phi J hNJ HJ hLJ hRJ
      (DirectSum.lof ℂ (Discriminant D) (Sector J) c
        (Finsupp.single n P ⊗ₜ[ℂ] w))) =
      Phi K hNK HK hLK hRK (familyMap (restrict f)
        (DirectSum.lof ℂ (Discriminant D) (Sector J) c
          (Finsupp.single n P ⊗ₜ[ℂ] w)))
    rw [familyMap_single, Phi_single, Phi_single,
      map_polynomialOperator f hNJ hNK HJ HK hLJ hLK]
    exact congrArg (polynomialOperator K hNK HK hLK P)
      (congrArg (fun z : Omega K => (z : N))
        (map_S_jointWeight f hNJ hNK HJ HK hLJ hRJ hLK hRK
          n (representative D c) w.val w.property))
  exact LinearMap.congr_fun h x

private theorem inverseGram_left_witness
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    inverseGram hD * gramComplex D = 1 :=
  (Classical.choose_spec (LatticePositiveEnergy.complex_inverse_exists D hD)).1

private theorem inverseGram_right_witness
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    gramComplex D * inverseGram hD = 1 :=
  (Classical.choose_spec (LatticePositiveEnergy.complex_inverse_exists D hD)).2

private theorem classification_naturality (f : ModuleHom J K)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (x : Model J) :
    f.linearMap (classificationEquiv J hD x) =
      classificationEquiv K hD (familyMap (restrict f) x) := by
  exact Phi_naturality f (originalNilpotence J hD) (originalNilpotence K hD)
    (inverseGram hD) (inverseGram hD)
    (inverseGram_left_witness hD) (inverseGram_right_witness hD)
    (inverseGram_left_witness hD) (inverseGram_right_witness hD) x

/-- Every family extends to an existing ModuleHom on the original modules.
The map is literal actual tensor/direct-sum transport through classificationEquiv. -/
def extend (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (g : Families J K) : ModuleHom J K where
  linearMap := (classificationEquiv K hD).toLinearMap.comp
    ((familyMap g).comp (classificationEquiv J hD).symm.toLinearMap)
  intertwines := by
    intro a n x
    change classificationEquiv K hD
      (familyMap g ((classificationEquiv J hD).symm (mode J a n x))) =
      mode K a n (classificationEquiv K hD
        (familyMap g ((classificationEquiv J hD).symm x)))
    rw [classification_inverse]
    have hm : familyMap g (mode (canonicalModule J) a n
        ((classificationEquiv J hD).symm x)) =
        mode (canonicalModule K) a n
          (familyMap g ((classificationEquiv J hD).symm x)) :=
      (familyHom g).intertwines a n ((classificationEquiv J hD).symm x)
    rw [hm, classification]

/-- Exact ground normalization, with the supplied [0]1 inclusion and no scalar
or chosen basis. This equality is consumed by the restriction/extension inverse. -/
theorem extend_ground (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (g : Families J K) (c : Discriminant D) (w : Multiplicity J c) :
    (extend hD g).linearMap (w.val : M) = ((g c w).val : N) := by
  have hinv : (classificationEquiv J hD).symm (w.val : M) =
      DirectSum.lof ℂ (Discriminant D) (Sector J) c
        (Finsupp.single 0 (1 : Oscillator D) ⊗ₜ[ℂ] w) := by
    apply (classificationEquiv J hD).injective
    rw [(classificationEquiv J hD).apply_symm_apply, classification_normalization]
  change classificationEquiv K hD
    (familyMap g ((classificationEquiv J hD).symm (w.val : M))) = _
  rw [hinv, familyMap_single, classification_normalization]

private theorem restrict_extend
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (g : Families J K) :
    restrict (extend hD g) = g := by
  funext c
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  apply Subtype.ext
  exact extend_ground hD g c w

private theorem extend_restrict
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (f : ModuleHom J K) :
    extend hD (restrict f) = f := by
  have hlinear : (extend hD (restrict f)).linearMap = f.linearMap := by
    apply LinearMap.ext
    intro x
    change classificationEquiv K hD
      (familyMap (restrict f) ((classificationEquiv J hD).symm x)) = f.linearMap x
    rw [← classification_naturality f hD,
      (classificationEquiv J hD).apply_symm_apply]
  apply (recordEquiv J K).injective
  exact Subtype.ext hlinear

/-- Full complex-linear correspondence on the faithful actual Hom space.
Only original modules and original positive definiteness are parameters.
Independent universes, zero spaces and rank zero require no extra hypotheses. -/
def homMultiplicityEquiv (J : FullJacobiLatticeModule D M)
    (K : FullJacobiLatticeModule D N)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    homSpace J K ≃ₗ[ℂ] Families J K where
  toLinearMap := restrictLinear J K
  invFun g := recordEquiv J K (extend hD g)
  left_inv q := by
    change recordEquiv J K
      (extend hD (restrict ((recordEquiv J K).symm q))) = q
    rw [extend_restrict, (recordEquiv J K).apply_symm_apply]
  right_inv g := by
    change restrict ((recordEquiv J K).symm (recordEquiv J K (extend hD g))) = g
    rw [(recordEquiv J K).symm_apply_apply, restrict_extend]

/-- Concrete vectorwise finite value of the extension. Both supports belong
to the source vector. The returnWeight carries the original epsilon(-n,n)^-1;
the target receives precisely g applied to that literal representative weight. -/
theorem extend_explicit (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (g : Families J K) (x : M) :
    let hNJ := originalNilpotence J hD
    let hNK := originalNilpotence K hD
    let H := inverseGram hD
    let hL := inverseGram_left_witness hD
    let hR := inverseGram_right_witness hD
    let T := W J hNJ H hL
    let ω := fun d => vacuumToOmega J hNJ H hL hR (T.coefficient d x)
    (extend hD g).linearMap x =
      ∑ d ∈ (T.coefficients x).support,
        ∑ b ∈ (jointDecomposition J hNJ hD (ω d)).support,
          polynomialOperator K hNK H hL (MvPolynomial.monomial d 1)
            (S K hNK H hL hR (weightIndex hD b).2
              (representative D (weightIndex hD b).1)
              ((g (weightIndex hD b).1)
                (returnWeight J hNJ H hL hR hD b
                  ((jointDecomposition J hNJ hD (ω d)) b))).val : N) := by
  dsimp only
  change classificationEquiv K hD
    (familyMap g ((classificationEquiv J hD).symm x)) = _
  rw [classification_inverse_explicit]
  simp only [map_sum, familyMap_single, classification_on_single]

/- Registration boundary: the sealed 67-module actual-stage2 source closure
contains no Describe or typed Reg declaration/import. No registration source
outside those permitted static inputs was read. Describe/typed Reg registration
is unfinished until its exact API is supplied; no binding is invented here.
-/

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleHom
