/-
Source candidate only. No elaboration or kernel-acceptance claim.

The input closure is the independently accepted 99-module final-source closure
identified by inputs.json, rather than the historical status comments embedded
in those final sources. Only original weak modules and original positiveG occur
at the endpoint. No pending arbitrary-input lawful-field API is imported.

The new content is the balanced algebraic tensor construction of a full Hahn
field, finite elementary presentations, three independent Jacobi support
extensions, and literal translation/Jacobi equations after classification.
The fixed-sector canonical field and all weak-module axioms are reused.
Attribution: the canonical fields retain their Bakalov--Kac conventions and
their suppliers' Carnahan/Kytola residue and conformal attributions.
The original VOA/CFT/fusion/string goal remains active and incomplete.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleScalarProbes
import D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullIntertwiner

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleUniversalField

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeSugawaraCurrents LatticeActualConformalState
open LatticeDualCosetModule LatticeDualCosetConformal
open FullJacobiCurrentTransport FullJacobiIntertwiner
open FullJacobiTensorModule FullJacobiDirectSum
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleScalarProbes (sectorModule sectorModule_mode)
open StateFieldResidueReconstruction (integerBinomial)


universe u v w z
variable {D : LatticeData} {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

attribute [local instance] Classical.propDecidable

variable (A : FullJacobiLatticeModule D X) (B : FullJacobiLatticeModule D Y)

/-- The summands use the additive charge, without choosing a representative
of its discriminant class or changing the canonical intertwiner. -/
abbrev PairSector (cd : Discriminant D × Discriminant D) :=
  Carrier D ⊗[ℂ] (Multiplicity A cd.1 ⊗[ℂ] Multiplicity B cd.2)

abbrev P := ⨁ cd : Discriminant D × Discriminant D, PairSector A B cd

-- Cache the canonical instance at this composite type to keep elaboration local.
local instance modelToTargetAddCommGroup : AddCommGroup (Model B →ₗ[ℂ] P A B) :=
  inferInstance

/-- The full weak target is exactly a direct sum of accepted tensor modules. -/
def targetModule : FullJacobiLatticeModule D (P A B) :=
  directSumModule (fun cd : Discriminant D × Discriminant D =>
    tensorModule (sectorModule D (representative D cd.1 + representative D cd.2))
      (Multiplicity A cd.1 ⊗[ℂ] Multiplicity B cd.2))

/-- The literal canonical field; this abbreviation makes no new choice. -/
abbrev C (c d : Discriminant D) :=
  LatticeCosetCanonicalIntertwiner.intertwiner D
    (1 : Matrix (Fin D.rank) (Fin D.rank) ℤ)
    (representative D c) (representative D d)

/-- Balanced multiplicity inclusion, as a linear map in all three factors. -/
def tag (c d : Discriminant D) :
    Multiplicity A c →ₗ[ℂ] Multiplicity B d →ₗ[ℂ] Carrier D →ₗ[ℂ] P A B where
  toFun n :=
    { toFun m := (DirectSum.lof ℂ _ (PairSector A B) (c,d)).comp
        ((TensorProduct.mk ℂ (Carrier D) _).flip (n ⊗ₜ[ℂ] m))
      map_add' m m' := by
        apply LinearMap.ext
        intro x
        change DirectSum.lof ℂ _ (PairSector A B) (c,d)
          (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] (m+m'))) =
            DirectSum.lof ℂ _ (PairSector A B) (c,d) (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m)) +
            DirectSum.lof ℂ _ (PairSector A B) (c,d) (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m'))
        rw [TensorProduct.tmul_add,TensorProduct.tmul_add,map_add]
      map_smul' a m := by
        apply LinearMap.ext
        intro x
        change DirectSum.lof ℂ _ (PairSector A B) (c,d)
          (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] (a • m))) =
            a • DirectSum.lof ℂ _ (PairSector A B) (c,d) (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m))
        rw [TensorProduct.tmul_smul,TensorProduct.tmul_smul,map_smul] }
  map_add' n n' := by
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro x
    change DirectSum.lof ℂ _ (PairSector A B) (c,d)
      (x ⊗ₜ[ℂ] ((n+n') ⊗ₜ[ℂ] m)) =
        DirectSum.lof ℂ _ (PairSector A B) (c,d) (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m)) +
        DirectSum.lof ℂ _ (PairSector A B) (c,d) (x ⊗ₜ[ℂ] (n' ⊗ₜ[ℂ] m))
    rw [TensorProduct.add_tmul,TensorProduct.tmul_add,map_add]
  map_smul' a n := by
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro x
    change DirectSum.lof ℂ _ (PairSector A B) (c,d)
      (x ⊗ₜ[ℂ] ((a • n) ⊗ₜ[ℂ] m)) =
        a • DirectSum.lof ℂ _ (PairSector A B) (c,d) (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m))
    rw [← TensorProduct.smul_tmul',TensorProduct.tmul_smul,map_smul]

@[simp] theorem tag_apply (c d : Discriminant D)
    (n : Multiplicity A c) (m : Multiplicity B d) (x : Carrier D) :
    tag A B c d n m x = DirectSum.lof ℂ _ (PairSector A B) (c,d)
      (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m)) := rfl

/-- The actual inclusionHom is reused; the insertion into its tensor summand
intertwines every original state and integer mode by tensorModule_mode. -/
def tagHom (c d : Discriminant D) (n : Multiplicity A c) (m : Multiplicity B d) :
    ModuleHom (sectorModule D (representative D c + representative D d))
      (targetModule A B) :=
  (inclusionHom _ (c,d)).comp
    { linearMap := (TensorProduct.mk ℂ (Carrier D) _).flip (n ⊗ₜ[ℂ] m)
      intertwines := by
        intro h k x
        simp only [tensorModule_mode,sectorModule_mode,TensorProduct.map_tmul,
          LinearMap.id_apply] <;> rfl }

@[simp] theorem target_action_tag (c d : Discriminant D)
    (n : Multiplicity A c) (m : Multiplicity B d) (h x : Carrier D) (k : ℤ) :
    mode (targetModule A B) h k (tag A B c d n m x) =
      tag A B c d n m (((action D (representative D c + representative D d) h)[[k]]) x) :=
by
  change mode (targetModule A B) h k
      (DirectSum.lof ℂ _ (PairSector A B) (c,d) (x ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m))) =
    DirectSum.lof ℂ _ (PairSector A B) (c,d)
      ((((action D (representative D c + representative D d) h)[[k]]) x) ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m))
  simp only [targetModule, directSumModule_mode, DirectSum.lmap_lof,
    tensorModule_mode, sectorModule_mode, TensorProduct.map_tmul, LinearMap.id_apply]

private def raw {Z : Type w} [AddCommGroup Z] [Module ℂ Z]
    (s : HahnModule ℚ ℂ Z) (q : ℚ) : Z := ((HahnModule.of ℂ).symm s).coeff q

private theorem hahn_ext {Z : Type w} [AddCommGroup Z] [Module ℂ Z]
    {s t : HahnModule ℚ ℂ Z} (h : ∀ q, raw s q = raw t q) : s = t := by
  apply (HahnModule.of ℂ).symm.injective
  apply HahnSeries.ext
  exact funext h

@[simp] private theorem raw_add {Z : Type w} [AddCommGroup Z] [Module ℂ Z]
    (s t : HahnModule ℚ ℂ Z) (q : ℚ) : raw (s + t) q = raw s q + raw t q := by
  simp [raw, HahnModule.of_symm_add, HahnSeries.coeff_add]

@[simp] private theorem raw_smul {Z : Type w} [AddCommGroup Z] [Module ℂ Z]
    (a : ℂ) (s : HahnModule ℚ ℂ Z) (q : ℚ) : raw (a • s) q = a • raw s q := by
  simp [raw, HahnModule.of_symm_smul, HahnSeries.coeff_smul]

private theorem raw_post {Z : Type w} {W : Type z}
    [AddCommGroup Z] [Module ℂ Z] [AddCommGroup W] [Module ℂ W]
    (f : Z →ₗ[ℂ] W) (s : HahnModule ℚ ℂ Z) (q : ℚ) :
    raw (D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullIntertwiner.hahnPost f s) q = f (raw s q) := rfl

/-- Four-linear Hahn-valued seed. Its value is a full series, not a raw
function with a support obligation deferred until after the tensor quotient. -/
private def seedAt (c d : Discriminant D) (x : Carrier D) :
    Multiplicity A c →ₗ[ℂ] Carrier D →ₗ[ℂ] Multiplicity B d →ₗ[ℂ]
      HahnModule ℚ ℂ (P A B) :=
    { toFun n :=
        { toFun y :=
            { toFun m := D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullIntertwiner.hahnPost (tag A B c d n m) (C c d x y)
              map_add' m m' := by
                apply hahn_ext
                intro q
                change tag A B c d n (m + m') (raw (C c d x y) q) =
                  tag A B c d n m (raw (C c d x y) q) + tag A B c d n m' (raw (C c d x y) q)
                simp only [map_add, LinearMap.add_apply]
              map_smul' a m := by
                apply hahn_ext
                intro q
                change tag A B c d n (a • m) (raw (C c d x y) q) =
                  a • tag A B c d n m (raw (C c d x y) q)
                simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
          map_add' y y' := by
            apply LinearMap.ext
            intro m
            apply hahn_ext
            intro q
            change tag A B c d n m (raw (C c d x (y+y')) q) =
              tag A B c d n m (raw (C c d x y) q) + tag A B c d n m (raw (C c d x y') q)
            rw [map_add, raw_add, map_add]
          map_smul' a y := by
            apply LinearMap.ext
            intro m
            apply hahn_ext
            intro q
            change tag A B c d n m (raw (C c d x (a • y)) q) =
              a • tag A B c d n m (raw (C c d x y) q)
            rw [map_smul, raw_smul, map_smul] }
      map_add' n n' := by
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro m
        apply hahn_ext
        intro q
        change tag A B c d (n+n') m (raw (C c d x y) q) =
          tag A B c d n m (raw (C c d x y) q) + tag A B c d n' m (raw (C c d x y) q)
        simp only [map_add, LinearMap.add_apply]
      map_smul' a n := by
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro m
        apply hahn_ext
        intro q
        change tag A B c d (a • n) m (raw (C c d x y) q) =
          a • tag A B c d n m (raw (C c d x y) q)
        simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }

private def seed (c d : Discriminant D) :
    Carrier D →ₗ[ℂ] Multiplicity A c →ₗ[ℂ]
      Carrier D →ₗ[ℂ] Multiplicity B d →ₗ[ℂ] HahnModule ℚ ℂ (P A B) where
  toFun x := seedAt A B c d x
  map_add' x x' := by
    apply LinearMap.ext
    intro n
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro m
    apply hahn_ext
    intro q
    change tag A B c d n m (raw (C c d (x+x') y) q) =
      tag A B c d n m (raw (C c d x y) q) + tag A B c d n m (raw (C c d x' y) q)
    rw [map_add, LinearMap.add_apply, raw_add, map_add]
  map_smul' a x := by
    apply LinearMap.ext
    intro n
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro m
    apply hahn_ext
    intro q
    change tag A B c d n m (raw (C c d (a • x) y) q) =
      a • tag A B c d n m (raw (C c d x y) q)
    rw [map_smul, LinearMap.smul_apply, raw_smul, map_smul]

/-- Both tensor quotients are taken before either dependent direct sum. -/
def block (c d : Discriminant D) :
    Sector A c →ₗ[ℂ] HVertexOperator ℚ ℂ (Sector B d) (P A B) :=
  TensorProduct.lift ((seed A B c d).compr₂
    (TensorProduct.uncurry (RingHom.id ℂ) (Carrier D) (Multiplicity B d)
      (HahnModule ℚ ℂ (P A B))))

@[simp] theorem block_tmul (c d : Discriminant D)
    (x y : Carrier D) (n : Multiplicity A c) (m : Multiplicity B d) :
    block A B c d (x ⊗ₜ[ℂ] n) (y ⊗ₜ[ℂ] m) =
      D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullIntertwiner.hahnPost (tag A B c d n m) (C c d x y) := rfl

private def column (c : Discriminant D) :
    Sector A c →ₗ[ℂ] HVertexOperator ℚ ℂ (Model B) (P A B) where
  toFun s := DirectSum.toModule ℂ _ _ (fun d => block A B c d s)
  map_add' s t := by
    apply DirectSum.linearMap_ext
    intro d
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof, map_add,
      LinearMap.add_apply]
  map_smul' a s := by
    apply DirectSum.linearMap_ext
    intro d
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof, map_smul,
      LinearMap.smul_apply, RingHom.id_apply]

/-- Full Hahn field on the actual classified direct sums. -/
def modelField : Model A →ₗ[ℂ] HVertexOperator ℚ ℂ (Model B) (P A B) :=
  DirectSum.toModule ℂ _ _ (column A B)

abbrev elementary (J : FullJacobiLatticeModule D X) (c : Discriminant D)
    (x : Carrier D) (n : Multiplicity J c) : Model J :=
  DirectSum.lof ℂ _ (Sector J) c (x ⊗ₜ[ℂ] n)

@[simp] theorem modelField_elementary (c d : Discriminant D)
    (x y : Carrier D) (n : Multiplicity A c) (m : Multiplicity B d) :
    modelField A B (elementary A c x n) (elementary B d y m) =
      D5.S3.VertexAlgebra.Sectors.ActualWeakTargetFullIntertwiner.hahnPost (tag A B c d n m) (C c d x y) := by
  simp only [modelField, elementary, DirectSum.toModule_lof, column, LinearMap.coe_mk, AddHom.coe_mk, block_tmul]

/-- Literal raw-q coefficient on arbitrary classified elementary vectors. -/
@[simp] theorem modelField_elementary_coeff (c d : Discriminant D)
    (x y : Carrier D) (n : Multiplicity A c) (m : Multiplicity B d) (q : ℚ) :
    (modelField A B (elementary A c x n)).coeff q (elementary B d y m) =
      tag A B c d n m ((C c d x).coeff q y) := by
  change raw (modelField A B (elementary A c x n) (elementary B d y m)) q = _
  rw [modelField_elementary, raw_post] <;> rfl

/-- Literal full-module action on a classified elementary vector. -/
@[simp] theorem canonical_action_elementary (J : FullJacobiLatticeModule D X)
    (c : Discriminant D) (x h : Carrier D) (n : Multiplicity J c) (k : ℤ) :
    mode (canonicalModule J) h k (elementary J c x n) =
      elementary J c (((action D (representative D c) h)[[k]]) x) n := by
  simp only [canonicalModule, directSumModule_mode, elementary, DirectSum.lmap_lof,
    tensorModule_mode, TensorProduct.map_tmul, LinearMap.id_apply] <;> rfl

variable (positiveG : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

/-- Classification pullback on both inputs. The evaluated value lives in
HahnModule; the once-curried value lives in HVertexOperator. -/
def U : X →ₗ[ℂ] HVertexOperator ℚ ℂ Y (P A B) where
  toFun x := LinearMap.comp (modelField A B ((classificationEquiv A positiveG).symm x))
    (classificationEquiv B positiveG).symm.toLinearMap
  map_add' x y := by simp only [map_add, LinearMap.add_comp]
  map_smul' a x := by simp only [map_smul, LinearMap.smul_comp, RingHom.id_apply]

@[simp] theorem U_classified (s : Model A) (t : Model B) :
    U A B positiveG (classificationEquiv A positiveG s)
      (classificationEquiv B positiveG t) = modelField A B s t := by
  simp only [U, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

@[simp] theorem U_elementary_coeff (c d : Discriminant D)
    (x y : Carrier D) (n : Multiplicity A c) (m : Multiplicity B d) (q : ℚ) :
    (U A B positiveG (classificationEquiv A positiveG (elementary A c x n))).coeff q
      (classificationEquiv B positiveG (elementary B d y m)) =
      DirectSum.lof ℂ _ (PairSector A B) (c,d)
        (((C c d x).coeff q y) ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m)) := by
  change raw (U A B positiveG (classificationEquiv A positiveG (elementary A c x n))
    (classificationEquiv B positiveG (elementary B d y m))) q = _
  rw [U_classified]
  simpa only [tag_apply, HVertexOperator.coeff, LinearMap.coe_mk, AddHom.coe_mk, raw] using modelField_elementary_coeff A B c d x y n m q

/-- The two outer sums are over the actual vectors' finite sector supports. -/
theorem U_sector_sum (x : X) (y : Y) :
    let s := (classificationEquiv A positiveG).symm x
    let t := (classificationEquiv B positiveG).symm y
    U A B positiveG x y = ∑ c ∈ s.support, ∑ d ∈ t.support,
      block A B c d (s c) (t d) := by
  classical
  dsimp only
  let s := (classificationEquiv A positiveG).symm x
  let t := (classificationEquiv B positiveG).symm y
  have hs : (∑ c ∈ s.support, DirectSum.lof ℂ _ (Sector A) c (s c)) = s := by
    simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of s
  have ht : (∑ d ∈ t.support, DirectSum.lof ℂ _ (Sector B) d (t d)) = t := by
    simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of t
  change modelField A B s t = _
  calc
    modelField A B s t = modelField A B
        (∑ c ∈ s.support, DirectSum.lof ℂ _ (Sector A) c (s c))
        (∑ d ∈ t.support, DirectSum.lof ℂ _ (Sector B) d (t d)) := by rw [hs,ht]
    _ = _ := by
      simp only [modelField,map_sum,LinearMap.sum_apply,DirectSum.toModule_lof,column,LinearMap.coe_mk,AddHom.coe_mk]
      exact Finset.sum_comm

/-- Actual zero modes of omega, for every original weak module. -/
def translation {Z : Type w} [AddCommGroup Z] [Module ℂ Z]
    (J : FullJacobiLatticeModule D Z)
    (positiveG : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) : Module.End ℂ Z :=
  mode J (omega D (inverseGram positiveG)) 0

/-- Additive generation uses only algebraic tensor induction and the actual
dependent direct-sum induction. No basis or dimension hypothesis is used. -/
private theorem model_induction (J : FullJacobiLatticeModule D X)
    (Q : Model J → Prop) (h0 : Q 0)
    (hadd : ∀ s t, Q s → Q t → Q (s+t))
    (he : ∀ c x n, Q (elementary J c x n)) (s : Model J) : Q s := by
  induction s using DirectSum.induction_on with
  | zero => exact h0
  | of c z =>
    change Q (DirectSum.lof ℂ _ (Sector J) c z)
    induction z using TensorProduct.inductionOn with
    | tmul x n => exact he c x n
    | add s t hs ht => simpa only [map_add] using hadd _ _ hs ht
  | add s t hs ht => exact hadd s t hs ht

abbrev ElementaryData (J : FullJacobiLatticeModule D X) :=
  Σ c : Discriminant D, Carrier D × Multiplicity J c

abbrev elementaryValue (J : FullJacobiLatticeModule D X) (e : ElementaryData J) :=
  elementary J e.1 e.2.1 e.2.2

/-- Every vector has its own finite algebraic presentation; duplicate
summands are retained by List, and the zero vector permits the empty list. -/
theorem elementary_presentation (J : FullJacobiLatticeModule D X) (s : Model J) :
    ∃ l : List (ElementaryData J), s = (l.map (elementaryValue J)).sum := by
  apply model_induction J (fun s => ∃ l : List (ElementaryData J),
    s = (l.map (elementaryValue J)).sum)
  · exact ⟨[], by simp⟩
  · intro s t hs ht
    obtain ⟨l,hl⟩ := hs
    obtain ⟨k,hk⟩ := ht
    exact ⟨l ++ k, by simp only [List.map_append, List.sum_append, ← hl, ← hk]⟩
  · intro c x n
    exact ⟨[⟨c,x,n⟩], by simp⟩

/-- Raw coefficients of the actual field on finite tensor presentations. -/
theorem modelField_list_coeff (l : List (ElementaryData A))
    (k : List (ElementaryData B)) (q : ℚ) :
    (modelField A B (l.map (elementaryValue A)).sum).coeff q
      (k.map (elementaryValue B)).sum =
    (l.map (fun e => (k.map (fun f => tag A B e.1 f.1 e.2.2 f.2.2
      ((C e.1 f.1 e.2.1).coeff q f.2.1))).sum)).sum := by
  induction l with
  | nil => simp
  | cons e l hl =>
    simp only [List.map_cons, List.sum_cons, map_add, Pi.add_apply,
      LinearMap.add_apply, hl]
    congr 1
    clear hl
    induction k with
    | nil => simp
    | cons f k hk =>
      simp only [List.map_cons, List.sum_cons, map_add, hk]
      congr 1
      exact modelField_elementary_coeff A B e.1 f.1 e.2.1 f.2.1 e.2.2 f.2.2 q

/-- A finite union bound for each actual input pair. The sector fields in
the bound are evaluated at the finite algebraic presentations of that pair. -/
theorem U_support_finite_union (x : X) (y : Y) :
    ∃ (l : List (ElementaryData A)) (k : List (ElementaryData B)),
      (classificationEquiv A positiveG).symm x = (l.map (elementaryValue A)).sum ∧
      (classificationEquiv B positiveG).symm y = (k.map (elementaryValue B)).sum ∧
      Function.support (fun q => (U A B positiveG x).coeff q y) ⊆
        ⋃ e ∈ (l.toFinset : Set (ElementaryData A)),
          ⋃ f ∈ (k.toFinset : Set (ElementaryData B)),
            Function.support (fun q => (C e.1 f.1 e.2.1).coeff q f.2.1) := by
  classical
  obtain ⟨l,hl⟩ := elementary_presentation A ((classificationEquiv A positiveG).symm x)
  obtain ⟨k,hk⟩ := elementary_presentation B ((classificationEquiv B positiveG).symm y)
  refine ⟨l,k,hl,hk,?_⟩
  intro q hq
  by_contra hn
  have hz (e : ElementaryData A) (he : e ∈ l)
      (f : ElementaryData B) (hf : f ∈ k) :
      (C e.1 f.1 e.2.1).coeff q f.2.1 = 0 := by
    by_contra h
    apply hn
    exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨by simpa using he,
      Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨by simpa using hf,h⟩⟩⟩⟩
  apply hq
  change raw (modelField A B ((classificationEquiv A positiveG).symm x)
    ((classificationEquiv B positiveG).symm y)) q = 0
  rw [hl,hk]
  change (modelField A B (l.map (elementaryValue A)).sum).coeff q
    (k.map (elementaryValue B)).sum = 0
  rw [modelField_list_coeff]
  apply List.sum_eq_zero
  intro z hz'
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz'
  apply List.sum_eq_zero
  intro z hz'
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hz'
  rw [hz e he f hf, map_zero]

private theorem finite_union_pwo {ι : Type w} (s : Finset ι) (f : ι → Set ℚ)
    (hf : ∀ i ∈ s, (f i).IsPWO) : (⋃ i ∈ (s : Set ι), f i).IsPWO := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro hf; simp
  | @insert a s ha ih =>
    intro hf
    rw [Finset.coe_insert, Set.biUnion_insert]
    exact (hf a (Finset.mem_insert_self a s)).union
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- The union bound is PWO because both indexing sets are finite and each
canonical field has its actual evaluated Hahn support. -/
theorem U_isPWO (x : X) (y : Y) :
    (Function.support (fun q => (U A B positiveG x).coeff q y)).IsPWO := by
  classical
  obtain ⟨l,k,hl,hk,hs⟩ := U_support_finite_union A B positiveG x y
  apply Set.IsPWO.mono _ hs
  apply finite_union_pwo l.toFinset
  intro e he
  apply finite_union_pwo k.toFinset
  intro f hf
  exact (C e.1 f.1 e.2.1).isPWO_support_coeff f.2.1

/-- Rational modes use raw exponent -tau-1 throughout. -/
def modelMode (τ : ℚ) : Model A →ₗ[ℂ] Model B →ₗ[ℂ] P A B where
  toFun s := (modelField A B s).coeff (-τ-1)
  map_add' s t := by simp only [map_add, Pi.add_apply]
  map_smul' a s := by simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

@[simp] theorem modelMode_elementary (c d : Discriminant D)
    (x y : Carrier D) (n : Multiplicity A c) (m : Multiplicity B d) (τ : ℚ) :
    modelMode A B τ (elementary A c x n) (elementary B d y m) =
      tag A B c d n m (LatticeDualCosetIntertwiner.mode (C c d) x τ y) :=
  modelField_elementary_coeff A B c d x y n m (-τ-1)

/-- These are bilinear maps for this constructed field alone; they are not
a predicate, record, or representation framework for arbitrary fields. -/
def leftFamily (h : Carrier D) (p r : ℤ) (τ : ℚ) (i : ℕ) :
    Model A →ₗ[ℂ] Model B →ₗ[ℂ] P A B :=
  integerBinomial p i • (modelMode A B ((p : ℚ)+τ-i)).comp
    (mode (canonicalModule A) h (r+i))

def firstFamily (h : Carrier D) (p r : ℤ) (τ : ℚ) (i : ℕ) :
    Model A →ₗ[ℂ] Model B →ₗ[ℂ] P A B :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    (modelMode A B (τ+i)).compr₂ (mode (targetModule A B) h (p+r-i))

def secondFamily (h : Carrier D) (p r : ℤ) (τ : ℚ) (i : ℕ) :
    Model A →ₗ[ℂ] Model B →ₗ[ℂ] P A B :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r •
      (modelMode A B (τ+r-i)).compl₂ (mode (canonicalModule B) h (p+i)))

@[simp] theorem leftFamily_elementary (c d : Discriminant D)
    (x y h : Carrier D) (n : Multiplicity A c) (m : Multiplicity B d)
    (p r : ℤ) (τ : ℚ) (i : ℕ) :
    leftFamily A B h p r τ i (elementary A c x n) (elementary B d y m) =
      tag A B c d n m (LatticeDualCosetIntertwiner.leftTerm D (representative D c)
        (C c d) h x y p r τ i) := by
  simp only [leftFamily, LinearMap.smul_apply, LinearMap.comp_apply,
    canonical_action_elementary, modelMode_elementary,
    LatticeDualCosetIntertwiner.leftTerm, map_smul]

@[simp] theorem firstFamily_elementary (c d : Discriminant D)
    (x y h : Carrier D) (n : Multiplicity A c) (m : Multiplicity B d)
    (p r : ℤ) (τ : ℚ) (i : ℕ) :
    firstFamily A B h p r τ i (elementary A c x n) (elementary B d y m) =
      tag A B c d n m (LatticeDualCosetIntertwiner.firstTerm D
        (representative D c) (representative D d) (C c d) h x y p r τ i) := by
  simp only [firstFamily, LinearMap.smul_apply, LinearMap.compr₂_apply,
    modelMode_elementary, target_action_tag,
    LatticeDualCosetIntertwiner.firstTerm, map_smul]

@[simp] theorem secondFamily_elementary (c d : Discriminant D)
    (x y h : Carrier D) (n : Multiplicity A c) (m : Multiplicity B d)
    (p r : ℤ) (τ : ℚ) (i : ℕ) :
    secondFamily A B h p r τ i (elementary A c x n) (elementary B d y m) =
      tag A B c d n m (LatticeDualCosetIntertwiner.secondTerm D (representative D d)
        (C c d) h x y p r τ i) := by
  simp only [secondFamily, LinearMap.smul_apply, LinearMap.compl₂_apply,
    canonical_action_elementary, modelMode_elementary,
    LatticeDualCosetIntertwiner.secondTerm, map_smul]

private theorem bilinear_list_eval {Z : Type w} [AddCommGroup Z] [Module ℂ Z]
    (F : Model A →ₗ[ℂ] Model B →ₗ[ℂ] Z)
    (l : List (ElementaryData A)) (k : List (ElementaryData B)) :
    F (l.map (elementaryValue A)).sum (k.map (elementaryValue B)).sum =
      (l.map (fun e => (k.map (fun f => F (elementaryValue A e)
        (elementaryValue B f))).sum)).sum := by
  induction l with
  | nil => simp
  | cons e l hl =>
    simp only [List.map_cons,List.sum_cons,map_add,LinearMap.add_apply,hl]
    congr 1
    clear hl
    induction k with
    | nil => simp
    | cons f k hk => simp only [List.map_cons,List.sum_cons,map_add,hk]

/-- An explicit finite union support bound for any bilinear index family
on the two actual algebraic presentations; no field law is an input. -/
private theorem presentation_support {Z : Type w} [AddCommGroup Z] [Module ℂ Z]
    (F : ℕ → Model A →ₗ[ℂ] Model B →ₗ[ℂ] Z)
    (l : List (ElementaryData A)) (k : List (ElementaryData B)) :
    Function.support (fun i => F i (l.map (elementaryValue A)).sum
      (k.map (elementaryValue B)).sum) ⊆
    ⋃ e ∈ (l.toFinset : Set (ElementaryData A)),
      ⋃ f ∈ (k.toFinset : Set (ElementaryData B)),
        Function.support (fun i => F i (elementaryValue A e) (elementaryValue B f)) := by
  classical
  intro i hi
  by_contra hn
  have hz (e : ElementaryData A) (he : e ∈ l)
      (f : ElementaryData B) (hf : f ∈ k) :
      F i (elementaryValue A e) (elementaryValue B f) = 0 := by
    by_contra h
    apply hn
    exact Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨by simpa using he,
      Set.mem_iUnion.mpr ⟨f,Set.mem_iUnion.mpr ⟨by simpa using hf,h⟩⟩⟩⟩
  apply hi
  change F i (l.map (elementaryValue A)).sum (k.map (elementaryValue B)).sum = 0
  rw [bilinear_list_eval]
  apply List.sum_eq_zero
  intro z hz'
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz'
  apply List.sum_eq_zero
  intro z hz'
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hz'
  exact hz e he f hf

/-- Applied separately to the three actual families, before map_finsum.
The two finite unions are over this pair's finite tensor presentations,
which themselves come from dependent direct-sum/algebraic tensor induction. -/
private theorem finite_extension {Z : Type w} [AddCommGroup Z] [Module ℂ Z]
    (F : ℕ → Model A →ₗ[ℂ] Model B →ₗ[ℂ] Z)
    (he : ∀ c d x y n m, Function.HasFiniteSupport
      (fun i => F i (elementary A c x n) (elementary B d y m)))
    (s : Model A) (t : Model B) : Function.HasFiniteSupport (fun i => F i s t) := by
  classical
  obtain ⟨l,hl⟩ := elementary_presentation A s
  obtain ⟨k,hk⟩ := elementary_presentation B t
  rw [hl,hk]
  apply (l.toFinset.finite_toSet.biUnion (fun e _ =>
    k.toFinset.finite_toSet.biUnion (fun f _ =>
      he e.1 f.1 e.2.1 f.2.1 e.2.2 f.2.2))).subset
  exact presentation_support A B F l k

private theorem gram_left : inverseGram positiveG * gramComplex D = 1 :=
  (Classical.choose_spec (LatticePositiveEnergy.complex_inverse_exists D positiveG)).1

private theorem gram_right : gramComplex D * inverseGram positiveG = 1 :=
  (Classical.choose_spec (LatticePositiveEnergy.complex_inverse_exists D positiveG)).2

include positiveG in
/-- Left support, independently extended across both tensor products and
both direct sums. No difference of families enters this assertion. -/
theorem model_left_finite (h : Carrier D) (s : Model A) (t : Model B)
    (p r : ℤ) (τ : ℚ) :
    Function.HasFiniteSupport (fun i => leftFamily A B h p r τ i s t) := by
  apply finite_extension A B (leftFamily A B h p r τ) ?_ s t
  intro c d x y n m
  have hc := (LatticeDualCosetFusion.canonical_lawful D positiveG
    (representative D c) (representative D d) (inverseGram positiveG)
    (gram_left positiveG) (gram_right positiveG)).jacobi h x y p r τ
  apply hc.1.subset
  intro i hi
  change LatticeDualCosetIntertwiner.leftTerm D (representative D c)
    (C c d) h x y p r τ i ≠ 0
  intro hz
  exact hi (by
    change leftFamily A B h p r τ i (elementary A c x n) (elementary B d y m) = 0
    rw [leftFamily_elementary,hz,map_zero])

include positiveG in
/-- First support is finite in its own right. -/
theorem model_first_finite (h : Carrier D) (s : Model A) (t : Model B)
    (p r : ℤ) (τ : ℚ) :
    Function.HasFiniteSupport (fun i => firstFamily A B h p r τ i s t) := by
  apply finite_extension A B (firstFamily A B h p r τ) ?_ s t
  intro c d x y n m
  have hc := (LatticeDualCosetFusion.canonical_lawful D positiveG
    (representative D c) (representative D d) (inverseGram positiveG)
    (gram_left positiveG) (gram_right positiveG)).jacobi h x y p r τ
  apply hc.2.1.subset
  intro i hi
  change LatticeDualCosetIntertwiner.firstTerm D (representative D c) (representative D d)
    (C c d) h x y p r τ i ≠ 0
  intro hz
  exact hi (by
    change firstFamily A B h p r τ i (elementary A c x n) (elementary B d y m) = 0
    rw [firstFamily_elementary,hz,map_zero])

include positiveG in
/-- Second support is finite in its own right, retaining residue epsilon(r). -/
theorem model_second_finite (h : Carrier D) (s : Model A) (t : Model B)
    (p r : ℤ) (τ : ℚ) :
    Function.HasFiniteSupport (fun i => secondFamily A B h p r τ i s t) := by
  apply finite_extension A B (secondFamily A B h p r τ) ?_ s t
  intro c d x y n m
  have hc := (LatticeDualCosetFusion.canonical_lawful D positiveG
    (representative D c) (representative D d) (inverseGram positiveG)
    (gram_left positiveG) (gram_right positiveG)).jacobi h x y p r τ
  apply hc.2.2.1.subset
  intro i hi
  change LatticeDualCosetIntertwiner.secondTerm D (representative D d)
    (C c d) h x y p r τ i ≠ 0
  intro hz
  exact hi (by
    change secondFamily A B h p r τ i (elementary A c x n) (elementary B d y m) = 0
    rw [secondFamily_elementary,hz,map_zero])

private theorem bilinear_ext {Z : Type w} [AddCommGroup Z] [Module ℂ Z]
    {F G : Model A →ₗ[ℂ] Model B →ₗ[ℂ] Z}
    (h : ∀ c d x y n m,
      F (elementary A c x n) (elementary B d y m) =
        G (elementary A c x n) (elementary B d y m)) : F = G := by
  apply DirectSum.linearMap_ext
  intro c
  apply TensorProduct.ext'
  intro x n
  apply DirectSum.linearMap_ext
  intro d
  apply TensorProduct.ext'
  intro y m
  exact h c d x y n m

/-- A family of bilinear maps has a bilinear finsum only after its support
has been proved finite for each actual pair of arguments. -/
private def sumFamily {Z : Type w} [AddCommGroup Z] [Module ℂ Z]
    (F : ℕ → Model A →ₗ[ℂ] Model B →ₗ[ℂ] Z)
    (hf : ∀ s t, Function.HasFiniteSupport (fun i => F i s t)) :
    Model A →ₗ[ℂ] Model B →ₗ[ℂ] Z where
  toFun s :=
    { toFun t := ∑ᶠ i, F i s t
      map_add' t t' := by
        simp only [map_add]
        exact finsum_add_distrib (hf s t) (hf s t')
      map_smul' a t := by
        simp only [map_smul, RingHom.id_apply]
        exact (smul_finsum' a (hf s t)).symm }
  map_add' s s' := by
    apply LinearMap.ext
    intro t
    simp only [map_add, LinearMap.add_apply]
    exact finsum_add_distrib (hf s t) (hf s' t)
  map_smul' a s := by
    apply LinearMap.ext
    intro t
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]
    exact (smul_finsum' a (hf s t)).symm

include positiveG in
/-- Full mixed Jacobi on the constructed classified field. Each of the
three support theorems above precedes every finsum manipulation here. -/
theorem model_mixed_jacobi (h : Carrier D) (s : Model A) (t : Model B)
    (p r : ℤ) (τ : ℚ) :
    (∑ᶠ i, leftFamily A B h p r τ i s t) =
      (∑ᶠ i, firstFamily A B h p r τ i s t) -
        (∑ᶠ i, secondFamily A B h p r τ i s t) := by
  have hL := fun s t => model_left_finite A B positiveG h s t p r τ
  have hF := fun s t => model_first_finite A B positiveG h s t p r τ
  have hS := fun s t => model_second_finite A B positiveG h s t p r τ
  have e : sumFamily A B (leftFamily A B h p r τ) hL =
      sumFamily A B (firstFamily A B h p r τ) hF -
        sumFamily A B (secondFamily A B h p r τ) hS := by
    apply bilinear_ext A B
    intro c d x y n m
    change (∑ᶠ i, leftFamily A B h p r τ i (elementary A c x n) (elementary B d y m)) =
      (∑ᶠ i, firstFamily A B h p r τ i (elementary A c x n) (elementary B d y m)) -
        (∑ᶠ i, secondFamily A B h p r τ i (elementary A c x n) (elementary B d y m))
    simp only [leftFamily_elementary,firstFamily_elementary,secondFamily_elementary]
    have hc := (LatticeDualCosetFusion.canonical_lawful D positiveG
      (representative D c) (representative D d) (inverseGram positiveG)
      (gram_left positiveG) (gram_right positiveG)).jacobi h x y p r τ
    rw [← map_finsum (tag A B c d n m) hc.1,
      ← map_finsum (tag A B c d n m) hc.2.1,
      ← map_finsum (tag A B c d n m) hc.2.2.1, ← map_sub, hc.2.2.2]
  exact congrArg (fun f : Model A →ₗ[ℂ] Model B →ₗ[ℂ] P A B => f s t) e
/-- Translation of the source, proved as a bilinear equality from the literal
canonical derivative at elementary tensors and algebraic extensionality. -/
theorem model_source_translation (τ : ℚ) :
    (modelMode A B τ).comp (translation (canonicalModule A) positiveG) =
      -(τ : ℂ) • modelMode A B (τ-1) := by
  apply bilinear_ext A B
  intro c d x y n m
  change modelMode A B τ
      (translation (canonicalModule A) positiveG (elementary A c x n))
      (elementary B d y m) =
    -(τ : ℂ) • modelMode A B (τ-1) (elementary A c x n) (elementary B d y m)
  simp only [translation,canonical_action_elementary,modelMode_elementary]
  have hc := (LatticeDualCosetFusion.canonical_lawful D positiveG
    (representative D c) (representative D d) (inverseGram positiveG)
    (gram_left positiveG) (gram_right positiveG)).source x τ
  have e := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => tag A B c d n m (f y)) hc
  simpa only [moduleL, neg_add_cancel, LinearMap.smul_apply, map_smul] using e

/-- The target derivative is the actual difference of the two omega zero
modes. Its right side has the same raw rational mode convention. -/
theorem model_target_translation (τ : ℚ) :
    (modelMode A B τ).compr₂ (translation (targetModule A B) positiveG) -
      (modelMode A B τ).compl₂ (translation (canonicalModule B) positiveG) =
        -(τ : ℂ) • modelMode A B (τ-1) := by
  apply bilinear_ext A B
  intro c d x y n m
  change translation (targetModule A B) positiveG
      (modelMode A B τ (elementary A c x n) (elementary B d y m)) -
      modelMode A B τ (elementary A c x n)
        (translation (canonicalModule B) positiveG (elementary B d y m)) =
    -(τ : ℂ) • modelMode A B (τ-1) (elementary A c x n) (elementary B d y m)
  simp only [translation,canonical_action_elementary,modelMode_elementary,target_action_tag]
  have hc := (LatticeDualCosetFusion.canonical_lawful D positiveG
    (representative D c) (representative D d) (inverseGram positiveG)
    (gram_left positiveG) (gram_right positiveG)).target x τ
  have e := congrArg (fun f : Carrier D →ₗ[ℂ] Carrier D => tag A B c d n m (f y)) hc
  simpa only [moduleL,neg_add_cancel,LinearMap.sub_apply,LinearMap.comp_apply,
    LinearMap.smul_apply,map_sub,map_smul] using e

/-- Literal module-action normalization, for use by reconstruction on either
input. Every original VOA state and every integer mode is retained. -/
theorem classified_elementary_action (J : FullJacobiLatticeModule D X)
    (c : Discriminant D) (x h : Carrier D) (n : Multiplicity J c) (k : ℤ) :
    mode J h k (classificationEquiv J positiveG (elementary J c x n)) =
      classificationEquiv J positiveG
        (elementary J c (((action D (representative D c) h)[[k]]) x) n) := by
  rw [← classification,canonical_action_elementary]

/-- Original source action inside the actual elementary raw coefficient. -/
theorem U_source_action_elementary_coeff (c d : Discriminant D)
    (x y h : Carrier D) (n : Multiplicity A c) (m : Multiplicity B d) (k : ℤ) (q : ℚ) :
    (U A B positiveG (mode A h k
      (classificationEquiv A positiveG (elementary A c x n)))).coeff q
      (classificationEquiv B positiveG (elementary B d y m)) =
    DirectSum.lof ℂ _ (PairSector A B) (c,d)
      (((C c d (((action D (representative D c) h)[[k]]) x)).coeff q y) ⊗ₜ[ℂ]
        (n ⊗ₜ[ℂ] m)) := by
  rw [classified_elementary_action,U_elementary_coeff]

/-- Original second-input action inside the actual elementary coefficient. -/
theorem U_input_action_elementary_coeff (c d : Discriminant D)
    (x y h : Carrier D) (n : Multiplicity A c) (m : Multiplicity B d) (k : ℤ) (q : ℚ) :
    (U A B positiveG (classificationEquiv A positiveG (elementary A c x n))).coeff q
      (mode B h k (classificationEquiv B positiveG (elementary B d y m))) =
    DirectSum.lof ℂ _ (PairSector A B) (c,d)
      (((C c d x).coeff q (((action D (representative D d) h)[[k]]) y)) ⊗ₜ[ℂ]
        (n ⊗ₜ[ℂ] m)) := by
  rw [classified_elementary_action,U_elementary_coeff]

/-- Original target action on the actual elementary coefficient. -/
theorem U_target_action_elementary_coeff (c d : Discriminant D)
    (x y h : Carrier D) (n : Multiplicity A c) (m : Multiplicity B d) (k : ℤ) (q : ℚ) :
    mode (targetModule A B) h k
      ((U A B positiveG (classificationEquiv A positiveG (elementary A c x n))).coeff q
        (classificationEquiv B positiveG (elementary B d y m))) =
    DirectSum.lof ℂ _ (PairSector A B) (c,d)
      (((((action D (representative D c + representative D d) h)[[k]]))
        ((C c d x).coeff q y)) ⊗ₜ[ℂ] (n ⊗ₜ[ℂ] m)) := by
  rw [U_elementary_coeff]
  exact target_action_tag A B c d n m h ((C c d x).coeff q y) k

/-- Both arguments of U are actual original vectors, with their own actual
classification inverses. There is no abstract translation assumption. -/
theorem U_source_translation (x : X) (y : Y) (τ : ℚ) :
    (U A B positiveG (translation A positiveG x)).coeff (-τ-1) y =
      -(τ : ℂ) • (U A B positiveG x).coeff (-(τ-1)-1) y := by
  change modelMode A B τ
      ((classificationEquiv A positiveG).symm (translation A positiveG x))
      ((classificationEquiv B positiveG).symm y) =
    -(τ : ℂ) • modelMode A B (τ-1)
      ((classificationEquiv A positiveG).symm x)
      ((classificationEquiv B positiveG).symm y)
  rw [show (classificationEquiv A positiveG).symm (translation A positiveG x) =
    translation (canonicalModule A) positiveG ((classificationEquiv A positiveG).symm x) from
      classification_inverse A positiveG (omega D (inverseGram positiveG)) 0 x]
  exact congrArg (fun f : Model A →ₗ[ℂ] Model B →ₗ[ℂ] P A B =>
    f ((classificationEquiv A positiveG).symm x) ((classificationEquiv B positiveG).symm y))
    (model_source_translation A B positiveG τ)

theorem U_target_translation (x : X) (y : Y) (τ : ℚ) :
    translation (targetModule A B) positiveG ((U A B positiveG x).coeff (-τ-1) y) -
      (U A B positiveG x).coeff (-τ-1) (translation B positiveG y) =
        -(τ : ℂ) • (U A B positiveG x).coeff (-(τ-1)-1) y := by
  change translation (targetModule A B) positiveG
      (modelMode A B τ ((classificationEquiv A positiveG).symm x)
        ((classificationEquiv B positiveG).symm y)) -
      modelMode A B τ ((classificationEquiv A positiveG).symm x)
        ((classificationEquiv B positiveG).symm (translation B positiveG y)) =
    -(τ : ℂ) • modelMode A B (τ-1)
      ((classificationEquiv A positiveG).symm x)
      ((classificationEquiv B positiveG).symm y)
  rw [show (classificationEquiv B positiveG).symm (translation B positiveG y) =
    translation (canonicalModule B) positiveG ((classificationEquiv B positiveG).symm y) from
      classification_inverse B positiveG (omega D (inverseGram positiveG)) 0 y]
  exact congrArg (fun f : Model A →ₗ[ℂ] Model B →ₗ[ℂ] P A B =>
    f ((classificationEquiv A positiveG).symm x) ((classificationEquiv B positiveG).symm y))
    (model_target_translation A B positiveG τ)

/-- The actual left mixed Jacobi family, using the original A action. -/
def leftTerm (h : Carrier D) (x : X) (y : Y) (p r : ℤ) (τ : ℚ) (i : ℕ) : P A B :=
  integerBinomial p i •
    (U A B positiveG (mode A h (r+i) x)).coeff (-((p : ℚ)+τ-i)-1) y

/-- The actual first mixed Jacobi family, using the constructed P action. -/
def firstTerm (h : Carrier D) (x : X) (y : Y) (p r : ℤ) (τ : ℚ) (i : ℕ) : P A B :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    mode (targetModule A B) h (p+r-i) ((U A B positiveG x).coeff (-(τ+i)-1) y)

/-- The actual second family, using the original B action and epsilon(r). -/
def secondTerm (h : Carrier D) (x : X) (y : Y) (p r : ℤ) (τ : ℚ) (i : ℕ) : P A B :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r •
      (U A B positiveG x).coeff (-(τ+r-i)-1) (mode B h (p+i) y))

theorem leftTerm_pullback (h : Carrier D) (x : X) (y : Y)
    (p r : ℤ) (τ : ℚ) (i : ℕ) :
    leftTerm A B positiveG h x y p r τ i = leftFamily A B h p r τ i
      ((classificationEquiv A positiveG).symm x) ((classificationEquiv B positiveG).symm y) := by
  change integerBinomial p i • modelMode A B ((p : ℚ)+τ-i)
    ((classificationEquiv A positiveG).symm (mode A h (r+i) x))
    ((classificationEquiv B positiveG).symm y) = _
  rw [classification_inverse] <;> rfl

theorem firstTerm_pullback (h : Carrier D) (x : X) (y : Y)
    (p r : ℤ) (τ : ℚ) (i : ℕ) :
    firstTerm A B positiveG h x y p r τ i = firstFamily A B h p r τ i
      ((classificationEquiv A positiveG).symm x) ((classificationEquiv B positiveG).symm y) := rfl

theorem secondTerm_pullback (h : Carrier D) (x : X) (y : Y)
    (p r : ℤ) (τ : ℚ) (i : ℕ) :
    secondTerm A B positiveG h x y p r τ i = secondFamily A B h p r τ i
      ((classificationEquiv A positiveG).symm x) ((classificationEquiv B positiveG).symm y) := by
  change (((-1 : ℂ)^i) * integerBinomial r i) •
    (StateFieldResidueReconstruction.epsilon r • modelMode A B (τ+r-i)
      ((classificationEquiv A positiveG).symm x)
      ((classificationEquiv B positiveG).symm (mode B h (p+i) y))) = _
  rw [classification_inverse] <;> rfl

/-- Separate left support on every pair of original vectors. -/
theorem U_left_finite (h : Carrier D) (x : X) (y : Y) (p r : ℤ) (τ : ℚ) :
    Function.HasFiniteSupport (leftTerm A B positiveG h x y p r τ) := by
  change Function.HasFiniteSupport (fun i => leftTerm A B positiveG h x y p r τ i)
  simpa only [leftTerm_pullback] using model_left_finite A B positiveG h
    ((classificationEquiv A positiveG).symm x) ((classificationEquiv B positiveG).symm y) p r τ

/-- Separate first support on every pair of original vectors. -/
theorem U_first_finite (h : Carrier D) (x : X) (y : Y) (p r : ℤ) (τ : ℚ) :
    Function.HasFiniteSupport (firstTerm A B positiveG h x y p r τ) := by
  change Function.HasFiniteSupport (fun i => firstTerm A B positiveG h x y p r τ i)
  simpa only [firstTerm_pullback] using model_first_finite A B positiveG h
    ((classificationEquiv A positiveG).symm x) ((classificationEquiv B positiveG).symm y) p r τ

/-- Separate second support on every pair of original vectors. -/
theorem U_second_finite (h : Carrier D) (x : X) (y : Y) (p r : ℤ) (τ : ℚ) :
    Function.HasFiniteSupport (secondTerm A B positiveG h x y p r τ) := by
  change Function.HasFiniteSupport (fun i => secondTerm A B positiveG h x y p r τ i)
  simpa only [secondTerm_pullback] using model_second_finite A B positiveG h
    ((classificationEquiv A positiveG).symm x) ((classificationEquiv B positiveG).symm y) p r τ

/-- Literal original full mixed Jacobi. The three separately finite families
have already been established; no cancellation is used for their supports. -/
theorem U_mixed_jacobi (h : Carrier D) (x : X) (y : Y) (p r : ℤ) (τ : ℚ) :
    (∑ᶠ i, leftTerm A B positiveG h x y p r τ i) =
      (∑ᶠ i, firstTerm A B positiveG h x y p r τ i) -
        (∑ᶠ i, secondTerm A B positiveG h x y p r τ i) := by
  simpa only [leftTerm_pullback,firstTerm_pullback,secondTerm_pullback] using
    model_mixed_jacobi A B positiveG h ((classificationEquiv A positiveG).symm x)
      ((classificationEquiv B positiveG).symm y) p r τ

end D5.S3.VertexAlgebra.Modules.ActualWeakModuleUniversalField
