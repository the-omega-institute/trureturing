/- GID: D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: General position of one symbolic normal for constant subspace arrangements. -/

import D5.S3.Factorization.Galois.ActualWindowCommonKernel
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
The symbolic normal uses the fraction field of the full multivariate polynomial
ring. The arrangement is defined over the coefficient field before adjoining
the variables. In particular, its members cannot depend on the normal.

The intersection argument uses derivations in an arbitrary rational direction:
if that direction annihilates the cut span, differentiation preserves each cut
and hence both extended uncut spans. Dual separation then proves precisely the
intersection clause of Raz--Wigderson, Definition 5.1, including empty families.
-/

noncomputable section

open scoped TensorProduct

namespace D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition

open ActualWindowCommonKernel.HyperplaneRank

variable {F α ι : Type*} [Field F]

/-- The rational function field with one independent variable per coordinate. -/
abbrev SymbolicField (F α : Type*) [Field F] := FractionRing (MvPolynomial α F)

/-- The actual independent coordinate variables, embedded in the fraction field. -/
def coordinate (j : α) : SymbolicField F α :=
  algebraMap (MvPolynomial α F) (SymbolicField F α) (MvPolynomial.X j)

/-- Coordinatewise scalar inclusion. -/
def constantVector (v : α → F) : α → SymbolicField F α :=
  fun j => algebraMap F (SymbolicField F α) (v j)

/-- Scalar extension of an F-subspace, as an actual span in the new ambient space. -/
def extend (V : Submodule F (α → F)) : Submodule (SymbolicField F α) (α → SymbolicField F α) :=
  Submodule.span _ (constantVector '' (V : Set (α → F)))

/-- One common normal, with all coordinates independently indeterminate. -/
def symbolicNormal [Fintype α] :
    (α → SymbolicField F α) →ₗ[SymbolicField F α] SymbolicField F α where
  toFun v := ∑ j, coordinate j * v j
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_left_comm]

private def direction (y : α → SymbolicField F α) :
    Derivation F (SymbolicField F α) (SymbolicField F α) := by
  let P := MvPolynomial α F
  let K := SymbolicField F α
  letI : Algebra.FormallyEtale P K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  let d := MvPolynomial.mkDerivation F y
  exact ((d.liftKaehlerDifferential.liftBaseChange K).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale F P K).symm.toLinearMap).compDer
      (KaehlerDifferential.D F K)

private theorem direction_coordinate (y : α → SymbolicField F α) (j : α) :
    direction y (coordinate j) = y j := by
  let : Algebra.FormallyEtale (MvPolynomial α F) (SymbolicField F α) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial α F))
  change (MvPolynomial.mkDerivation F y).liftKaehlerDifferential.liftBaseChange
    (SymbolicField F α)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale F (MvPolynomial α F)
      (SymbolicField F α)).symm
        (KaehlerDifferential.D F (SymbolicField F α)
          (algebraMap (MvPolynomial α F) (SymbolicField F α) (MvPolynomial.X j)))) = y j
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp

private def differentiate (d : Derivation F (SymbolicField F α) (SymbolicField F α))
    (v : α → SymbolicField F α) : α → SymbolicField F α := fun j => d (v j)

private theorem differentiate_add (d : Derivation F (SymbolicField F α) (SymbolicField F α))
    (v w : α → SymbolicField F α) :
    differentiate d (v + w) = differentiate d v + differentiate d w := by
  ext j
  exact map_add d _ _

private theorem differentiate_smul (d : Derivation F (SymbolicField F α) (SymbolicField F α))
    (c : SymbolicField F α) (v : α → SymbolicField F α) :
    differentiate d (c • v) = d c • v + c • differentiate d v := by
  ext j
  simp [differentiate, smul_eq_mul, add_comm, mul_comm]

private theorem differentiate_extend (d : Derivation F (SymbolicField F α) (SymbolicField F α))
    (V : Submodule F (α → F)) {v : α → SymbolicField F α} (hv : v ∈ extend V) :
    differentiate d v ∈ extend V := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨a, ha, rfl⟩ := hv
      have hz : differentiate d (constantVector a) = 0 := by
        ext j
        exact d.map_algebraMap _
      rw [hz]
      exact (extend V).zero_mem
  | zero =>
      have hz : differentiate d 0 = 0 := by ext j; exact map_zero d
      rw [hz]
      exact (extend V).zero_mem
  | add v w hv hw ihv ihw =>
      rw [differentiate_add]
      exact (extend V).add_mem ihv ihw
  | smul c v hv ih =>
      rw [differentiate_smul]
      exact (extend V).add_mem ((extend V).smul_mem _ hv) ((extend V).smul_mem _ ih)

open Classical in
private theorem differentiate_normal [Fintype α]
    (ψ : (α → SymbolicField F α) →ₗ[SymbolicField F α]
    SymbolicField F α) (v : α → SymbolicField F α) :
    direction (fun j => ψ (Pi.single j 1)) (symbolicNormal v) =
      symbolicNormal (differentiate (direction (fun j => ψ (Pi.single j 1))) v) + ψ v := by
  classical
  simp only [symbolicNormal, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    Derivation.leibniz, smul_eq_mul, direction_coordinate, Finset.sum_add_distrib]
  congr 1
  conv_rhs => rw [← Finset.univ_sum_single v, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show Pi.single j (v j) = v j • Pi.single j (1 : SymbolicField F α) by
    ext k; simp [Pi.single_apply]]
  simp

private theorem normal_constant_ne_zero [Fintype α] {v : α → F} (hv : v ≠ 0) :
    symbolicNormal (constantVector v) ≠ 0 := by
  classical
  intro hz
  apply hv
  ext j
  have h := congrArg (direction (Pi.single j (1 : SymbolicField F α))) hz
  simp only [symbolicNormal, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    Derivation.leibniz, direction_coordinate, constantVector, Derivation.map_algebraMap,
    smul_eq_mul, mul_zero, zero_add, map_zero, Pi.single_apply] at h
  exact (algebraMap F (SymbolicField F α)).injective (by simpa using h)

private theorem stable_sup {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (D : E → E) (hadd : ∀ x y, D (x + y) = D x + D y)
    {U W : Submodule K E} (hU : ∀ x ∈ U, D x ∈ U) (hW : ∀ x ∈ W, D x ∈ W) :
    ∀ x ∈ U ⊔ W, D x ∈ U ⊔ W := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  rw [hadd]
  exact (U ⊔ W).add_mem
    ((show U ≤ U ⊔ W from le_sup_left) (hU u hu))
    ((show W ≤ U ⊔ W from le_sup_right) (hW w hw))

private theorem stable_finset_sup {K E η : Type*} [Field K] [AddCommGroup E] [Module K E]
    (D : E → E) (hzero : D 0 = 0) (hadd : ∀ x y, D (x + y) = D x + D y)
    (V : η → Submodule K E) (A : Finset η) (hV : ∀ i ∈ A, ∀ x ∈ V i, D x ∈ V i) :
    ∀ x ∈ A.sup V, D x ∈ A.sup V := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using hzero
  | @insert i A hi ih =>
      rw [Finset.sup_insert]
      exact stable_sup D hadd (hV i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hV j (Finset.mem_insert_of_mem hj)))

/-- The exact two-clause general-position predicate for the scalar extensions
of nonzero constant subspaces. A, B and C may be empty, overlap, and contain
indices representing equal subspaces. No genericity antecedent is assumed. -/
theorem symbolic_general_position [Fintype α] [CharZero F] (V : ι → Submodule F (α → F))
    (s : Finset ι) (hV : ∀ i ∈ s, V i ≠ ⊥) :
    InGeneralPosition (fun i => extend (V i)) symbolicNormal s := by
  classical
  constructor
  · intro i hi hker
    obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hV i hi)
    exact normal_constant_ne_zero hne (LinearMap.mem_ker.mp
      (hker (Submodule.subset_span ⟨v, hv, rfl⟩)))
  · intro A hA B hB C hC hker
    let T := cutSpan (fun i => extend (V i)) symbolicNormal A
    let I := (T ⊔ familySpan (fun i => extend (V i)) B) ⊓
      (T ⊔ familySpan (fun i => extend (V i)) C)
    apply le_antisymm _ (le_inf le_sup_left le_sup_left)
    intro w hw
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff T w).mp
    intro ψ hψ
    have hψT : ∀ v ∈ T, ψ v = 0 := (Submodule.mem_dualAnnihilator ψ).mp hψ
    let d := direction (fun j => ψ (Pi.single j 1))
    have hstableT : ∀ v ∈ T, differentiate d v ∈ T := by
      apply stable_finset_sup (differentiate d) (by ext j; exact map_zero d)
        (differentiate_add d)
      intro i hi v hv
      refine ⟨differentiate_extend d (V i) hv.1, LinearMap.mem_ker.mpr ?_⟩
      have hψv : ψ v = 0 := hψT v (Finset.le_sup (f := fun i =>
        extend (V i) ⊓ LinearMap.ker symbolicNormal) hi hv)
      have hd := differentiate_normal ψ v
      rw [LinearMap.mem_ker.mp hv.2, map_zero, hψv, add_zero] at hd
      exact hd.symm
    have hstable (S : Finset ι) : ∀ v ∈ familySpan (fun i => extend (V i)) S,
        differentiate d v ∈ familySpan (fun i => extend (V i)) S :=
      stable_finset_sup (differentiate d) (by ext j; exact map_zero d)
        (differentiate_add d) _ S (fun i _ v hv => differentiate_extend d (V i) hv)
    have hdw : differentiate d w ∈ I :=
      ⟨stable_sup _ (differentiate_add d) hstableT (hstable B) w hw.1,
        stable_sup _ (differentiate_add d) hstableT (hstable C) w hw.2⟩
    have hd := differentiate_normal ψ w
    rw [LinearMap.mem_ker.mp (hker hw), map_zero,
      LinearMap.mem_ker.mp (hker hdw), zero_add] at hd
    exact hd.symm

private theorem generalPosition_comap {K E E' η : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup E'] [Module K E']
    (e : E ≃ₗ[K] E') (V : η → Submodule K E') (φ : E' →ₗ[K] K)
    (s : Finset η) (h : InGeneralPosition V φ s) :
    InGeneralPosition (fun i => (V i).comap e.toLinearMap) (φ.comp e.toLinearMap) s := by
  let L := (Submodule.orderIsoMapComap e).symm
  have hker : L (LinearMap.ker φ) = LinearMap.ker (φ.comp e.toLinearMap) := rfl
  have hspan (A : Finset η) : L (familySpan V A) =
      familySpan (fun i => (V i).comap e.toLinearMap) A := map_finset_sup L A V
  have hcut (A : Finset η) : L (cutSpan V φ A) =
      cutSpan (fun i => (V i).comap e.toLinearMap) (φ.comp e.toLinearMap) A := by
    simp only [cutSpan, map_finset_sup]
    rfl
  constructor
  · intro i hi hle
    apply h.1 i hi
    have hh : L (V i) ≤ L (LinearMap.ker φ) := hle
    simpa only [L.symm_apply_apply] using L.symm.monotone hh
  · intro A hA B hB C hC hle
    have hh : L ((cutSpan V φ A ⊔ familySpan V B) ⊓
        (cutSpan V φ A ⊔ familySpan V C)) ≤ L (LinearMap.ker φ) := by
      simpa only [map_inf, map_sup, hcut, hspan, hker] using hle
    have hbase : (cutSpan V φ A ⊔ familySpan V B) ⊓
        (cutSpan V φ A ⊔ familySpan V C) ≤ LinearMap.ker φ := by
      simpa only [L.symm_apply_apply] using L.symm.monotone hh
    have heq := congrArg L (h.2 A hA B hB C hC hbase)
    simpa only [map_inf, map_sup, hcut, hspan] using heq

private theorem extend_span_range {η : Type*} (v : η → α → F) :
    extend (Submodule.span F (Set.range v)) =
      Submodule.span (SymbolicField F α) (Set.range fun i => constantVector (v i)) := by
  let c : (α → F) →ₗ[F] (α → SymbolicField F α) :=
    { toFun := constantVector
      map_add' := by intro x y; ext j; exact map_add _ _ _
      map_smul' := by intro a x; ext j; simp [constantVector, Algebra.smul_def] }
  change Submodule.span _ (c '' (Submodule.span F (Set.range v) : Set (α → F))) = _
  rw [← Submodule.map_coe, Submodule.map_span, ← Set.range_comp,
    Submodule.span_span_of_tower]
  rfl

section Blocks

variable {β : Type*} {κ : β → Type*} [Fintype β] [∀ i, Fintype (κ i)]

/-- The same base-field rows, before and after adjoining the one common tuple. -/
def liftRows (b : ∀ i, ι → κ i → F) : ∀ i, ι → κ i → SymbolicField F (Σ i, κ i) :=
  fun i σ j => algebraMap F _ (b i σ j)

private theorem blockSpan_liftRows_finrank (b : ∀ i, ι → κ i → F)
    (B : Finset ι) (i : β) :
    Module.finrank (SymbolicField F (Σ i, κ i)) (blockSpan (liftRows b) B i) =
      Module.finrank F (blockSpan b B i) := by
  classical
  -- Use the same scalar extension argument with the full common coordinate field.
  let K := SymbolicField F (Σ i, κ i)
  let V := blockSpan b B i
  let bV := Module.Basis.ofVectorSpace F V
  let _ := bV.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 F V)
  let c : (κ i → F) →ₗ[F] (κ i → K) :=
    { toFun := fun v j => algebraMap F K (v j)
      map_add' := by intro v w; ext j; exact map_add _ _ _
      map_smul' := by intro a v; ext j; simp [Algebra.smul_def] }
  have hspan : Submodule.span F (Set.range fun j => (bV j : κ i → F)) = V := by
    change Submodule.span F (Set.range (V.subtype ∘ bV)) = V
    rw [Set.range_comp, Submodule.span_image, bV.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hli := bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hlift : LinearIndependent K (fun j => c (bV j : κ i → F)) :=
    (linearIndependent_algebraMap_comp_iff (R := F) (S := K)
      (v := fun j => (bV j : κ i → F))).mpr hli
  have hext : Submodule.span K (Set.range fun j => c (bV j : κ i → F)) =
      blockSpan (liftRows b) B i := by
    have hbasis : Submodule.span K (c '' (V : Set (κ i → F))) =
        Submodule.span K (Set.range fun j => c (bV j : κ i → F)) := by
      calc
        _ = Submodule.span K (c '' (Submodule.span F
            (Set.range fun j => (bV j : κ i → F)) : Set (κ i → F))) :=
          congrArg (fun W : Submodule F (κ i → F) =>
            Submodule.span K (c '' (W : Set (κ i → F)))) hspan.symm
        _ = _ := by
          rw [← Submodule.map_coe, Submodule.map_span, ← Set.range_comp,
        Submodule.span_span_of_tower]
          rfl
    rw [← hbasis]
    change Submodule.span K (c '' (Submodule.span F (b i '' (B : Set ι)) : Set _)) = _
    rw [← Submodule.map_coe, Submodule.map_span, Submodule.span_span_of_tower,
      Set.image_image]
    rfl
  change Module.finrank K (blockSpan (liftRows b) B i) = Module.finrank F V
  rw [← hext, finrank_span_eq_card hlift, Module.finrank_eq_card_basis bV]

open Classical in
/-- The common-constraint partition rank with the symbolic GP antecedent
discharged. The rows are arbitrary constant rows, so in particular may be the
actual embedding rows over the normal closure, before adjoining the variables. -/
theorem symbolic_block_common_rows_partition_rank [CharZero F]
    (b : ∀ i, ι → κ i → F) (k : β) (s : Finset ι)
    (hk : ∀ σ ∈ s, b k σ ≠ 0) :
    ∃ P : Finpartition s,
      Module.finrank (SymbolicField F (Σ i, κ i))
        (commonRowSpan (blockRows (liftRows b)) (coefficientNormal coordinate) k s) =
        ∑ B ∈ P.parts,
          ((∑ i, Module.finrank (SymbolicField F (Σ i, κ i)) (blockSpan (liftRows b) B i)) - 1) ∧
      ∀ Q : Finpartition s, Module.finrank (SymbolicField F (Σ i, κ i))
        (commonRowSpan (blockRows (liftRows b)) (coefficientNormal coordinate) k s) ≤
        ∑ B ∈ Q.parts,
          ((∑ i, Module.finrank (SymbolicField F (Σ i, κ i))
            (blockSpan (liftRows b) B i)) - 1) := by
  classical
  let K := SymbolicField F (Σ i, κ i)
  let e : ((i : β) → κ i → K) ≃ₗ[K] ((a : Σ i, κ i) → K) :=
    (LinearEquiv.piCurry K (fun _ _ => K)).symm
  let e₀ : ((i : β) → κ i → F) ≃ₗ[F] ((a : Σ i, κ i) → F) :=
    (LinearEquiv.piCurry F (fun _ _ => F)).symm
  let V : ι → Submodule F ((a : Σ i, κ i) → F) :=
    fun σ => Submodule.span F (Set.range fun i => e₀ (blockRows b σ i))
  have hgen (σ : ι) (i : β) :
      constantVector (e₀ (blockRows b σ i)) = e (blockRows (liftRows b) σ i) := by
    ext ⟨j, l⟩
    by_cases hji : j = i
    · subst j
      simp [constantVector, e, e₀, blockRows, liftRows, Sigma.uncurry]
    · simp [constantVector, e, e₀, blockRows, Sigma.uncurry,
        Pi.single_eq_of_ne hji]
  have hV (σ : ι) (hσ : σ ∈ s) : V σ ≠ ⊥ := by
    intro hbot
    have hv : e₀ (blockRows b σ k) ∈ V σ :=
      Submodule.subset_span (Set.mem_range_self k)
    rw [hbot] at hv
    have heq : blockRows b σ k = 0 := e₀.injective (by simpa using hv)
    apply hk σ hσ
    have heqk := congrFun heq k
    simpa [blockRows] using heqk
  have hext (σ : ι) : extend (V σ) =
      (Submodule.span K (Set.range (blockRows (liftRows b) σ))).map e.toLinearMap := by
    rw [show V σ = Submodule.span F (Set.range fun i => e₀ (blockRows b σ i)) from rfl,
      extend_span_range, Submodule.map_span, ← Set.range_comp]
    congr 1
    exact congrArg Set.range (funext (hgen σ))
  have hnormal : symbolicNormal.comp e.toLinearMap = coefficientNormal
      (coordinate (F := F) (α := Σ i, κ i)) := by
    ext v
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  have hgp := generalPosition_comap e (fun σ => extend (V σ)) symbolicNormal s
    (symbolic_general_position V s hV)
  have hfamily (σ : ι) : (extend (V σ)).comap e.toLinearMap =
      Submodule.span K (Set.range (blockRows (liftRows b) σ)) := by
    rw [hext, Submodule.comap_map_eq_of_injective e.injective]
  simp only [hfamily, hnormal] at hgp
  apply block_common_rows_partition_rank (liftRows b) (coefficientNormal coordinate) k s _ hgp
  intro σ hσ
  have hne : e₀ (blockRows b σ k) ≠ 0 := by
    intro hz
    have heq : blockRows b σ k = 0 := e₀.injective (by simpa using hz)
    exact hk σ hσ (by simpa [blockRows] using congrFun heq k)
  have hn := normal_constant_ne_zero hne
  rw [hgen] at hn
  change (symbolicNormal.comp e.toLinearMap) (blockRows (liftRows b) σ k) ≠ 0 at hn
  rwa [hnormal] at hn

private theorem block_common_rows_linearIndependent
    {K : Type*} {β ι : Type*} [Field K]
    {κ : β → Type*} [Fintype β] [∀ i, Fintype (κ i)]
    (b : ∀ i, ι → κ i → K)
    (φ : ((i : β) → κ i → K) →ₗ[K] K) (k : β) (σ : ι)
    (hu : φ (blockRows b σ k) ≠ 0)
    (hb : ∀ i, b i σ ≠ 0) :
    LinearIndependent K (fun i : {i : β // i ≠ k} =>
      φ (blockRows b σ k) • blockRows b σ (i : β) -
        φ (blockRows b σ (i : β)) • blockRows b σ k) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (hb i)
  have hv := congrFun hc i.1
  have hsum := congrFun hv j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply] at hsum
  have hzero : ∀ x : {i // i ≠ k}, x ≠ i →
      c x • (φ (blockRows b σ k) • blockRows b σ (↑x) (↑i) j -
        φ (blockRows b σ (↑x)) • blockRows b σ k (↑i) j) = 0 := by
    intro x hxi
    have hix : (i : β) ≠ (x : β) := by
      intro heq
      exact hxi (Subtype.ext heq.symm)
    simp [blockRows, Pi.single_eq_of_ne hix, Pi.single_eq_of_ne i.property]
  have hsum_single := Finset.sum_eq_single (s := Finset.univ) i
    (fun x _ hxi => hzero x hxi) (by simp)
  rw [hsum_single] at hsum
  simp [blockRows, Pi.single_eq_same, Pi.single_eq_of_ne i.property,
    smul_eq_mul] at hsum
  rcases hsum with hci | hu0 | hj0
  · exact hci
  · exact False.elim (hu (by simpa [blockRows] using hu0))
  · exact False.elim (hj (by simpa using hj0))

private theorem block_common_rows_span_basis
    {K : Type*} {β ι : Type*} [Field K]
    {κ : β → Type*} [Fintype β] [∀ i, Fintype (κ i)]
    (b : ∀ i, ι → κ i → K)
    (φ : ((i : β) → κ i → K) →ₗ[K] K) (k : β) (σ : ι)
    (hu : φ (blockRows b σ k) ≠ 0) :
    Submodule.span K (Set.range (fun i : {i : β // i ≠ k} =>
      φ (blockRows b σ k) • blockRows b σ (i : β) -
        φ (blockRows b σ (i : β)) • blockRows b σ k)) =
      Submodule.span K (Set.range (blockRows b σ)) ⊓ LinearMap.ker φ := by
  have hall := span_common_rows_eq_cut (blockRows b σ) φ k hu
  have hsub : Submodule.span K (Set.range (fun i : {i : β // i ≠ k} =>
      φ (blockRows b σ k) • blockRows b σ (i : β) -
        φ (blockRows b σ (i : β)) • blockRows b σ k)) =
      Submodule.span K (Set.range (fun i : β =>
      φ (blockRows b σ k) • blockRows b σ i -
        φ (blockRows b σ i) • blockRows b σ k)) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨(i : β), rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hik : i = k
      · subst i
        simp
      · exact Submodule.subset_span ⟨⟨i, hik⟩, rfl⟩
  rw [hsub, hall]

open Classical in
/-- The full symbolic (31.6)--(31.7) assertion: for one common independent
coefficient tuple, the displayed non-distinguished rows are a basis of each
scalar-extended block space cut by the same hyperplane, and their total span
has the attained minimum partition rank. -/
theorem symbolic_block_common_rows_basis_partition_rank [CharZero F]
    (b : ∀ i, ι → κ i → F) (k : β) (s : Finset ι)
    (hrows : ∀ σ ∈ s, ∀ i, b i σ ≠ 0) :
    ∃ P : Finpartition s,
      (∀ σ ∈ s,
        (∀ i, coefficientNormal (coordinate (F := F) (α := Σ i, κ i))
            (blockRows (liftRows b) σ i) ≠ 0) ∧
        LinearIndependent (SymbolicField F (Σ i, κ i))
          (fun i : {i // i ≠ k} =>
            coefficientNormal (coordinate (F := F) (α := Σ i, κ i)) (blockRows (liftRows b) σ k) •
                blockRows (liftRows b) σ (i : β) -
              coefficientNormal (coordinate (F := F) (α := Σ i, κ i)) (blockRows (liftRows b) σ (i : β)) •
                blockRows (liftRows b) σ k) ∧
        Submodule.span (SymbolicField F (Σ i, κ i))
            (Set.range (fun i : {i // i ≠ k} =>
              coefficientNormal (coordinate (F := F) (α := Σ i, κ i)) (blockRows (liftRows b) σ k) •
                  blockRows (liftRows b) σ (i : β) -
                coefficientNormal (coordinate (F := F) (α := Σ i, κ i)) (blockRows (liftRows b) σ (i : β)) •
                  blockRows (liftRows b) σ k)) =
          Submodule.span (SymbolicField F (Σ i, κ i))
            (Set.range (blockRows (liftRows b) σ)) ⊓
            LinearMap.ker (coefficientNormal (coordinate (F := F) (α := Σ i, κ i)))) ∧
      Module.finrank (SymbolicField F (Σ i, κ i))
          (commonRowSpan (blockRows (liftRows b)) (coefficientNormal (coordinate (F := F) (α := Σ i, κ i))) k s) =
        ∑ B ∈ P.parts,
          ((∑ i, Module.finrank F (blockSpan b B i)) - 1) ∧
      ∀ Q : Finpartition s,
        Module.finrank (SymbolicField F (Σ i, κ i))
            (commonRowSpan (blockRows (liftRows b)) (coefficientNormal (coordinate (F := F) (α := Σ i, κ i))) k s) ≤
          ∑ B ∈ Q.parts,
            ((∑ i, Module.finrank F (blockSpan b B i)) - 1) := by
  classical
  let K := SymbolicField F (Σ i, κ i)
  let e : ((i : β) → κ i → K) ≃ₗ[K] ((a : Σ i, κ i) → K) :=
    (LinearEquiv.piCurry K (fun _ _ => K)).symm
  let e₀ : ((i : β) → κ i → F) ≃ₗ[F] ((a : Σ i, κ i) → F) :=
    (LinearEquiv.piCurry F (fun _ _ => F)).symm
  have hgen (σ : ι) (i : β) :
      constantVector (e₀ (blockRows b σ i)) =
        e (blockRows (liftRows b) σ i) := by
    ext ⟨j, l⟩
    by_cases hji : j = i
    · subst j
      simp [constantVector, e, e₀, blockRows, liftRows, Sigma.uncurry]
    · simp [constantVector, e, e₀, blockRows, liftRows, Sigma.uncurry,
        Pi.single_eq_of_ne hji]
  have hnormal : symbolicNormal.comp e.toLinearMap =
      coefficientNormal (coordinate (F := F) (α := Σ i, κ i)) := by
    ext v
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  have hUi : ∀ σ ∈ s, ∀ i,
      coefficientNormal (coordinate (F := F) (α := Σ i, κ i)) (blockRows (liftRows b) σ i) ≠ 0 := by
    intro σ hσ i
    have hbase : e₀ (blockRows b σ i) ≠ 0 := by
      intro hz
      apply hrows σ hσ i
      apply funext
      intro j
      have hzero : blockRows b σ i = 0 := e₀.injective (by simpa using hz)
      have hj := congrFun (congrFun hzero i) j
      simpa [blockRows] using hj
    have hn := normal_constant_ne_zero hbase
    rw [hgen] at hn
    change (symbolicNormal.comp e.toLinearMap)
        (blockRows (liftRows b) σ i) ≠ 0 at hn
    rwa [hnormal] at hn
  obtain ⟨P, hP, hbound⟩ := symbolic_block_common_rows_partition_rank b k s
    (fun σ hσ => hrows σ hσ k)
  simp only [blockSpan_liftRows_finrank] at hP hbound
  refine ⟨P, ?_, hP, hbound⟩
  intro σ hσ
  have hbaseRows : ∀ i, liftRows b i σ ≠ 0 := by
    intro i hz
    apply hrows σ hσ i
    apply funext
    intro j
    have hj := congrFun hz j
    simpa [liftRows] using hj
  refine ⟨hUi σ hσ, ?_, ?_⟩
  · exact block_common_rows_linearIndependent (liftRows b)
      (coefficientNormal (coordinate (F := F) (α := Σ i, κ i))) k σ
      (hUi σ hσ k) hbaseRows
  · exact block_common_rows_span_basis (liftRows b)
      (coefficientNormal (coordinate (F := F) (α := Σ i, κ i))) k σ
      (hUi σ hσ k)

end Blocks

#print axioms symbolic_general_position
#print axioms symbolic_block_common_rows_partition_rank
#print axioms symbolic_block_common_rows_basis_partition_rank

end D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition
