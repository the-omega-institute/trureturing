/- GID: D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full actual six-coordinate kernel/projection/lift geometry and orthogonality. -/

import D5.S3.Combinatorics.Orthogonality.SplitSubmoduleLift
import D5.S3.Combinatorics.Orthogonality.SixBitSubmoduleBridge
import D5.S3.Combinatorics.Orthogonality.GaussianSubspaceCount
import D5.S3.Combinatorics.Orthogonality.OrthogonalityDegreeDeletion
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! The two complementary spaces are exactly the source spans of masks
3,12,48 and 1,4,16. Every submodule, including zero and the whole space,
has its complete placement map. Orthogonality retains the full placement
data and does not assert a successful profile-only coloring rule. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Orthogonality.SixDimensionalLiftGeometry

open Matrix
open scoped CharTwo
open SplitSubmoduleLift

abbrev F := ZMod 2
abbrev A := Fin 3 → F
abbrev V := Fin 6 → F

/-- Coordinates t+s in the fixed source splitting. -/
def coordinates : (A × A) ≃ₗ[F] V where
  toFun p := ![p.1 0 + p.2 0, p.1 0, p.1 1 + p.2 1, p.1 1,
    p.1 2 + p.2 2, p.1 2]
  invFun v := (![v 1,v 3,v 5], ![v 0 + v 1,v 2 + v 3,v 4 + v 5])
  left_inv p := by
    ext i <;> fin_cases i <;> simp [add_assoc, add_comm, add_left_comm]
  right_inv v := by
    ext i
    fin_cases i <;> simp [add_assoc, add_comm, add_left_comm]
  map_add' p q := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c p := by
    ext i
    fin_cases i <;> simp [mul_add]

/-- The exact coordinate bilinear form, with the T-T term cancelled in F2. -/
theorem coordinates_dot (p q : A × A) :
    dotProduct (coordinates p) (coordinates q) =
      dotProduct p.1 q.2 + dotProduct p.2 q.1 + dotProduct p.2 q.2 := by
  simp [coordinates, dotProduct, Fin.sum_univ_succ]
  ring_nf
  simp only [show (2 : F) = 0 by decide, mul_zero, add_zero, zero_add]

private def firstEmbedding : A →ₗ[F] V :=
  coordinates.toLinearMap.comp (LinearMap.inl F A A)

private def secondEmbedding : A →ₗ[F] V :=
  coordinates.toLinearMap.comp (LinearMap.inr F A A)

/-- The actual fixed totally isotropic space. -/
def T : Submodule F V := firstEmbedding.range

/-- The actual specified complementary space. -/
def S : Submodule F V := secondEmbedding.range

private theorem range_basis (f : A →ₗ[F] V) :
    f.range = Submodule.span F (Set.range fun i : Fin 3 => f (Pi.basisFun F (Fin 3) i)) := by
  rw [← Submodule.map_top, ← (Pi.basisFun F (Fin 3)).span_eq,
    Submodule.map_span]
  congr 1
  ext v
  simp

/-- This is the original mask span, not an arbitrary convenient isotropic space. -/
theorem T_source : T = Submodule.span F
    {SixBitSubmoduleBridge.bits 3, SixBitSubmoduleBridge.bits 12,
      SixBitSubmoduleBridge.bits 48} := by
  rw [T, range_basis]
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  have he : ∀ i : Fin 3, firstEmbedding (Pi.basisFun F (Fin 3) i) =
      ![SixBitSubmoduleBridge.bits 3, SixBitSubmoduleBridge.bits 12,
        SixBitSubmoduleBridge.bits 48] i := by
    intro i
    ext j
    fin_cases i <;> fin_cases j <;>
      norm_num [firstEmbedding, secondEmbedding, coordinates, Pi.basisFun_apply,
        SixBitSubmoduleBridge.bits]
  simp_rw [he]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

/-- This is the original mask complement. -/
theorem S_source : S = Submodule.span F
    {SixBitSubmoduleBridge.bits 1, SixBitSubmoduleBridge.bits 4,
      SixBitSubmoduleBridge.bits 16} := by
  rw [S, range_basis]
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  have he : ∀ i : Fin 3, secondEmbedding (Pi.basisFun F (Fin 3) i) =
      ![SixBitSubmoduleBridge.bits 1, SixBitSubmoduleBridge.bits 4,
        SixBitSubmoduleBridge.bits 16] i := by
    intro i
    ext j
    fin_cases i <;> fin_cases j <;>
      norm_num [firstEmbedding, secondEmbedding, coordinates, Pi.basisFun_apply,
        SixBitSubmoduleBridge.bits]
  simp_rw [he]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

def split (U : Submodule F V) : Submodule F (A × A) :=
  U.comap coordinates.toLinearMap

def K (U : Submodule F V) : Submodule F A := firstKernel (split U)
def P (U : Submodule F V) : Submodule F A := secondRange (split U)

/-- The dimension in the exact source profile is recovered from K and P. -/
theorem dimension_profile (U : Submodule F V) :
    Module.finrank F U = Module.finrank F (K U) + Module.finrank F (P U) := by
  have he := (coordinates.ofSubmodule' U).finrank_eq
  exact he.symm.trans (SplitSubmoduleLift.finrank_split (split U))

/-- The annihilator of the full projection, in the fixed T coordinates. -/
def H (U : Submodule F V) : Submodule F A :=
  (LinearMap.BilinForm.orthogonal (dotProductBilin F F : A →ₗ[F] A →ₗ[F] F)) (P U)

/-- The source K is exactly the actual intersection with T. -/
theorem K_source (U : Submodule F V) :
    (K U).map firstEmbedding = U ⊓ T := by
  ext v
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨ha,⟨a,rfl⟩⟩
  · rintro ⟨hu,a,rfl⟩
    exact ⟨a,hu,rfl⟩

/-- The source H is exactly U-perpendicular intersected with the specified T. -/
theorem H_source (U : Submodule F V) :
    (H U).map firstEmbedding = (LinearMap.BilinForm.orthogonal (dotProductBilin F F : V →ₗ[F] V →ₗ[F] F)) U ⊓ T := by
  ext v
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨?_,⟨a,rfl⟩⟩
    intro u hu
    let w := coordinates.symm u
    have hw : w ∈ split U := by
      change coordinates w ∈ U
      simpa [w] using hu
    have hp : w.2 ∈ P U := ⟨w,hw,rfl⟩
    have hh := ha w.2 hp
    change dotProduct w.2 a = 0 at hh
    change dotProduct u (firstEmbedding a) = 0
    rw [dotProduct_comm]
    rw [← coordinates.apply_symm_apply u]
    change dotProduct (coordinates (a,0)) (coordinates w) = 0
    simpa only [coordinates_dot, dotProduct_zero, zero_dotProduct, zero_add,
      add_zero, dotProduct_comm] using hh
  · rintro ⟨hu,a,rfl⟩
    refine ⟨a,?_,rfl⟩
    intro p hp
    obtain ⟨w,hw,he⟩ := hp
    have he' : w.2 = p := he
    have hh := hu (coordinates w) hw
    change dotProduct (coordinates w) (coordinates (a,0)) = 0 at hh
    rw [dotProduct_comm] at hh
    rw [coordinates_dot] at hh
    change dotProduct p a = 0
    rw [dotProduct_comm]
    simpa only [dotProduct_zero, zero_dotProduct, zero_add, add_zero, he'] using hh

private theorem pairing_nondegenerate :
    (dotProductBilin F F : A →ₗ[F] A →ₗ[F] F).Nondegenerate := by
  exact (show (dotProductBilin F F : A →ₗ[F] A →ₗ[F] F).IsSymm from
    ⟨dotProduct_comm⟩).isRefl.nondegenerate_iff_separatingLeft.mpr
      (fun x hx => dotProduct_eq_zero x hx)

/-- The perfect T-S pairing loses no projection information. -/
theorem projection_recovered (U : Submodule F V) :
    (LinearMap.BilinForm.orthogonal (dotProductBilin F F : A →ₗ[F] A →ₗ[F] F)) (H U) = P U := by
  exact LinearMap.BilinForm.orthogonal_orthogonal pairing_nondegenerate
    (show (dotProductBilin F F : A →ₗ[F] A →ₗ[F] F).IsRefl from
      (show (dotProductBilin F F : A →ₗ[F] A →ₗ[F] F).IsSymm from
        ⟨dotProduct_comm⟩).isRefl) (P U)

/-- Exact profile data and the actual kernel/projection pair determine one another. -/
theorem profile_iff (U W : Submodule F V) :
    K U = K W ∧ P U = P W ↔
      Module.finrank F U = Module.finrank F W ∧ K U = K W ∧ H U = H W := by
  constructor
  · rintro ⟨hk,hp⟩
    refine ⟨?_,hk,congrArg
      (LinearMap.BilinForm.orthogonal (dotProductBilin F F : A →ₗ[F] A →ₗ[F] F)) hp⟩
    rw [dimension_profile U, dimension_profile W, hk, hp]
  · rintro ⟨_,hk,hh⟩
    exact ⟨hk,(projection_recovered U).symm.trans
      ((congrArg (LinearMap.BilinForm.orthogonal (dotProductBilin F F : A →ₗ[F] A →ₗ[F] F)) hh).trans (projection_recovered W))⟩

/-- Every full placement map represents an actual coordinate submodule. -/
def represented (K : Submodule F A) (P : Submodule F A)
    (f : P →ₗ[F] A ⧸ K) : Submodule F V :=
  (liftSpace K P f).map coordinates.toLinearMap

/-- Every actual submodule is reconstructed, with unique full placement data. -/
theorem reconstruction (U : Submodule F V) :
    ∃! f : P U →ₗ[F] A ⧸ K U, represented (K U) (P U) f = U := by
  obtain ⟨f,hf,hu⟩ := SplitSubmoduleLift.reconstruction (split U)
  refine ⟨f,?_,?_⟩
  · change (liftSpace _ _ f).map coordinates.toLinearMap = U
    rw [hf]
    exact Submodule.map_comap_eq_of_surjective coordinates.surjective U
  · intro g hg
    apply hu g
    apply Submodule.map_injective_of_injective coordinates.injective
    exact hg.trans (Submodule.map_comap_eq_of_surjective coordinates.surjective U).symm

private def form : (A × A) →ₗ[F] (A × A) →ₗ[F] F :=
  (dotProductBilin F F).compl₁₂ coordinates.toLinearMap coordinates.toLinearMap

/-- The source X,Y,Z criterion on the entire actual reconstructed submodules. -/
theorem orthogonal_iff
    (K L : Submodule F A) (P Q : Submodule F A)
    (f : P →ₗ[F] A ⧸ K) (g : Q →ₗ[F] A ⧸ L)
    (F' : P →ₗ[F] A) (G' : Q →ₗ[F] A)
    (hF : K.mkQ.comp F' = f) (hG : L.mkQ.comp G' = g) :
    (∀ u ∈ represented K P f, ∀ w ∈ represented L Q g, dotProduct u w = 0) ↔
      (∀ k ∈ K, ∀ q : Q, dotProduct k q.val = 0) ∧
      (∀ p : P, ∀ l ∈ L, dotProduct p.val l = 0) ∧
      (∀ (p : P) (q : Q), dotProduct p.val q.val +
        dotProduct (F' p) q.val + dotProduct p.val (G' q) = 0) := by
  have hA : ∀ a a' : A, form (a,0) (a',0) = 0 := by
    intro a a'
    change dotProduct (coordinates (a,0)) (coordinates (a',0)) = 0
    rw [coordinates_dot]
    simp
  have hs := SplitSubmoduleLift.orthogonal_iff form hA K L P Q f g F' G' hF hG
  have hb : ∀ x y : A × A, form x y =
      dotProduct x.1 y.2 + dotProduct x.2 y.1 + dotProduct x.2 y.2 :=
    coordinates_dot
  have hm : (∀ u ∈ represented K P f, ∀ w ∈ represented L Q g,
      dotProduct u w = 0) ↔
      ∀ x ∈ liftSpace K P f, ∀ y ∈ liftSpace L Q g, form x y = 0 := by
    constructor
    · intro h x hx y hy
      exact h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    · intro h u hu w hw
      obtain ⟨x,hx,he⟩ := hu
      obtain ⟨y,hy,hf⟩ := hw
      subst u
      subst w
      exact h x hx y hy
  rw [hm,hs]
  simp only [hb, Prod.fst, Prod.snd, dotProduct_zero, zero_dotProduct, zero_add, add_zero]

/-- Full source fiber count in the original six-coordinate object domain. -/
theorem profile_card (K : Submodule F A) (P : Submodule F A) :
    Nat.card {U : Submodule F V // SixDimensionalLiftGeometry.K U = K ∧
      SixDimensionalLiftGeometry.P U = P} =
      2 ^ (Module.finrank F P * (3 - Module.finrank F K)) := by
  let e := Submodule.orderIsoMapComap coordinates
  let e' : {U : Submodule F (A × A) // firstKernel U = K ∧ secondRange U = P} ≃
      {U : Submodule F V // SixDimensionalLiftGeometry.K U = K ∧
        SixDimensionalLiftGeometry.P U = P} :=
    e.toEquiv.subtypeEquiv (by
      intro U
      change (firstKernel U = K ∧ secondRange U = P) ↔
        firstKernel (split (e U)) = K ∧ secondRange (split (e U)) = P
      have he : split (e U) = U := e.symm_apply_apply U
      rw [he])
  rw [← Nat.card_congr e', SplitSubmoduleLift.fiber_card]
  simp [F,A,Module.finrank_pi]

/-- Intersection with the original complement is exactly the actual kernel
of the full placement map, in its original projection domain. -/
theorem complement_kernel (K : Submodule F A) (P : Submodule F A)
    (f : P →ₗ[F] A ⧸ K) :
    (represented K P f).comap secondEmbedding = (LinearMap.ker f).map P.subtype := by
  have hm : (represented K P f).comap coordinates.toLinearMap = liftSpace K P f :=
    Submodule.comap_map_eq_of_injective coordinates.injective _
  have he := congrArg (Submodule.comap (LinearMap.inr F A A)) hm
  exact he.trans (secondKernel_liftSpace K P f)

/-- The annihilator dimension is recovered from the entire projection. -/
theorem annihilator_dimension (U : Submodule F V) :
    Module.finrank F (H U) = 3 - Module.finrank F (P U) := by
  have hd : Module.finrank F A = 3 := by simp [F,A]
  exact (LinearMap.BilinForm.finrank_orthogonal pairing_nondegenerate (P U)).trans
    (congrArg (fun d => d - Module.finrank F (P U)) hd)

/-- The full projection vanishes exactly on the fixed clique subspace. -/
theorem projection_eq_bot_iff (U : Submodule F V) : P U = ⊥ ↔ U ≤ T := by
  constructor
  · intro h u hu
    let w := coordinates.symm u
    have hw : w ∈ split U := by
      change coordinates w ∈ U
      simpa [w] using hu
    have hp : w.2 ∈ P U := ⟨w,hw,rfl⟩
    rw [h] at hp
    have hz : w.2 = 0 := hp
    refine ⟨w.1,?_⟩
    change coordinates (w.1,0) = u
    simpa only [← hz,Prod.eta] using coordinates.apply_symm_apply u
  · intro h
    apply eq_bot_iff.mpr
    rintro p ⟨w,hw,rfl⟩
    obtain ⟨a,he⟩ := h hw
    have hc : (a,(0 : A)) = w := coordinates.injective he
    change w.2 = 0
    exact (congrArg Prod.snd hc).symm

/-- Every nonclique vertex has precisely one of the three source annihilator
dimensions. No proper-profile hypothesis is separately assumed. -/
theorem nonclique_annihilator_dimension (U : Submodule F V) (hU : ¬ U ≤ T) :
    Module.finrank F (H U) ≤ 2 := by
  have hH : H U ≠ ⊤ := by
    intro hH
    apply hU
    apply (projection_eq_bot_iff U).mp
    rw [← projection_recovered U,hH]
    exact LinearMap.BilinForm.orthogonal_top_eq_bot pairing_nondegenerate
  have hd := Submodule.finrank_lt hH
  have hA : Module.finrank F A = 3 := by simp [F,A]
  omega

private theorem first_injective : Function.Injective firstEmbedding := by
  intro a b h
  have he : (a,(0 : A)) = (b,0) := coordinates.injective h
  exact congrArg Prod.fst he

/-- The source labels are all nonzero subspaces of the specified T. -/
abbrev Label := {L : Submodule F A // L ≠ ⊥}

private theorem label_map_ne_bot (L : Label) :
    L.val.map firstEmbedding ≠ ⊥ := by
  intro h
  apply L.property
  apply le_antisymm _ bot_le
  intro a ha
  have hm : firstEmbedding a ∈ L.val.map firstEmbedding := ⟨a,ha,rfl⟩
  rw [h] at hm
  change a = 0
  apply first_injective
  simpa only [map_zero,Submodule.mem_bot] using hm

/-- The actual clique vertex represented by a source label. -/
def labelVertex (L : Label) : NikandishClique.Vertex 6 :=
  ⟨L.val.map firstEmbedding,label_map_ne_bot L⟩

private theorem label_below_T (L : Label) : (labelVertex L).val ≤ T := by
  rintro v ⟨a,_,rfl⟩
  exact ⟨a,rfl⟩

private theorem label_injective : Function.Injective labelVertex := by
  intro L M h
  apply Subtype.ext
  apply Submodule.map_injective_of_injective first_injective
  exact congrArg Subtype.val h

/-- Exact cardinality of the complete original clique-label domain. -/
theorem label_card : Nat.card Label = 15 := by
  change NikandishClique.nonzeroSubspaceCount 3 = 15
  rw [GaussianSubspaceCount.result]
  norm_num [GaussianSubspaceCount.gaussian, Finset.sum_Icc_succ_top,
    Fin.prod_univ_succ]

/-- Full list cardinality for every submodule, including degenerate profiles. -/
theorem allowed_label_card (U : Submodule F V) :
    Nat.card {L : Label // ¬ L.val ≤ H U} =
      15 - NikandishClique.nonzeroSubspaceCount (Module.finrank F (H U)) := by
  classical
  letI : Fintype Label := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, label_card]
  rw [OrthogonalityDegreeDeletion.below_card]

/-- The three original list sizes at annihilator dimensions zero, one and two. -/
theorem allowed_label_sizes (U : Submodule F V) :
    (Module.finrank F (H U) = 0 → Nat.card {L : Label // ¬ L.val ≤ H U} = 15) ∧
    (Module.finrank F (H U) = 1 → Nat.card {L : Label // ¬ L.val ≤ H U} = 14) ∧
    (Module.finrank F (H U) = 2 → Nat.card {L : Label // ¬ L.val ≤ H U} = 11) := by
  have hn (d : ℕ) : NikandishClique.nonzeroSubspaceCount d =
      ∑ k ∈ Finset.Icc 1 d, GaussianSubspaceCount.gaussian d k :=
    GaussianSubspaceCount.result d
  repeat' constructor
  all_goals
    intro hd
    rw [allowed_label_card,hd,hn]
    norm_num [GaussianSubspaceCount.gaussian, Finset.sum_Icc_succ_top,
      Fin.prod_univ_succ]

/-- Availability is exactly the nonvanishing pairing with the full projection. -/
theorem label_orthogonal_iff (U : Submodule F V) (L : Label) :
    (∀ u ∈ U, ∀ w ∈ (labelVertex L).val, dotProduct u w = 0) ↔
      L.val ≤ H U := by
  constructor
  · intro h a ha
    have hm : firstEmbedding a ∈ (LinearMap.BilinForm.orthogonal (dotProductBilin F F : V →ₗ[F] V →ₗ[F] F)) U ⊓ T := by
      refine ⟨?_,⟨a,rfl⟩⟩
      intro u hu
      change dotProduct u (firstEmbedding a) = 0
      exact h u hu _ ⟨a,ha,rfl⟩
    rw [← H_source U] at hm
    obtain ⟨b,hb,he⟩ := hm
    exact first_injective he ▸ hb
  · intro h u hu w hw
    obtain ⟨a,ha,rfl⟩ := hw
    have hm : firstEmbedding a ∈ (H U).map firstEmbedding := ⟨a,h ha,rfl⟩
    rw [H_source U] at hm
    have hh := hm.1 u hu
    exact hh

/-- The full source precolored-label criterion. It quantifies every actual
vertex and every normalized assignment; it supplies no successful rule. The
second clause is exactly the X/Y/Z test under `orthogonal_iff`. -/
theorem precolor_criterion
    (c : NikandishClique.Vertex 6 → Label)
    (hc : ∀ U, U.val ≤ T → labelVertex (c U) = U) :
    (∀ U W, (NikandishClique.orthogonalityGraph 6).Adj U W → c U ≠ c W) ↔
      (∀ U, ¬ U.val ≤ T → ¬ (c U).val ≤ H U.val) ∧
      (∀ U W, ¬ U.val ≤ T → ¬ W.val ≤ T → U ≠ W → c U = c W →
        ¬ (∀ u ∈ U.val, ∀ w ∈ W.val, dotProduct u w = 0)) := by
  have hl (L : Label) : c (labelVertex L) = L :=
    label_injective (hc (labelVertex L) (label_below_T L))
  constructor
  · intro hp
    refine ⟨?_,?_⟩
    · intro U hU hle
      have hne : U ≠ labelVertex (c U) := by
        intro he
        exact hU (he.symm ▸ label_below_T (c U))
      have ha : (NikandishClique.orthogonalityGraph 6).Adj U (labelVertex (c U)) :=
        ⟨hne,(label_orthogonal_iff U.val (c U)).mpr hle⟩
      exact hp _ _ ha (hl (c U)).symm
    · intro U W _ _ hne he ho
      exact hp U W ⟨hne,ho⟩ he
  · rintro ⟨ha,hb⟩ U W hUW he
    by_cases hU : U.val ≤ T
    · have hu : labelVertex (c U) = U := hc U hU
      by_cases hW : W.val ≤ T
      · have hw := hc W hW
        exact hUW.1 (hu.symm.trans ((congrArg labelVertex he).trans hw))
      · apply ha W hW
        apply (label_orthogonal_iff W.val (c W)).mp
        rw [← he,hu]
        intro w hw u hu'
        rw [dotProduct_comm]
        exact hUW.2 u hu' w hw
    · by_cases hW : W.val ≤ T
      · apply ha U hU
        apply (label_orthogonal_iff U.val (c U)).mp
        rw [he,hc W hW]
        exact hUW.2
      · exact hb U W hU hW hUW.1 he hUW.2

#print axioms reconstruction
#print axioms orthogonal_iff
#print axioms profile_card
#print axioms precolor_criterion
end D5.S3.Combinatorics.Orthogonality.SixDimensionalLiftGeometry
