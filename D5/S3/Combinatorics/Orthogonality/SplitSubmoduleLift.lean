/- GID: D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SplitSubmoduleLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact kernel/projection/quotient-lift reconstruction of every split submodule. -/

import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! The split representation is the full K/P/f representation in the
Nikandish/Ma/Zhang six-dimensional geometry, over an arbitrary field and
arbitrary complementary coordinate spaces. It constructs the lift map from
an actual submodule; no reconstruction or target conclusion is assumed.
The fixed six-dimensional orthogonality consumer must additionally bind the
specified T and S and its coordinate bilinear form. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Orthogonality.SplitSubmoduleLift

variable {𝕜 A B : Type*} [Field 𝕜] [AddCommGroup A] [Module 𝕜 A]
  [AddCommGroup B] [Module 𝕜 B]

/-- Actual intersection with the first summand, in that summand's coordinates. -/
def firstKernel (U : Submodule 𝕜 (A × B)) : Submodule 𝕜 A :=
  U.comap (LinearMap.inl 𝕜 A B)

/-- Actual projection onto the second summand. -/
def secondRange (U : Submodule 𝕜 (A × B)) : Submodule 𝕜 B :=
  U.map (LinearMap.snd 𝕜 A B)

private def projection (U : Submodule 𝕜 (A × B)) : U →ₗ[𝕜] secondRange U where
  toFun u := ⟨u.val.2, ⟨u.val,u.property,rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem projection_surjective (U : Submodule 𝕜 (A × B)) :
    Function.Surjective (projection U) := by
  rintro ⟨s,hs⟩
  obtain ⟨u,hu,he⟩ := hs
  exact ⟨⟨u,hu⟩,Subtype.ext he⟩

/-- Rank-nullity for the actual kernel and full second projection. -/
theorem finrank_split [FiniteDimensional 𝕜 A] [FiniteDimensional 𝕜 B]
    (U : Submodule 𝕜 (A × B)) :
    Module.finrank 𝕜 U =
      Module.finrank 𝕜 (firstKernel U) + Module.finrank 𝕜 (secondRange U) := by
  let e : firstKernel U ≃ₗ[𝕜] LinearMap.ker (projection U) :=
    { toFun := fun a => ⟨⟨(a.val,0),a.property⟩,Subtype.ext rfl⟩
      invFun := fun u => ⟨u.val.val.1,by
        have hz : u.val.val.2 = 0 := congrArg Subtype.val u.property
        change (u.val.val.1,0) ∈ U
        simpa only [← hz, Prod.eta] using u.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun u => by
        apply Subtype.ext
        apply Subtype.ext
        change (u.val.val.1, (0 : B)) = u.val.val
        apply Prod.ext
        · rfl
        · exact (congrArg Subtype.val u.property).symm
      map_add' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        change (a.val + b.val, (0 : B)) = (a.val + b.val, (0 : B) + 0)
        simp
      map_smul' := fun c a => by
        apply Subtype.ext
        apply Subtype.ext
        change (c • a.val, (0 : B)) = (c • a.val, c • (0 : B))
        simp }
  have h := (projection U).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (projection_surjective U),
    finrank_top, ← e.finrank_eq] at h
  omega

/-- Every submodule determines one quotient-valued linear lift on its full
projection, and the displayed relation reconstructs every one of its vectors. -/
theorem exists_unique_lift (U : Submodule 𝕜 (A × B)) :
    ∃! f : secondRange U →ₗ[𝕜] A ⧸ firstKernel U,
      ∀ (a : A) (s : secondRange U),
        (a,s.val) ∈ U ↔ (firstKernel U).mkQ a = f s := by
  classical
  obtain ⟨j,hj⟩ := (projection U).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (projection_surjective U))
  let f := (firstKernel U).mkQ.comp
    ((LinearMap.fst 𝕜 A B).comp (U.subtype.comp j))
  have js (s : secondRange U) : (j s).val.2 = s.val :=
    congrArg Subtype.val (LinearMap.congr_fun hj s)
  have spec (a : A) (s : secondRange U) :
      (a,s.val) ∈ U ↔ (firstKernel U).mkQ a = f s := by
    have diff : (a,s.val) - (j s).val = (a-(j s).val.1,0) := by
      ext <;> simp [js s]
    change (a,s.val) ∈ U ↔
      (firstKernel U).mkQ a = (firstKernel U).mkQ (j s).val.1
    change (a,s.val) ∈ U ↔
      Submodule.Quotient.mk a = Submodule.Quotient.mk (j s).val.1
    rw [Submodule.Quotient.eq]
    change (a,s.val) ∈ U ↔ (a-(j s).val.1,0) ∈ U
    rw [← diff]
    exact (U.sub_mem_iff_left (j s).property).symm
  refine ⟨f,spec,?_⟩
  intro g hg
  ext s
  have hmem : ((j s).val.1,s.val) ∈ U := by
    simpa only [← js s,Prod.eta] using (j s).property
  exact ((hg _ s).mp hmem).symm.trans ((spec _ s).mp hmem)

/-- The actual subspace reconstructed from arbitrary full lift data. -/
def liftSpace (K : Submodule 𝕜 A) (P : Submodule 𝕜 B)
    (f : P →ₗ[𝕜] A ⧸ K) : Submodule 𝕜 (A × B) where
  carrier := {v | ∃ h : v.2 ∈ P, K.mkQ v.1 = f ⟨v.2,h⟩}
  zero_mem' := ⟨P.zero_mem,by change K.mkQ 0 = f 0; simp⟩
  add_mem' := by
    rintro x y ⟨hx,he⟩ ⟨hy,hf⟩
    refine ⟨P.add_mem hx hy,?_⟩
    change K.mkQ (x.1+y.1) = f (⟨x.2,hx⟩+⟨y.2,hy⟩)
    simp only [map_add,he,hf]
  smul_mem' := by
    rintro c x ⟨hx,he⟩
    refine ⟨P.smul_mem c hx,?_⟩
    change K.mkQ (c • x.1) = f (c • (⟨x.2,hx⟩ : P))
    simp only [map_smul,he]

/-- Reconstruction realizes exactly K, not merely a contained kernel. -/
theorem firstKernel_liftSpace (K : Submodule 𝕜 A) (P : Submodule 𝕜 B)
    (f : P →ₗ[𝕜] A ⧸ K) : firstKernel (liftSpace K P f) = K := by
  ext a
  change (∃ h : (0 : B) ∈ P, K.mkQ a = f ⟨0,h⟩) ↔ a ∈ K
  have he : ∀ h : (0 : B) ∈ P, f ⟨0,h⟩ = 0 := by
    intro h
    change f 0 = 0
    exact map_zero f
  simp only [he,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨P.zero_mem,h⟩⟩

/-- Every projection vector lifts, including when K or P is zero. -/
theorem secondRange_liftSpace (K : Submodule 𝕜 A) (P : Submodule 𝕜 B)
    (f : P →ₗ[𝕜] A ⧸ K) : secondRange (liftSpace K P f) = P := by
  ext s
  constructor
  · rintro ⟨v,⟨hv,he⟩,rfl⟩
    exact hv
  · intro hs
    obtain ⟨a,ha⟩ := K.mkQ_surjective (f ⟨s,hs⟩)
    exact ⟨(a,s),⟨hs,ha⟩,rfl⟩

/-- Lift data always recover the original entire submodule. -/
theorem reconstruction (U : Submodule 𝕜 (A × B)) :
    ∃! f : secondRange U →ₗ[𝕜] A ⧸ firstKernel U,
      liftSpace (firstKernel U) (secondRange U) f = U := by
  obtain ⟨f,hf,hu⟩ := exists_unique_lift U
  refine ⟨f,?_,?_⟩
  · ext v
    change (∃ hs : v.2 ∈ secondRange U,
      (firstKernel U).mkQ v.1 = f ⟨v.2,hs⟩) ↔ v ∈ U
    constructor
    · rintro ⟨hs,he⟩
      exact (hf v.1 ⟨v.2,hs⟩).mpr he
    · intro hv
      exact ⟨⟨v,hv,rfl⟩,(hf v.1 ⟨v.2,⟨v,hv,rfl⟩⟩).mp hv⟩
  · intro g hg
    apply hu g
    intro a s
    have hm : ((a,s.val) ∈ liftSpace (firstKernel U) (secondRange U) g) ↔
        (firstKernel U).mkQ a = g s :=
      ⟨fun ⟨_,he⟩ => he,fun he => ⟨s.property,he⟩⟩
    have hh := congrArg (fun V : Submodule 𝕜 (A × B) => (a,s.val) ∈ V) hg
    exact (Iff.of_eq hh).symm.trans hm

/-- Distinct complete placement maps give distinct actual submodules. -/
theorem liftSpace_injective (K : Submodule 𝕜 A) (P : Submodule 𝕜 B) :
    Function.Injective (liftSpace K P) := by
  intro f g h
  ext s
  obtain ⟨a,ha⟩ := K.mkQ_surjective (f s)
  have hm : (a,s.val) ∈ liftSpace K P f := ⟨s.property,ha⟩
  rw [h] at hm
  obtain ⟨_,hg⟩ := hm
  exact ha.symm.trans hg

/-- The entire fiber at a fixed kernel/projection is parametrized by all
linear maps. No subspace, including the zero one, is omitted. -/
def liftEquiv (K : Submodule 𝕜 A) (P : Submodule 𝕜 B) :
    (P →ₗ[𝕜] A ⧸ K) ≃
      {U : Submodule 𝕜 (A × B) // firstKernel U = K ∧ secondRange U = P} :=
  Equiv.ofBijective
    (fun f => ⟨liftSpace K P f,firstKernel_liftSpace K P f,secondRange_liftSpace K P f⟩)
    ⟨fun f g h => liftSpace_injective K P (congrArg Subtype.val h),by
      rintro ⟨U,hK,hP⟩
      have h := reconstruction U
      rw [hK,hP] at h
      obtain ⟨f,hf,_⟩ := h
      exact ⟨f,Subtype.ext hf⟩⟩

/-- The intersection with the complementary summand is the actual kernel
of the placement map, transported along its domain subtype. -/
theorem secondKernel_liftSpace (K : Submodule 𝕜 A) (P : Submodule 𝕜 B)
    (f : P →ₗ[𝕜] A ⧸ K) :
    (liftSpace K P f).comap (LinearMap.inr 𝕜 A B) =
      (LinearMap.ker f).map P.subtype := by
  ext s
  constructor
  · rintro ⟨hs,he⟩
    refine ⟨⟨s,hs⟩,?_,rfl⟩
    exact he.symm
  · rintro ⟨s,hs,rfl⟩
    exact ⟨s.property,hs.symm⟩

/-- Full bilinear orthogonality in lift coordinates. The first summand is
totally isotropic; the second summand need not be isotropic. Representatives
are arbitrary full linear lifts of the quotient maps. -/
theorem orthogonal_iff
    (β : (A × B) →ₗ[𝕜] (A × B) →ₗ[𝕜] 𝕜)
    (hA : ∀ a a' : A, β (a,0) (a',0) = 0)
    (K L : Submodule 𝕜 A) (P Q : Submodule 𝕜 B)
    (f : P →ₗ[𝕜] A ⧸ K) (g : Q →ₗ[𝕜] A ⧸ L)
    (F : P →ₗ[𝕜] A) (G : Q →ₗ[𝕜] A)
    (hF : K.mkQ.comp F = f) (hG : L.mkQ.comp G = g) :
    (∀ u ∈ liftSpace K P f, ∀ w ∈ liftSpace L Q g, β u w = 0) ↔
      (∀ k ∈ K, ∀ q : Q, β (k,0) (0,q.val) = 0) ∧
      (∀ p : P, ∀ l ∈ L, β (0,p.val) (l,0) = 0) ∧
      (∀ (p : P) (q : Q),
        β (0,p.val) (0,q.val) + β (F p,0) (0,q.val) +
          β (0,p.val) (G q,0) = 0) := by
  have hFm (p : P) : (F p,p.val) ∈ liftSpace K P f :=
    ⟨p.property,LinearMap.congr_fun hF p⟩
  have hGm (q : Q) : (G q,q.val) ∈ liftSpace L Q g :=
    ⟨q.property,LinearMap.congr_fun hG q⟩
  have hKm (k : A) (hk : k ∈ K) : (k,0) ∈ liftSpace K P f := by
    refine ⟨P.zero_mem,?_⟩
    change K.mkQ k = f 0
    simpa only [map_zero,Submodule.mkQ_apply] using (Submodule.Quotient.mk_eq_zero K).mpr hk
  have hLm (l : A) (hl : l ∈ L) : (l,0) ∈ liftSpace L Q g := by
    refine ⟨Q.zero_mem,?_⟩
    change L.mkQ l = g 0
    simpa only [map_zero,Submodule.mkQ_apply] using (Submodule.Quotient.mk_eq_zero L).mpr hl
  have expand (a a' : A) (b b' : B) :
      β (a,b) (a',b') = β (0,b) (0,b') +
        β (a,0) (0,b') + β (0,b) (a',0) := by
    have e (a : A) (b : B) : (a,b) = (a,0) + (0,b) := by simp
    conv_lhs => rw [e a b,e a' b']
    simp only [map_add,LinearMap.add_apply,hA]
    ring
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro k hk q
      have hh := h (k,0) (hKm k hk) (G q,q.val) (hGm q)
      rw [expand] at hh
      simpa only [show ((0 : A),(0 : B)) = (0 : A×B) from rfl,
        map_zero,LinearMap.zero_apply,zero_add,add_zero,hA] using hh
    · intro p l hl
      have hh := h (F p,p.val) (hFm p) (l,0) (hLm l hl)
      rw [expand] at hh
      simpa only [show ((0 : A),(0 : B)) = (0 : A×B) from rfl,
        map_zero,LinearMap.zero_apply,zero_add,add_zero,hA] using hh
    · intro p q
      have hh := h (F p,p.val) (hFm p) (G q,q.val) (hGm q)
      rw [expand] at hh
      exact hh
  · rintro ⟨hK,hL,hfg⟩ u ⟨hu,heu⟩ w ⟨hw,hew⟩
    let p : P := ⟨u.2,hu⟩
    let q : Q := ⟨w.2,hw⟩
    have hk : u.1 - F p ∈ K := by
      apply (Submodule.Quotient.eq K).mp
      exact heu.trans (LinearMap.congr_fun hF p).symm
    have hl : w.1 - G q ∈ L := by
      apply (Submodule.Quotient.eq L).mp
      exact hew.trans (LinearMap.congr_fun hG q).symm
    have eu : u = (u.1 - F p,0) + (F p,p.val) := by ext <;> simp [p]
    have ew : w = (w.1 - G q,0) + (G q,q.val) := by ext <;> simp [q]
    have hkq : β (u.1 - F p,0) (G q,q.val) = 0 := by
      rw [expand]
      simpa only [show ((0 : A),(0 : B)) = (0 : A×B) from rfl,
        map_zero,LinearMap.zero_apply,zero_add,add_zero] using hK _ hk q
    have hpl : β (F p,p.val) (w.1 - G q,0) = 0 := by
      rw [expand]
      simpa only [show ((0 : A),(0 : B)) = (0 : A×B) from rfl,
        map_zero,LinearMap.zero_apply,zero_add,add_zero] using hL p _ hl
    have hpq : β (F p,p.val) (G q,q.val) = 0 := by
      rw [expand]
      exact hfg p q
    rw [eu,ew]
    simp only [map_add,LinearMap.add_apply,hA,hkq,hpl,hpq,zero_add]

/-- The exact number of actual submodules with prescribed full kernel and
projection. Over F2 with dim A=3 this is 2^(dim P*(3-dim K)),
including all zero/full fibers. -/
theorem fiber_card [Finite 𝕜] [Module.Finite 𝕜 A] [Module.Finite 𝕜 B]
    (K : Submodule 𝕜 A) (P : Submodule 𝕜 B) :
    Nat.card {U : Submodule 𝕜 (A × B) // firstKernel U = K ∧ secondRange U = P} =
      Nat.card 𝕜 ^ (Module.finrank 𝕜 P * (Module.finrank 𝕜 A - Module.finrank 𝕜 K)) := by
  rw [← Nat.card_congr (liftEquiv K P)]
  rw [Module.natCard_eq_pow_finrank (K := 𝕜)]
  congr 1
  rw [Module.finrank_linearMap]
  have hd : Module.finrank 𝕜 (A ⧸ K) =
      Module.finrank 𝕜 A - Module.finrank 𝕜 K := by
    have h := K.finrank_quotient_add_finrank
    omega
  rw [hd]

#print axioms fiber_card
#print axioms exists_unique_lift
#print axioms reconstruction
end D5.S3.Combinatorics.Orthogonality.SplitSubmoduleLift
