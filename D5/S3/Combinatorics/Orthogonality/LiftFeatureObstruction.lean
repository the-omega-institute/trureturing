/- GID: D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/LiftFeatureObstruction
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.claim; result=D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.result; claim=D5/S3/Combinatorics/Orthogonality/LiftFeatureObstruction.claim
   digest: The original adjacent planes have identical full kernel/projection and lift rank/image/kernel. -/

import D5.S3.Combinatorics.Orthogonality.SixDimensionalProfiles
import D5.S3.Combinatorics.Orthogonality.OrthogonalitySymmetryObstruction

/-! The received planes are the original spans (13,6) and (9,14).
The maps have their full original domains and quotient codomains. This
refutes the proposed coloring rule on every actual graph vertex; no
structural fifteen-color construction or paused n7 exclusion is asserted. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Orthogonality.LiftFeatureObstruction
open Matrix SixDimensionalLiftGeometry SplitSubmoduleLift
open scoped CharTwo

/-- The whole original two-dimensional projection plane. -/
def J : Submodule F A := LinearMap.ker (LinearMap.proj (2 : Fin 3))

private theorem J_mem (p : A) : p ∈ J ↔ p 2 = 0 := Iff.rfl

private def uEquiv : J ≃ₗ[F] J where
  toFun p := ⟨![p.val 1,p.val 0+p.val 1,0],rfl⟩
  invFun p := ⟨![p.val 0+p.val 1,p.val 0,0],rfl⟩
  left_inv p := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [(J_mem _).mp p.property,add_assoc,add_comm,add_left_comm]
  right_inv p := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [(J_mem _).mp p.property,add_assoc,add_comm,add_left_comm]
  map_add' p q := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c p := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [mul_add]

/-- The full T-coordinate lift of the first original plane. -/
def fu : J →ₗ[F] A := J.subtype.comp uEquiv.toLinearMap
/-- The full T-coordinate lift of the second original plane. -/
def fw : J →ₗ[F] A := J.subtype.comp uEquiv.symm.toLinearMap
/-- The actual quotient-valued placement map. -/
def f : J →ₗ[F] A ⧸ (⊥ : Submodule F A) := (⊥ : Submodule F A).mkQ.comp fu
/-- The second actual quotient-valued placement map. -/
def g : J →ₗ[F] A ⧸ (⊥ : Submodule F A) := (⊥ : Submodule F A).mkQ.comp fw

private theorem q_injective : Function.Injective (⊥ : Submodule F A).mkQ := by
  intro x y h
  exact sub_eq_zero.mp ((Submodule.Quotient.eq ⊥).mp h)

private theorem f_injective : Function.Injective f := by
  intro p q h
  have h' : fu p = fu q := q_injective h
  exact uEquiv.injective (Subtype.ext h')

private theorem g_injective : Function.Injective g := by
  intro p q h
  have h' : fw p = fw q := q_injective h
  exact uEquiv.symm.injective (Subtype.ext h')

/-- Both entire quotient maps have zero kernel. -/
theorem kernels : LinearMap.ker f = ⊥ ∧ LinearMap.ker g = ⊥ :=
  ⟨LinearMap.ker_eq_bot.mpr f_injective,LinearMap.ker_eq_bot.mpr g_injective⟩

/-- Both entire quotient maps have the same complete image. -/
theorem ranges : LinearMap.range f = J.map (⊥ : Submodule F A).mkQ ∧
    LinearMap.range g = J.map (⊥ : Submodule F A).mkQ := by
  constructor
  · rw [f,LinearMap.range_comp,fu,LinearMap.range_comp,
      LinearEquiv.range,Submodule.map_top,Submodule.range_subtype]
  · rw [g,LinearMap.range_comp,fw,LinearMap.range_comp,
      LinearEquiv.range,Submodule.map_top,Submodule.range_subtype]

private def JEquiv : (Fin 2 → F) ≃ₗ[F] J where
  toFun p := ⟨![p 0,p 1,0],rfl⟩
  invFun p := ![p.val 0,p.val 1]
  left_inv p := by ext i; fin_cases i <;> rfl
  right_inv p := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [(J_mem _).mp p.property]
  map_add' p q := by apply Subtype.ext; ext i; fin_cases i <;> rfl
  map_smul' c p := by apply Subtype.ext; ext i; fin_cases i <;> rfl

/-- The full lift maps have the original rank two. -/
theorem ranks : Module.finrank F (LinearMap.range f) = 2 ∧
    Module.finrank F (LinearMap.range g) = 2 := by
  have hJ : Module.finrank F J = 2 := by
    rw [← JEquiv.finrank_eq]
    simp [F]
  exact ⟨(LinearEquiv.ofInjective f f_injective).finrank_eq.symm.trans hJ,
    (LinearEquiv.ofInjective g g_injective).finrank_eq.symm.trans hJ⟩

/-- The entire first received plane. -/
def U : Submodule F V := represented ⊥ J f
/-- The entire second received plane. -/
def W : Submodule F V := represented ⊥ J g

private def liftMap (h : J →ₗ[F] A) : J →ₗ[F] V :=
  coordinates.toLinearMap.comp (h.prod J.subtype)

private theorem represented_range (h : J →ₗ[F] A) :
    represented ⊥ J ((⊥ : Submodule F A).mkQ.comp h) = (liftMap h).range := by
  ext v
  constructor
  · rintro ⟨⟨t,p⟩,⟨hp,he⟩,rfl⟩
    have ht : t = h ⟨p,hp⟩ := q_injective he
    exact ⟨⟨p,hp⟩,by change coordinates (h ⟨p,hp⟩,p) = coordinates (t,p); rw [ht]⟩
  · rintro ⟨p,rfl⟩
    exact ⟨(h p,p.val),⟨p.property,rfl⟩,rfl⟩

private def basisChange : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) where
  toFun p := ![p 0+p 1,p 1]
  invFun p := ![p 0+p 1,p 1]
  left_inv p := by ext i; fin_cases i <;> simp [add_assoc]
  right_inv p := by ext i; fin_cases i <;> simp [add_assoc]
  map_add' p q := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c p := by ext i; fin_cases i <;> simp [mul_add]

private theorem range_basis (h : (Fin 2 → F) →ₗ[F] V) :
    h.range = Submodule.span F {h ![1,0],h ![0,1]} := by
  have he := (Pi.basisFun F (Fin 2)).span_eq
  rw [← Submodule.map_top,← he,Submodule.map_span]
  congr 1
  ext v
  simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and,Set.mem_insert_iff,
    Set.mem_singleton_iff]
  have hb : ∀ i : Fin 2, Pi.basisFun F (Fin 2) i = ![![1,0],![0,1]] i := by
    intro i
    ext j
    fin_cases i <;> fin_cases j <;> simp [Pi.basisFun_apply]
  simp_rw [hb]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩

/-- Exact equality to the original binary-coordinate spans. -/
theorem source_planes :
    U = Submodule.span F {SixBitSubmoduleBridge.bits 13,SixBitSubmoduleBridge.bits 6} ∧
    W = Submodule.span F {SixBitSubmoduleBridge.bits 9,SixBitSubmoduleBridge.bits 14} := by
  have hr (h : J →ₗ[F] A) : (liftMap h).range =
      (((liftMap h).comp JEquiv.toLinearMap).comp basisChange.toLinearMap).range := by
    rw [LinearMap.range_comp,LinearEquiv.range,Submodule.map_top,
      LinearMap.range_comp,LinearEquiv.range,Submodule.map_top]
  constructor
  · rw [U,f,represented_range,hr,range_basis]
    congr 1
    have h1 : ((liftMap fu).comp JEquiv.toLinearMap).comp basisChange.toLinearMap ![1,0] = SixBitSubmoduleBridge.bits 13 := by
      ext i
      fin_cases i <;> norm_num [liftMap,fu,uEquiv,JEquiv,basisChange,coordinates,SixBitSubmoduleBridge.bits]
    have h2 : ((liftMap fu).comp JEquiv.toLinearMap).comp basisChange.toLinearMap ![0,1] = SixBitSubmoduleBridge.bits 6 := by
      ext i
      fin_cases i <;> norm_num [liftMap,fu,uEquiv,JEquiv,basisChange,coordinates,SixBitSubmoduleBridge.bits]
    rw [h1,h2]
  · rw [W,g,represented_range,hr,range_basis]
    congr 1
    have h1 : ((liftMap fw).comp JEquiv.toLinearMap).comp basisChange.toLinearMap ![1,0] = SixBitSubmoduleBridge.bits 14 := by
      ext i
      fin_cases i <;> norm_num [liftMap,fw,uEquiv,JEquiv,basisChange,coordinates,SixBitSubmoduleBridge.bits]
    have h2 : ((liftMap fw).comp JEquiv.toLinearMap).comp basisChange.toLinearMap ![0,1] = SixBitSubmoduleBridge.bits 9 := by
      ext i
      fin_cases i <;> norm_num [liftMap,fw,uEquiv,JEquiv,basisChange,coordinates,SixBitSubmoduleBridge.bits]
    rw [h1,h2,Set.pair_comm]

private theorem U_ne_bot : U ≠ ⊥ := by
  intro h
  have hp := (SixDimensionalProfiles.represented_profile ⊥ J f).2
  have hz : P (⊥ : Submodule F V) = ⊥ := by
    apply (projection_eq_bot_iff _).mpr bot_le
  have hJ : J = ⊥ := hp.symm.trans ((congrArg P h).trans hz)
  have hm : (![1,0,0] : A) ∈ J := rfl
  rw [hJ] at hm
  have he := congrFun (show (![1,0,0] : A) = 0 from hm) 0
  norm_num at he

private theorem W_ne_bot : W ≠ ⊥ := by
  intro h
  have hp := (SixDimensionalProfiles.represented_profile ⊥ J g).2
  have hz : P (⊥ : Submodule F V) = ⊥ := (projection_eq_bot_iff _).mpr bot_le
  have hJ : J = ⊥ := hp.symm.trans ((congrArg P h).trans hz)
  have hm : (![1,0,0] : A) ∈ J := rfl
  rw [hJ] at hm
  have he := congrFun (show (![1,0,0] : A) = 0 from hm) 0
  norm_num at he

private def uVertex : NikandishClique.Vertex 6 := ⟨U,U_ne_bot⟩
private def wVertex : NikandishClique.Vertex 6 := ⟨W,W_ne_bot⟩

private theorem planes_distinct : uVertex ≠ wVertex := by
  intro h
  have hu : f = g := by
    apply SplitSubmoduleLift.liftSpace_injective ⊥ J
    apply Submodule.map_injective_of_injective coordinates.injective
    exact congrArg Subtype.val h
  have he := congrArg (fun h : J →ₗ[F] A ⧸ (⊥ : Submodule F A) =>
    (Submodule.quotEquivOfEqBot (⊥ : Submodule F A) rfl) (h ⟨![1,0,0],rfl⟩)) hu
  change fu ⟨![1,0,0],rfl⟩ = fw ⟨![1,0,0],rfl⟩ at he
  have hh := congrFun he 0
  norm_num [fu,fw,uEquiv] at hh

private theorem planes_orthogonal : ∀ u ∈ U, ∀ w ∈ W, dotProduct u w = 0 := by
  apply (SixDimensionalLiftGeometry.orthogonal_iff ⊥ ⊥ J J f g fu fw rfl rfl).mpr
  refine ⟨?_,?_,?_⟩
  · intro k hk q
    have hk' : k = 0 := hk
    simp [hk']
  · intro p l hl
    have hl' : l = 0 := hl
    simp [hl']
  · intro p q
    simp [dotProduct,Fin.sum_univ_succ,fu,fw,uEquiv,
      (J_mem _).mp p.property,(J_mem _).mp q.property]
    ring_nf
    simp only [show (2 : F) = 0 by decide,mul_zero,zero_add,add_zero]

/-- The actual original planes are distinct adjacent graph vertices. -/
theorem planes_adjacent : (NikandishClique.orthogonalityGraph 6).Adj uVertex wVertex :=
  ⟨planes_distinct,planes_orthogonal⟩

private def shear : V ≃ₗ[F] V :=
  LinearEquiv.funCongrLeft F F
    ((Equiv.swap (0 : Fin 6) 1).trans (Equiv.swap (2 : Fin 6) 3))

private theorem shear_dot (u v : V) :
    dotProduct (shear u) (shear v) = dotProduct u v := by
  simp [shear,LinearEquiv.funCongrLeft_apply,LinearMap.funLeft,
    dotProduct,Fin.sum_univ_succ,Equiv.swap_apply_def]
  ring

private theorem shear_fixes_T (v : V) (hv : v ∈ T) : shear v = v := by
  obtain ⟨a,rfl⟩ := hv
  change shear (coordinates (a,0)) = coordinates (a,0)
  ext i
  fin_cases i <;> simp [shear,LinearEquiv.funCongrLeft_apply,LinearMap.funLeft,
    SixDimensionalLiftGeometry.coordinates,Equiv.swap_apply_def]

/-- The actual received shear, in the entire orthogonal stabilizer.
In T/S coordinates it is (t,s) ↦ (t+diag(1,1,0)s,s). -/
def shearElement : OrthogonalitySymmetryObstruction.stabilizer :=
  ⟨shear,shear_dot,by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      change shear w ∈ T
      rw [shear_fixes_T w hw]
      exact hw
    · intro v hv
      exact ⟨v,hv,shear_fixes_T v hv⟩⟩

/-- The exact source plane orbit, under the actual full stabilizer action. -/
theorem plane_orbit : OrthogonalitySymmetryObstruction.act shearElement uVertex =
    wVertex := by
  apply Subtype.ext
  change U.map shear.toLinearMap = W
  rw [source_planes.1,source_planes.2,Submodule.map_span]
  have h13 : shear (SixBitSubmoduleBridge.bits 13) = SixBitSubmoduleBridge.bits 14 := by
    ext i
    fin_cases i <;> norm_num [shear,LinearEquiv.funCongrLeft_apply,LinearMap.funLeft,
      SixBitSubmoduleBridge.bits,Equiv.swap_apply_def]
  have h6 : shear (SixBitSubmoduleBridge.bits 6) = SixBitSubmoduleBridge.bits 9 := by
    ext i
    fin_cases i <;> norm_num [shear,LinearEquiv.funCongrLeft_apply,LinearMap.funLeft,
      SixBitSubmoduleBridge.bits,Equiv.swap_apply_def]
  rw [Set.image_insert_eq,Set.image_singleton]
  change Submodule.span F {shear (SixBitSubmoduleBridge.bits 13),
    shear (SixBitSubmoduleBridge.bits 6)} = _
  rw [h13,h6]
  exact congrArg (Submodule.span F) (Set.pair_comm _ _)

/-- The original shear fixes every actual clique label. -/
theorem shear_labels (W' : OrthogonalitySymmetryObstruction.CliqueLabel) :
    OrthogonalitySymmetryObstruction.labelAct shearElement W' = W' := by
  apply Subtype.ext
  apply Subtype.ext
  change W'.val.val.map shear.toLinearMap = W'.val.val
  apply le_antisymm
  · rintro v ⟨u,hu,rfl⟩
    change shear u ∈ W'.val.val
    rw [shear_fixes_T u (W'.property hu)]
    exact hu
  · intro v hv
    exact ⟨v,hv,shear_fixes_T v (W'.property hv)⟩

/-- The proposed rule on the full original graph domain. Every full K/P
fiber and both full quotient maps are quantified, including all degenerate
fibers giving nonzero vertices. Rank/image/kernel are actual linear-map data. -/
def featureClaim : Prop := ∃ (α : Type) (c : NikandishClique.Vertex 6 → α),
  (∀ U' W', (NikandishClique.orthogonalityGraph 6).Adj U' W' → c U' ≠ c W') ∧
  ∀ (K' P' : Submodule F A) (f' g' : P' →ₗ[F] A ⧸ K')
    (hf : represented K' P' f' ≠ ⊥) (hg : represented K' P' g' ≠ ⊥),
    Module.finrank F (LinearMap.range f') = Module.finrank F (LinearMap.range g') →
    LinearMap.range f' = LinearMap.range g' → LinearMap.ker f' = LinearMap.ker g' →
    c ⟨represented K' P' f',hf⟩ = c ⟨represented K' P' g',hg⟩

/-- The full feature rule or either original entire-stabilizer coloring rule. -/
def claim : Prop := featureClaim ∨ OrthogonalitySymmetryObstruction.symmetryClaim

/-- The original adjacent plane pair refutes the full feature rule and,
through its actual label-fixing shear orbit, both entire-group rules. -/
theorem result : ¬ claim := by
  rintro (⟨α,c,hc,he⟩ | ⟨c,hc,he⟩ | ⟨α,c,hc,he⟩)
  · exact hc _ _ planes_adjacent (he ⊥ J f g U_ne_bot W_ne_bot
      (ranks.1.trans ranks.2.symm) (ranges.1.trans ranges.2.symm)
      (kernels.1.trans kernels.2.symm))
  · have h := he shearElement uVertex
    rw [plane_orbit,shear_labels] at h
    exact hc _ _ planes_adjacent h.symm
  · have h := he shearElement uVertex
    rw [plane_orbit] at h
    exact hc _ _ planes_adjacent h.symm

#print axioms result
end D5.S3.Combinatorics.Orthogonality.LiftFeatureObstruction
