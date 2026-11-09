/- GID: D5/S3/Combinatorics/Orthogonality/OrthogonalitySymmetryObstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/OrthogonalitySymmetryObstruction
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Orthogonality/OrthogonalitySymmetryObstruction.claim; result=D5/S3/Combinatorics/Orthogonality/OrthogonalitySymmetryObstruction.result; claim=D5/S3/Combinatorics/Orthogonality/OrthogonalitySymmetryObstruction.claim
   digest: The actual full orthogonal stabilizer has adjacent vertices in a label-fixing orbit. -/

import D5.S3.Combinatorics.Orthogonality.SixDimensionalLiftGeometry
import Mathlib.Algebra.Module.Equiv.Basic
import D5.S3.QuadraticForms.RadicalQuotientIsometry

/-! The received coordinate swap is an element of the entire orthogonal
stabilizer of the specified T. The label domain consists of every nonzero
actual submodule of T. This excludes full-stabilizer equivariance and
invariance; it makes no assertion excluding symmetry breaking by auxiliary
choices or by restricting to a proper subgroup. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Orthogonality.OrthogonalitySymmetryObstruction

open Matrix
open SixDimensionalLiftGeometry
open scoped CharTwo

abbrev Vertex := NikandishClique.Vertex 6

/-- The full orthogonal stabilizer of the original T, as an actual subgroup. -/
def stabilizer : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | (∀ u v, dotProduct (g u) (g v) = dotProduct u v) ∧
    T.map g.toLinearMap = T}
  one_mem' := ⟨fun _ _ => rfl,by simp⟩
  mul_mem' := by
    rintro g h ⟨hg,hT⟩ ⟨hh,hT'⟩
    refine ⟨fun u v => (hg (h u) (h v)).trans (hh u v),?_⟩
    change T.map (g.toLinearMap.comp h.toLinearMap) = T
    rw [Submodule.map_comp,hT',hT]
  inv_mem' := by
    rintro g ⟨hg,hT⟩
    refine ⟨?_,?_⟩
    · intro u v
      have h := hg (g.symm u) (g.symm v)
      change dotProduct (g.symm u) (g.symm v) = dotProduct u v
      simpa only [LinearEquiv.apply_symm_apply] using h.symm
    · apply le_antisymm
      · rintro v ⟨u,hu,rfl⟩
        change g.symm u ∈ T
        have hm : u ∈ T.map g.toLinearMap := hT.symm ▸ hu
        obtain ⟨w,hw,he⟩ := hm
        change g w = u at he
        rw [← he,LinearEquiv.symm_apply_apply]
        exact hw
      · intro v hv
        have hgv : g v ∈ T := hT ▸ (show g v ∈ T.map g.toLinearMap from ⟨v,hv,rfl⟩)
        exact ⟨g v,hgv,by change g.symm (g v) = v; simp⟩

/-- The actual action on all nonzero coordinate submodules. -/
def act (g : stabilizer) (U : Vertex) : Vertex :=
  ⟨U.val.map g.val.toLinearMap,by
    intro h
    apply U.property
    exact (Submodule.map_eq_bot_iff (e := g.val)).mp h⟩

/-- All original fixed-clique labels, with their actual inclusion data. -/
abbrev CliqueLabel := {W : Vertex // W.val ≤ T}

/-- The induced action on the entire original label domain. -/
def labelAct (g : stabilizer) (W : CliqueLabel) : CliqueLabel :=
  ⟨act g W.val,by
    change W.val.val.map g.val.toLinearMap ≤ T
    exact (Submodule.map_mono W.property).trans_eq g.property.2⟩

private def swap : V ≃ₗ[F] V :=
  LinearEquiv.funCongrLeft F F (Equiv.swap (0 : Fin 6) 1)

private theorem swap_dot (u v : V) :
    dotProduct (swap u) (swap v) = dotProduct u v := by
  simp [swap,LinearEquiv.funCongrLeft_apply,LinearMap.funLeft,
    dotProduct,Fin.sum_univ_succ,Equiv.swap_apply_def]
  ring

private theorem swap_fixes_T (v : V) (hv : v ∈ T) : swap v = v := by
  obtain ⟨a,rfl⟩ := hv
  change swap (coordinates (a,0)) = coordinates (a,0)
  ext i
  fin_cases i <;> simp [swap,LinearEquiv.funCongrLeft_apply,LinearMap.funLeft,
    SixDimensionalLiftGeometry.coordinates,Equiv.swap_apply_def]

/-- The received swap, in the entire original stabilizer. -/
def swapElement : stabilizer := ⟨swap,swap_dot,by
  apply le_antisymm
  · rintro v ⟨w,hw,rfl⟩
    change swap w ∈ T
    rw [swap_fixes_T w hw]
    exact hw
  · intro v hv
    exact ⟨v,hv,swap_fixes_T v hv⟩⟩

private def firstLine : Submodule F V := Submodule.span F {SixBitSubmoduleBridge.bits 1}
private def secondLine : Submodule F V := Submodule.span F {SixBitSubmoduleBridge.bits 2}

private theorem firstLine_ne_bot : firstLine ≠ ⊥ := by
  intro h
  have hm : SixBitSubmoduleBridge.bits 1 ∈ firstLine := Submodule.subset_span (by simp)
  rw [h] at hm
  have hz : SixBitSubmoduleBridge.bits 1 = 0 := hm
  have := congrFun hz 0
  norm_num [SixBitSubmoduleBridge.bits] at this

private theorem secondLine_ne_bot : secondLine ≠ ⊥ := by
  intro h
  have hm : SixBitSubmoduleBridge.bits 2 ∈ secondLine := Submodule.subset_span (by simp)
  rw [h] at hm
  have hz : SixBitSubmoduleBridge.bits 2 = 0 := hm
  have := congrFun hz 1
  norm_num [SixBitSubmoduleBridge.bits] at this

private def firstVertex : Vertex := ⟨firstLine,firstLine_ne_bot⟩
private def secondVertex : Vertex := ⟨secondLine,secondLine_ne_bot⟩

private theorem lines_distinct : firstVertex ≠ secondVertex := by
  intro he
  have he' : firstLine = secondLine := congrArg Subtype.val he
  have h : SixBitSubmoduleBridge.bits 1 ∈ secondLine := by
    rw [← he']
    exact Submodule.subset_span (by simp)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
  have hh := congrFun hc 0
  norm_num [SixBitSubmoduleBridge.bits] at hh

private theorem lines_adjacent : (NikandishClique.orthogonalityGraph 6).Adj
    firstVertex secondVertex := by
  refine ⟨lines_distinct,?_⟩
  intro u hu v hv
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hv
  change dotProduct (a • SixBitSubmoduleBridge.bits 1)
    (b • SixBitSubmoduleBridge.bits 2) = 0
  rw [smul_dotProduct,dotProduct_smul]
  have hz : dotProduct (SixBitSubmoduleBridge.bits 1)
      (SixBitSubmoduleBridge.bits 2) = 0 := by
    exact (SixBitSubmoduleBridge.bits_dot 1 2).mpr (by decide +kernel)
  rw [hz]
  simp

private theorem swap_first : act swapElement firstVertex = secondVertex := by
  apply Subtype.ext
  change firstLine.map swap.toLinearMap = secondLine
  rw [firstLine,secondLine,Submodule.map_span]
  congr 1
  rw [Set.image_singleton]
  congr 1
  ext i
  fin_cases i <;> norm_num [swap,LinearEquiv.funCongrLeft_apply,LinearMap.funLeft,
    SixBitSubmoduleBridge.bits,Equiv.swap_apply_def]

private theorem swap_labels (W : CliqueLabel) : labelAct swapElement W = W := by
  apply Subtype.ext
  apply Subtype.ext
  change W.val.val.map swap.toLinearMap = W.val.val
  apply le_antisymm
  · rintro v ⟨u,hu,rfl⟩
    change swap u ∈ W.val.val
    rw [swap_fixes_T u (W.property hu)]
    exact hu
  · intro v hv
    exact ⟨v,hv,swap_fixes_T v (W.property hv)⟩

private theorem H_mem (U : Submodule F V) (a : A) :
    a ∈ H U ↔ ∀ u ∈ U, dotProduct u (coordinates (a,0)) = 0 := by
  have hh := congrArg (fun W : Submodule F V => coordinates (a,0) ∈ W) (H_source U)
  change (∃ b ∈ H U, coordinates (b,0) = coordinates (a,0)) =
    ((∀ u ∈ U, dotProduct u (coordinates (a,0)) = 0) ∧ coordinates (a,0) ∈ T) at hh
  have he : (∃ b ∈ H U, coordinates (b,0) = coordinates (a,0)) ↔ a ∈ H U := by
    constructor
    · rintro ⟨b,hb,hba⟩
      have h : b = a := congrArg Prod.fst (coordinates.injective hba)
      exact h ▸ hb
    · intro ha
      exact ⟨a,ha,rfl⟩
  exact he.symm.trans ((Iff.of_eq hh).trans (and_iff_left ⟨a,rfl⟩))

private theorem fixed_profile (g : stabilizer)
    (hg : ∀ v ∈ T, g.val v = v) (U : Vertex) :
    Module.finrank F (act g U).val = Module.finrank F U.val ∧
      K (act g U).val = K U.val ∧ H (act g U).val = H U.val := by
  refine ⟨(g.val.submoduleMap U.val).finrank_eq.symm,?_,?_⟩
  · ext a
    change coordinates (a,0) ∈ U.val.map g.val.toLinearMap ↔
      coordinates (a,0) ∈ U.val
    have hf := hg (coordinates (a,0)) ⟨a,rfl⟩
    constructor
    · rintro ⟨u,hu,he⟩
      change g.val u = coordinates (a,0) at he
      have hu' : u = coordinates (a,0) := g.val.injective (he.trans hf.symm)
      exact hu' ▸ hu
    · intro ha
      exact ⟨coordinates (a,0),ha,hf⟩
  · ext a
    rw [H_mem,H_mem]
    have hf := hg (coordinates (a,0)) ⟨a,rfl⟩
    have hd (u : V) : dotProduct (g.val u) (coordinates (a,0)) =
        dotProduct u (coordinates (a,0)) := by
      simpa only [hf] using g.property.1 u (coordinates (a,0))
    constructor
    · intro h u hu
      have hh := h (g.val u) ⟨u,hu,rfl⟩
      rwa [hd] at hh
    · intro h v hv
      obtain ⟨u,hu,rfl⟩ := hv
      change dotProduct (g.val u) (coordinates (a,0)) = 0
      rw [hd]
      exact h u hu

/-- The entire restricted form on every actual nonzero submodule. -/
def restricted (U : Vertex) : LinearMap.BilinForm F U.val :=
  LinearMap.BilinForm.restrict (dotProductBilin F F : V →ₗ[F] V →ₗ[F] F) U.val

private theorem restricted_refl (U : Vertex) : (restricted U).IsRefl := by
  have hs : (restricted U).IsSymm := ⟨by
    intro u v
    change dotProduct u.val v.val = dotProduct v.val u.val
    exact dotProduct_comm _ _⟩
  exact hs.isRefl

/-- The entire radical quotient, with its actual induced nondegenerate form. -/
def quotientForm (U : Vertex) :=
  D5.S3.QuadraticForms.RadicalQuotientIsometry.reduced (restricted U) (restricted_refl U)

private def restrictedIso (g : stabilizer) (U : Vertex) :
    (restricted U).IsometryEquiv (restricted (act g U)) :=
  { g.val.submoduleMap U.val with
    map_app' := fun u v => g.property.1 u.val v.val }

private theorem quotient_isometric :
    Nonempty ((quotientForm firstVertex).IsometryEquiv (quotientForm secondVertex)) := by
  rw [← swap_first]
  exact ⟨D5.S3.QuadraticForms.RadicalQuotientIsometry.result
    (restricted_refl firstVertex) (restricted_refl (act swapElement firstVertex))
      (restrictedIso swapElement firstVertex)⟩

/-- The prohibited rule depends solely on the full original dimension/K/H
profile and the isometry type of the actual nondegenerate radical quotient. -/
def profileClaim : Prop :=
  ∃ (α : Type) (c : Vertex → α),
    (∀ U W, (NikandishClique.orthogonalityGraph 6).Adj U W → c U ≠ c W) ∧
    ∀ U W, Module.finrank F U.val = Module.finrank F W.val →
      K U.val = K W.val → H U.val = H W.val →
      Nonempty ((quotientForm U).IsometryEquiv (quotientForm W)) → c U = c W

private theorem profile_refutation : ¬ profileClaim := by
  rintro ⟨α,c,hc,he⟩
  have hp := fixed_profile swapElement swap_fixes_T firstVertex
  rw [swap_first] at hp
  exact hc _ _ lines_adjacent (he _ _ hp.1.symm hp.2.1.symm hp.2.2.symm quotient_isometric)

/-- The complete prohibited full-stabilizer assertion. Both branches quantify
all actual graph vertices and the entire original group. -/
def symmetryClaim : Prop :=
  (∃ c : Vertex → CliqueLabel,
    (∀ U W, (NikandishClique.orthogonalityGraph 6).Adj U W → c U ≠ c W) ∧
    ∀ (g : stabilizer) U, c (act g U) = labelAct g (c U)) ∨
  (∃ (α : Type) (c : Vertex → α),
    (∀ U W, (NikandishClique.orthogonalityGraph 6).Adj U W → c U ≠ c W) ∧
    ∀ (g : stabilizer) U, c (act g U) = c U)

/-- The actual adjacent line orbit refutes both entire-group assertions.
No proper-subgroup or auxiliary-choice obstruction is inferred. -/
private theorem symmetry_refutation : ¬ symmetryClaim := by
  rintro (⟨c,hc,he⟩ | ⟨α,c,hc,he⟩)
  · have h := he swapElement firstVertex
    rw [swap_first,swap_labels] at h
    exact hc _ _ lines_adjacent h.symm
  · have h := he swapElement firstVertex
    rw [swap_first] at h
    exact hc _ _ lines_adjacent h.symm

/-- The complete received profile/quotient and full-stabilizer assertions. -/
def claim : Prop := profileClaim ∨ symmetryClaim

/-- Actual adjacent lines refute every profile/quotient-only rule and both
entire-stabilizer assertions. All objects and quantifiers retain their full
original domains; auxiliary symmetry breaking remains an open possibility. -/
theorem result : ¬ claim := by
  rintro (h | h)
  · exact profile_refutation h
  · exact symmetry_refutation h

#print axioms result
end D5.S3.Combinatorics.Orthogonality.OrthogonalitySymmetryObstruction
