import Reg.Support.DependentFamily
import D5.S3.Quantum.Algebra.OriginalCompactReciprocity

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.OriginalCompactActionMetric
open _root_.D5.S3.Quantum.Algebra.OriginalCompactReciprocity

noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Algebra.OriginalCompactReciprocity.CurveExponential

/-- The full original telescope, including zero-dimensional fibers. -/
structure Parameters where
  W : Type u
  [normed : NormedAddCommGroup W]
  [inner : InnerProductSpace ℝ W]
  [finite : FiniteDimensional ℝ W]
  G : MatrixGroup W
  compact : IsCompact (G : Set (W →L[ℝ] W)ˣ)

attribute [instance] Parameters.normed Parameters.inner Parameters.finite

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.W →L[ℝ] p.W
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p K => K ∈ velocitySpace p.G) (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : Parameters.{u}) (K : p.W →L[ℝ] p.W),
    R.readout () p K ↔ ∀ t : ℝ, ∃ g : (p.W →L[ℝ] p.W)ˣ,
      g ∈ p.G ∧ (g : p.W →L[ℝ] p.W) = NormedSpace.exp (t • K)

theorem full_telescope_bridge :
    (type_of% (@mem_velocitySpace_iff_exp.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p K
    exact h p.G p.compact K
  · intro h W _ _ _ G hG K
    exact h ⟨W, G, hG⟩ K

private def realPoint : Parameters.{0} where
  W := ℝ
  G := ⊥
  compact := by simpa using
    (isCompact_singleton : IsCompact ({1} : Set (ℝ →L[ℝ] ℝ)ˣ))

private theorem rejected_law : ¬ arena.{0}.Law rejected := by
  intro h
  have hz := h realPoint 0
  have hr : ∀ t : ℝ, ∃ g : (ℝ →L[ℝ] ℝ)ˣ,
      g ∈ realPoint.G ∧ (g : ℝ →L[ℝ] ℝ) = NormedSpace.exp (t • (0 : ℝ →L[ℝ] ℝ)) := by
    intro t
    exact ⟨1, realPoint.G.one_mem, by simp⟩
  exact (hz.mpr hr).elim

private theorem bot_velocity (K : ℝ →L[ℝ] ℝ) :
    K ∈ velocitySpace (⊥ : MatrixGroup ℝ) ↔ K = 0 := by
  constructor
  · rintro ⟨c, hc, hd⟩
    have he : (fun t => (c t).val.val) = fun _ : ℝ => (1 : ℝ →L[ℝ] ℝ) := by
      funext t
      have h := (c t).property
      simpa using congrArg Units.val (Subgroup.mem_bot.mp h)
    rw [he] at hd
    exact hd.unique (hasDerivAt_const (0 : ℝ) 1)
  · rintro rfl
    exact (velocitySpace (⊥ : MatrixGroup ℝ)).zero_mem

/-- Whole-family kernel evidence; current source-selection binding is separate. -/
def family : Registration arena.{0} (type_of% (@mem_velocitySpace_iff_exp.{0})) where
  actual := actual
  bridge := full_telescope_bridge
  variation := ⟨full_telescope_bridge.mp (@mem_velocitySpace_iff_exp.{0}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨realPoint, 0, 1, ?_⟩
    change (0 ∈ velocitySpace (⊥ : MatrixGroup ℝ)) ≠
      ((1 : ℝ →L[ℝ] ℝ) ∈ velocitySpace (⊥ : MatrixGroup ℝ))
    intro he
    have hz := (velocitySpace (⊥ : MatrixGroup ℝ)).zero_mem
    have hone := bot_velocity 1 |>.mp (he ▸ hz)
    have hh := congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) hone
    norm_num at hh

end Reg.D5.S3.Quantum.Algebra.OriginalCompactReciprocity.CurveExponential

namespace Reg.D5.S3.Quantum.Algebra.OriginalCompactReciprocity.OriginalExponential

abbrev signature : Signature where
  Params := CurveExponential.Parameters.{u}
  State p := OriginalLie p.G × p.W
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p _ => ∃ B : InnerProductSpace.Core ℝ p.W,
    (∀ (g : p.G) (v w : p.W), B.inner (g.val.val v) (g.val.val w) = B.inner v w) ∧
    Module.finrank ℝ p.W = 3 ∧ Module.finrank ℝ (OriginalLie p.G) = 3 ∧
    LinearMap.range (originalAction p.G) = skewEndomorphisms B ∧
    (∀ g ∈ connectedComponent (1 : p.G), g.val.val.det = 1) ∧
    ∀ K : p.W →L[ℝ] p.W, K.toLinearMap ∈ skewEndomorphisms B →
      ∀ t : ℝ, ∃ g : p.G, g ∈ connectedComponent (1 : p.G) ∧
        g.val.val = NormedSpace.exp (t • K)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : CurveExponential.Parameters.{u}) (A : OriginalLie p.G) (x : p.W),
    A ≠ 0 → x ≠ 0 → A.val x = 0 → FullReciprocity p.G A x → R.readout () p (A,x)

/-- Exact reconstruction retains the original compact group, witnesses and all conclusions. -/
theorem full_telescope_bridge :
    (type_of% (@original_exponential_rigidity.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p A x
    exact h p.G p.compact A x
  · intro h W _ _ _ G hG A x
    exact h ⟨W,G,hG⟩ A x

theorem actual_positive : arena.{u}.Law actual :=
  full_telescope_bridge.mp (@original_exponential_rigidity.{u})

end Reg.D5.S3.Quantum.Algebra.OriginalCompactReciprocity.OriginalExponential

namespace Reg.D5.S3.Quantum.Algebra.OriginalCompactReciprocity.ReverseFullRelation

/-- No compactness or nonzero-dimensional premise is hidden in the source family. -/
structure Parameters where
  W : Type u
  [normed : NormedAddCommGroup W]
  [inner : InnerProductSpace ℝ W]
  [finite : FiniteDimensional ℝ W]
  G : MatrixGroup W
  B : InnerProductSpace.Core ℝ W

attribute [instance] Parameters.normed Parameters.inner Parameters.finite

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := OriginalLie p.G × p.W
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p s => FullReciprocity p.G s.1 s.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ p : Parameters.{u}, Module.finrank ℝ p.W = 3 →
    LinearMap.range (originalAction p.G) = skewEndomorphisms p.B →
    ∃ s : OriginalLie p.G × p.W,
      s.1 ≠ 0 ∧ s.2 ≠ 0 ∧ s.1.val s.2 = 0 ∧ R.readout () p s

/-- Both bijections refer to the entire original relation in the exact source telescope. -/
theorem full_telescope_bridge :
    (type_of% (@fullReciprocity_of_full_skew.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p hW hfull
    obtain ⟨A,x,ha,hx,hAx,hQ⟩ := h p.G p.B hW hfull
    exact ⟨(A,x),ha,hx,hAx,hQ⟩
  · intro h W _ _ _ G B hW hfull
    obtain ⟨s,ha,hx,hAx,hQ⟩ := h ⟨W,G,B⟩ hW hfull
    exact ⟨s.1,s.2,ha,hx,hAx,hQ⟩

theorem actual_positive : arena.{u}.Law actual :=
  full_telescope_bridge.mp (@fullReciprocity_of_full_skew.{u})

end Reg.D5.S3.Quantum.Algebra.OriginalCompactReciprocity.ReverseFullRelation


namespace Reg.D5.S3.Quantum.Algebra.OriginalCompactReciprocity.OriginalGroup

abbrev signature : Signature where
  Params := CurveExponential.Parameters.{u}
  State p := OriginalLie p.G × p.W
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u}
  (fun _ p _ => ∃ B : InnerProductSpace.Core ℝ p.W,
    (∀ (g : p.G) (v w : p.W), B.inner (g.val.val v) (g.val.val w) = B.inner v w) ∧
    Module.finrank ℝ p.W = 3 ∧ Module.finrank ℝ (OriginalLie p.G) = 3 ∧
    LinearMap.range (originalAction p.G) = skewEndomorphisms B ∧
    p.G.subtype '' connectedComponent (1 : p.G) =
      {v : (p.W →L[ℝ] p.W)ˣ | (∀ x y, B.inner (v.val x) (v.val y) = B.inner x y) ∧
        v.val.det = 1} ∧
    ((p.G : Set (p.W →L[ℝ] p.W)ˣ) =
      {v | (∀ x y, B.inner (v.val x) (v.val y) = B.inner x y) ∧ v.val.det = 1} ∨
     (p.G : Set (p.W →L[ℝ] p.W)ˣ) =
      {v | ∀ x y, B.inner (v.val x) (v.val y) = B.inner x y})) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : CurveExponential.Parameters.{u}) (A : OriginalLie p.G) (x : p.W),
    A ≠ 0 → x ≠ 0 → A.val x = 0 → FullReciprocity p.G A x → R.readout () p (A,x)

/-- Exact reconstruction preserves the intrinsic component image and both full-group cases. -/
theorem full_telescope_bridge :
    (type_of% (@original_group_rigidity.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p A x
    exact h p.G p.compact A x
  · intro h W _ _ _ G hG A x
    exact h ⟨W,G,hG⟩ A x

theorem actual_positive : arena.{u}.Law actual :=
  full_telescope_bridge.mp (@original_group_rigidity.{u})

end Reg.D5.S3.Quantum.Algebra.OriginalCompactReciprocity.OriginalGroup
