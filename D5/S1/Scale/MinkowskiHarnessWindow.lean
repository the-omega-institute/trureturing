/- GID: D5/S1/Scale/MinkowskiHarnessWindow
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Minkowski window membership gives the formal harness acceptance dictionary. -/

/-
本单仅关"形式词典面";
不冒领完整 cut-and-project 公理(goldenLattice 离散/余紧/窗紧致均未证);
不宣称等于 C# harness/B6 晋升之操作语义(经验面 open,B9 双检验面之另一半)。
声明名独立(作者同席纪律:共窗机器不共地址)。
-/

import D5.S1.Scale.MinkowskiModelSet

namespace D5.S1.Scale

open D5.S0.Carrier

/-- Formal acceptance means that the conjugate embedding lies in the window. -/
def minkowskiHarnessAccepts (window : Set ℝ) (x : GoldenInt) : Prop :=
  embedding (conj x) ∈ window

/-- Golden lifts accepted by the formal Minkowski-window predicate. -/
abbrev HarnessAcceptedLift (window : Set ℝ) :=
  {x : GoldenInt // minkowskiHarnessAccepts window x}

/-- Physical points belonging to the model set selected by `window`. -/
abbrev WindowPoint (window : Set ℝ) := {y : ℝ // y ∈ modelSet window}

/-- Formal harness acceptance is exactly membership of the physical image in the model set. -/
theorem minkowski_harness_accepts_iff_window (window : Set ℝ) (x : GoldenInt) :
    minkowskiHarnessAccepts window x ↔ embedding x ∈ modelSet window := by
  constructor
  · intro hx
    exact ⟨x, rfl, hx⟩
  · rintro ⟨z, hz, hwindow⟩
    have hzx : z = x := embedding_injective hz
    simpa [minkowskiHarnessAccepts, hzx] using hwindow

/-- Accepted Golden lifts correspond bijectively to physical model-set points. -/
noncomputable def minkowskiHarnessEquiv (window : Set ℝ) :
    HarnessAcceptedLift window ≃ WindowPoint window :=
  Equiv.ofBijective
    (fun x =>
      ⟨embedding x.1,
        (minkowski_harness_accepts_iff_window window x.1).mp x.2⟩)
    ⟨by
      intro x z hxz
      apply Subtype.ext
      apply embedding_injective
      exact congrArg Subtype.val hxz,
    by
      rintro ⟨y, hy⟩
      rcases hy with ⟨x, hxy, hwindow⟩
      refine ⟨⟨x, hwindow⟩, ?_⟩
      apply Subtype.ext
      exact hxy⟩

end D5.S1.Scale
