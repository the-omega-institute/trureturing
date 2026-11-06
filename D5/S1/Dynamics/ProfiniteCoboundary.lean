/- GID: D5/S1/Dynamics/ProfiniteCoboundary
   generality: G
   mirror-B: D5/B/S1/Dynamics/ProfiniteCoboundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized finite quotient transfers assemble into a continuous profinite transfer. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.FiniteActionTrivialization
import Mathlib.Dynamics.Minimal
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

set_option autoImplicit false

open Set CategoryTheory

namespace D5.S1.Dynamics.ProfiniteCoboundary

open D5.S1.Dynamics.Symbolic.PermutativeLifts

universe u v

variable {X : Type v} [TopologicalSpace X] [AddAction ℤ X]

private theorem transfer_eq_of_eq_at
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {x₀ : X} (hdense : Dense (AddAction.orbit ℤ x₀)) {c b d : X → G}
    (hb : Continuous b) (hd : Continuous d)
    (hbstep : ∀ x, b ((1 : ℤ) +ᵥ x) = c x * b x)
    (hdstep : ∀ x, d ((1 : ℤ) +ᵥ x) = c x * d x)
    (hbase : b x₀ = d x₀) : b = d := by
  have hstep (x : X) :
      (b ((1 : ℤ) +ᵥ x))⁻¹ * d ((1 : ℤ) +ᵥ x) = (b x)⁻¹ * d x := by
    rw [hbstep, hdstep]
    simp [mul_assoc]
  apply Continuous.ext_on hdense hb hd
  rintro z ⟨g, rfl⟩
  apply inv_mul_eq_one.mp
  calc
    (b (g +ᵥ x₀))⁻¹ * d (g +ᵥ x₀) = (b x₀)⁻¹ * d x₀ :=
      invariant_of_unitStep (fun x => (b x)⁻¹ * d x) hstep g x₀
    _ = 1 := by rw [hbase]; simp

/-- If the basepoint has dense integer orbit, continuous solutions in every
finite open-normal quotient assemble into a unique continuous solution in the
profinite group, normalized to one at the basepoint. No countability or
metrizability, compactness of the source, or commutativity is required. -/
theorem exists_unique_continuous_transfer_of_finite_quotients
    (x₀ : X) (hdense : Dense (AddAction.orbit ℤ x₀)) (P : ProfiniteGrp.{u})
    (c : X → P)
    (hquot : ∀ U : OpenNormalSubgroup P,
      ∃ b : X → (ProfiniteGrp.diagram P).obj U,
        Continuous b ∧ ∀ x,
          b ((1 : ℤ) +ᵥ x) = (ProfiniteGrp.proj U) (c x) * b x) :
    ∃! b : X → P, Continuous b ∧ b x₀ = 1 ∧
      ∀ x, b ((1 : ℤ) +ᵥ x) = c x * b x := by
  classical
  choose b hb hstep using hquot
  let β (U : OpenNormalSubgroup P) (x : X) := b U x * (b U x₀)⁻¹
  have hβcont (U : OpenNormalSubgroup P) : Continuous (β U) :=
    (hb U).mul continuous_const
  have hβone (U : OpenNormalSubgroup P) : β U x₀ = 1 := by
    simp [β]
  have hβstep (U : OpenNormalSubgroup P) (x : X) :
      β U ((1 : ℤ) +ᵥ x) = (ProfiniteGrp.proj U) (c x) * β U x := by
    dsimp only [β]
    rw [hstep U x, mul_assoc]
  have hcompat {U V : OpenNormalSubgroup P} (f : U ⟶ V) (x : X) :
      (ProfiniteGrp.diagram P).map f (β U x) = β V x := by
    let q := ((ProfiniteGrp.diagram P).map f).hom
    have hqstep (y : X) : q (β U ((1 : ℤ) +ᵥ y)) =
        (ProfiniteGrp.proj V) (c y) * q (β U y) := by
      rw [hβstep U y, map_mul]
      rfl
    have hbase : q (β U x₀) = β V x₀ := by
      rw [hβone, map_one, hβone]
    have he : (fun y => q (β U y)) = β V :=
      transfer_eq_of_eq_at hdense (q.continuous.comp (hβcont U)) (hβcont V)
        hqstep (hβstep V) hbase
    exact congrFun he x
  let B : X → ProfiniteGrp.limit (ProfiniteGrp.diagram P) := fun x =>
    ⟨fun U => β U x, fun {U V} f => hcompat f x⟩
  have hBcont : Continuous B := (continuous_pi hβcont).subtype_mk _
  let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
  let bP : X → P := fun x => e.symm (B x)
  have hbPcont : Continuous bP := e.symm.continuous.comp hBcont
  have hBone : B x₀ = 1 := by
    apply ProfiniteGrp.limit_ext
    intro U
    exact hβone U
  have hbPone : bP x₀ = 1 := by
    simp only [bP, hBone, map_one]
  have hBstep (x : X) : B ((1 : ℤ) +ᵥ x) = e (c x) * B x := by
    apply ProfiniteGrp.limit_ext
    intro U
    exact hβstep U x
  have hbPstep (x : X) : bP ((1 : ℤ) +ᵥ x) = c x * bP x := by
    change e.symm (B ((1 : ℤ) +ᵥ x)) = c x * e.symm (B x)
    rw [hBstep, map_mul, e.symm_apply_apply]
  refine ⟨bP, ⟨hbPcont, hbPone, hbPstep⟩, ?_⟩
  intro d hd
  exact transfer_eq_of_eq_at hdense hd.1 hbPcont hd.2.2 hbPstep
    (hd.2.1.trans hbPone.symm)

end D5.S1.Dynamics.ProfiniteCoboundary
