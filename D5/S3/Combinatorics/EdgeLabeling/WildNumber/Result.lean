/- GID: D5/S3/Combinatorics/EdgeLabeling/WildNumber/Result
   generality: I
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/WildNumber/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Arbitrarily large additive gaps between greedy wild sets and the wild number. -/

/-
admission_basis: open-problem-resolution (#20098; Proved)
escape_witness: none
Direct frozen dependencies: none.
result: proof_shape: content; escape_witness: none; Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21209
-/

import D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph
import D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild
import D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
import D5.S3.Combinatorics.EdgeLabeling.WildNumber.Relabel
import D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate
import Mathlib.Logic.Equiv.Fin.Basic

namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.Result
open SimpleGraph
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Greedy
open D5.S3.Combinatorics.EdgeLabeling.WildNumber.Relabel
def claim : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), ∃ γ : G.edgeSet → Fin 4,
    G.Connected ∧ Function.Surjective γ ∧ wildNumber G γ = 5 * r ∧
      (∃ W, IsGreedyOutput G γ W) ∧ ∀ W, IsGreedyOutput G γ W → W.card = 6 * r
theorem result : claim := by
  classical
  let e : Fin 8 ≃ Option (Fin 7) := finSuccEquiv' (0 : Fin 8)
  let B := D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H.map e
  let f : D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H ≃g B := SimpleGraph.Iso.map e D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H
  let γ := SimpleGraph.EdgeLabeling.pullback D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma f.symm.toHom
  have hB : B.Connected := f.connected_iff.mp D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.H_connected
  have hγ : Function.Surjective γ := colorMap_surjective f D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma_surjective
  have hO : ∃ W, IsColorConnecting B γ W ∧ W.card = 5 :=
    ⟨(fun f W => Finset.image (Sym2.map f) W) f D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.O,(connecting_iff f _ _).mpr D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.O_color_connecting,
      by rw [setMap_card]; exact D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.O_card⟩
  have hl : ∀ W, IsColorConnecting B γ W → 5 ≤ W.card := by
    intro W hc
    obtain ⟨U,rfl⟩ := setMap_surjective f W
    rw [setMap_card]
    exact D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.color_connecting_card_ge_five U ((connecting_iff f _ _).mp hc)
  have ho : ∀ W, IsGreedyOutput B γ W → W.card = 6 := by
    intro W hc
    obtain ⟨U,rfl,hu⟩ := output_reflect f D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.gamma hc
    rw [setMap_card]
    exact D5.S3.Combinatorics.EdgeLabeling.WildNumber.WheelCertificate.Wheel.all_outputs_six U hu
  intro r hr
  have ha := D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild.amplify B γ hB hγ 5 6 hO hl ho r hr
  let Br := D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamGraph.starGraph (fun _ : Fin r => B)
  let γr := D5.S3.Combinatorics.EdgeLabeling.WildNumber.AmalgamWild.starColor (fun _ : Fin r => B) (fun _ => γ)
  change Br.Connected ∧ Function.Surjective γr ∧ wildNumber Br γr = 5*r ∧
    (∃ W, IsGreedyOutput Br γr W) ∧
    ∀ W, IsGreedyOutput Br γr W → W.card = 6*r at ha
  let q : Option (Fin r × Fin 7) ≃ Fin (7*r + 1) :=
    Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])
  let K := Br.map q
  let g : Br ≃g K := SimpleGraph.Iso.map q Br
  refine ⟨7*r + 1,K,(SimpleGraph.EdgeLabeling.pullback γr g.symm.toHom),g.connected_iff.mp ha.1,
    colorMap_surjective g γr ha.2.1,?_,?_,?_⟩
  · rw [wildNumber_map]
    exact ha.2.2.1
  · obtain ⟨W,hw⟩ := ha.2.2.2.1
    exact ⟨(fun f W => Finset.image (Sym2.map f) W) g W,run_map g γr hw.1,(connecting_iff g γr W).mpr hw.2⟩
  · intro W hw
    obtain ⟨U,rfl,hu⟩ := output_reflect g γr hw
    rw [setMap_card]
    exact ha.2.2.2.2 U hu
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.Result
