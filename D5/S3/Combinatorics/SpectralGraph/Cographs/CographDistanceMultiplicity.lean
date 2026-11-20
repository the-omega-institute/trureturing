/- GID: D5/S3/Combinatorics/SpectralGraph/Cographs/CographDistanceMultiplicity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Cographs/CographDistanceMultiplicity
   mirror-E: none
   anchors: []
   digest: Both clauses of the cograph distance multiplicity problem. -/

import D5.S3.Combinatorics.SpectralGraph.CographDistanceCriterion
import D5.S3.Combinatorics.SpectralGraph.Cographs.UniversalCliqueCographDistance

/-! # The distance multiplicity characterization and explicit attaining family -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.CographDistanceMultiplicity

open SimpleGraph Matrix CographDistanceCotree CographVicinalWidth NormalizedCographCotree
open D5.S3.QuadraticForms.SymmetricRankOneKernel (realGuardCandidates)

private theorem finrank_ker_toEuclideanLin {V : Type} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) :
    Module.finrank ℝ (LinearMap.ker A.mulVecLin) =
      Module.finrank ℝ (LinearMap.ker A.toEuclideanLin) := by
  let e := (WithLp.linearEquiv 2 ℝ (V → ℝ)).symm
  refine LinearEquiv.finrank_eq (e.ofSubmodules _ _ ?_)
  ext x
  rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
  change A *ᵥ WithLp.ofLp x = 0 ↔ Matrix.toLpLin 2 2 A x = 0
  rw [Matrix.toLpLin_apply, WithLp.toLp_eq_zero]

private theorem shiftedKernel_finrank_eq_distanceMultiplicity (r s b : ℕ) :
    Module.finrank ℝ (UniversalCliqueCographDistance.shiftedKernel r s b) =
      distanceMultiplicity (UniversalCliqueCographDistance.graph r s b) ((s : ℝ) - 2) := by
  classical
  unfold UniversalCliqueCographDistance.shiftedKernel distanceMultiplicity
  rw [finrank_ker_toEuclideanLin]
  let V := UniversalCliqueCographDistance.Vertex r s b
  let D := distanceMatrix (UniversalCliqueCographDistance.graph r s b)
  let dim (inst : Fintype V) (dec : DecidableEq V) : ℕ :=
    Module.finrank ℝ (LinearMap.ker ((D - ((s : ℝ) - 2) • (1 : Matrix V V ℝ)).toEuclideanLin))
  change dim _ _ = dim _ _
  exact congrArg₂ dim (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- The finite cotree characterization and one explicit attaining cograph
at each integer parameter at least two. The orders are strictly increasing. -/
theorem result :
    (∀ {V : Type} [Finite V] {G : SimpleGraph V},
      G.Connected → ¬(pathGraph 4).IsIndContained G →
      ((∃ x, Eligible x ∧ distanceMultiplicity G x = width G) ↔
        width G = 1 ∨
        (1 < width G ∧ ∃ (arity : Nontrivial (cutGraph G true).ConnectedComponent)
          (kind : (cutGraph G true).ConnectedComponent → Option Bool)
          (alternates : ∀ C, kind C ≠ some true)
          (child : ∀ C, Cotree (G.induce C.supp) (kind C)),
          let tree := Cotree.node true arity kind alternates child
          ∃ x ∈ realGuardCandidates (cotreeGuardData tree 0).subtreeGuards id,
            Eligible x ∧ JoinRootCriterion G kind x))) ∧
    (∀ s : ℕ, 2 ≤ s →
      Fintype.card (UniversalCliqueCographDistance.Vertex (3 * (s - 1)) s s) = 6 * s - 3 ∧
      let G := UniversalCliqueCographDistance.graph (3 * (s - 1)) s s
      G.Connected ∧ ¬(pathGraph 4).IsIndContained G ∧ width G = 2 ∧
        Eligible ((s : ℝ) - 2) ∧ distanceMultiplicity G ((s : ℝ) - 2) = width G) := by
  refine ⟨fun hc hP => distanceMultiplicity_attains_iff hc hP, ?_⟩
  intro s hs
  obtain ⟨hcard, hc, hP, hwidth, hel, _, hdim⟩ := UniversalCliqueCographDistance.family hs
  rw [dilworthNumber_eq_width] at hwidth
  have hw : width (UniversalCliqueCographDistance.graph (3 * (s - 1)) s s) = 2 := by
    exact_mod_cast hwidth
  rw [shiftedKernel_finrank_eq_distanceMultiplicity] at hdim
  exact ⟨hcard, hc, hP, hw, hel, hdim.trans hw.symm⟩

end D5.S3.Combinatorics.SpectralGraph.CographDistanceMultiplicity
