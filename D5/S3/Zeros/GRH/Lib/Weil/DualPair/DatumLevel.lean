/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/DatumLevel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/DatumLevel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.DatumLevel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/DatumLevel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.BlockMatrices
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.PairReal
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

This file: Finite vectors of the Weil representation are fixed by open subgroups. -/

/-- Every f in the finite part of the data space of Hom(S,T) is fixed, under the representation
`pairWeil` with characters a, b, by K × K' for some open subgroups K, K' of the two finite
adelic unitary groups. -/
lemma exists_level_pairWeil {E n n' s s'} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n']
    {S : Space E n s} {T : Space E n' s'} a b {f} (hf : f ∈ (S.hom T).finitePart) :
    ∃ K K' : OpenSubgroup _, ∀ᵉ (k ∈ K) (k' ∈ K'), pairWeil S T a b ((1, k), 1, k') f = f := by
  let j : _ →ₜ* G E s × G E s' := .prodMap (.inr ..) (.inr ..)
  peel NonarchimedeanGroup.prod_subset ((char_eventually_eq_one (.comp (.coprod (b⁻¹.1.1.comp G.det)
    (a.1.1.comp G.det)) j.1) (by simp [Function.comp_def]; fun_prop)).and
    ((G.continuous_onHom.comp j.2).snd.tendsto' _ _ (by simp) (Space.eventually_omega_eq_self hf)))
  simp_all [pairWeil_apply, pairChar, j, ← G.onHom_fin, Set.subset_def]
