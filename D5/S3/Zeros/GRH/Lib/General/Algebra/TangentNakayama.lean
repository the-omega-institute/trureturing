/- GID: D5/S3/Zeros/GRH/Lib/General/Algebra/TangentNakayama
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Algebra/TangentNakayama
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Algebra.TangentNakayama. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Algebra/TangentNakayama.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Analysis.ZpowSum
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of commutative and general algebra (textbook or folklore). -/

open DualNumber Module RingHom Algebra FinitePresentation Ideal Quotient TrivSqZeroExt

/-- Nakayama in tangent form: let x : S → V be a section of a finite type V-algebra, φ : V → k a
field point, I ⊆ ker x. If every k[ε]-point over φ lifting φ∘x that kills I kills ker x,
some b with b·ker x ⊆ I has φ(x(b)) ≠ 0. -/
lemma exists_mem_colon_of_tangent {V S k} [CommRing V] [CommRing S] [Algebra V S] [FiniteType V S]
    [Field k] [Algebra V k] {x : S →ₐ[V] V} {o} (e : (ofId V k).comp x = o) {I}
    (hI : I ≤ ker x) (h : ∀ w : S →ₐ[V] k[ε], (∀ s, (w s).fst = o s) → I ≤ ker w →
    ∀ s, (w s).snd = 0) : ∃ b ∈ I.colon (ker x), o b ≠ 0 := by
  algebraize [x.1]; by_contra! H
  let ϖ a : Submodule.map I.mkQ (ker x) := ⟨_, a - ofId V S (x a), by simp, rfl⟩
  have := of_restrict_scalars_finitePresentation V S
  have := Finite.of_fg (N := ker x) (ker_fG_of_surjective (ofId ..) (⟨_, x.2 ·⟩))
  refine (@exists_ne _ ((LinearMap.liftBaseChangeEquiv _).nontrivial_congr.2 ((nontrivial_dual_iff
    _).2 ((mem_support_iff_nontrivial_residueField_tensorProduct ⟨_, ker_isPrime o⟩).1
    (mem_support_iff_of_finite.2 (I.annihilator_map_mkQ_eq_colon ▸ H))))) 0).elim fun l ↦ (· ?_)
  ext ⟨_, q, g, rfl⟩; convert h ⟨⟨⟨⟨fun s ↦ inl (o s) + inr ((l (ϖ s)).lift (ker o) _ le_rfl fun _ ↦
    .mk0 _), ?_⟩, by simp [show ∀ s t, ϖ (s * t) = s • ϖ t + x t • ϖ s by simp [ϖ, smul_def]; grind,
    @smul_def S, ← algebraMap_smul S, TrivSqZeroExt.ext_iff, ← e]; grind⟩, _, _⟩, _⟩ _ _ q <;>
    simp +contextual [← map_add, ϖ, sub_add_sub_comm, ← e, mem_ker.1 g, TrivSqZeroExt.ext_iff,
    ← ZeroMemClass.zero_def, LE.le, mem_ker.1 (hI _), eq_zero_iff_mem.2, algebraMap_eq_inl']
