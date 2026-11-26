/- GID: D5/S3/Zeros/GRH/Lib/SiegelWeil/StrongApproximation/EqualRankConstant
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/SiegelWeil/StrongApproximation/EqualRankConstant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.SiegelWeil.StrongApproximation.EqualRankConstant. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/SiegelWeil/StrongApproximation/EqualRankConstant.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.SiegelWeil.SingularForms.SingularForms
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Strong approximation for isotropic unitary groups. It is stated here for functions
on the full unitary group, where invariance under rational points, a split place, the compact group
and the torus of a hyperbolic plane forces constancy. The proof uses unipotent radicals and rational
quasi-reflections. Source: M. Kneser, Starke Approximation in algebraischen Gruppen I, J. reine
angew. Math. 218 (1965); G. Shimura, Arithmetic of unitary groups, Ann. of Math. 79 (1964); survey
A. Rapinchuk, MSRI Publ. 61 (2013).

This file: Automorphic function invariant at a split place, compact group and torus is constant. -/

open Matrix WeilData Space Splitting G Gf MulAction MatMul Set
attribute [local simp] smul_smul Prod.map
attribute [-simp] Algebra.smul_mul_assoc

/-- Let D be continuous on [U(W)], W split along a line, right invariant under points supported
on S ∪ S̄ (S nonempty) and integral points off S. If invariance under the radical makes D on
the Levi independent of the torus, then D is constant.

Known result: Strong approximation for isotropic unitary groups. -/
lemma IsAutFunction.apply_eq_apply_one {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
  [Fintype m] {s s₀} {W : Space E n s} {W₀ : Space E m s₀} (H : W.Splitting W₀ Unit) {S D} (hD :
  IsAutFunction W D) (hS : S.Nonempty) (on : HasLevel D (supportedOn n S)) (hK :
  HasLevel D (Kf E n ⊓ Gf.trivialOn n S)) (h : (∀ c z g,
  D (H.radicalElt c z * g) = D g) → ∃ F : _ → ℂ, ∀ t g, D (H.levi (t, g)) = F g) : ∀ g, D g = D 1 :=
  have o a b e := (congrArg D (ext_mat (by simpa [-map_mul, ← mul_assoc, ← mat_mul b]) :
    a = b * closurePart S (b⁻¹ * a))).trans (on _ componentOn_mem_supportedOn b)
  -- strong approximation in the radical
  have N (H : W.Splitting W₀ Unit) c z g : D (H.radicalElt c z * g) = D g :=
    ((denseRange_rat_matrix_add hS.inl W₀.x).prodMap (denseRange_rat_matrix_add hS.inl 1)).eq (f :=
    fun q ↦ D (H.radicalElt q.1 q.2 * g)) (fun ⟨⟨Y, _⟩, A, _⟩ ↦ (o _ _ (by
    rw [← conjClosure]; simp [radicalElt, smul_sub, mul_left_comm (idemAdele S.conjClosure)]
    module)).trans
    (hD.2 _ (H.radicalElt_mem_Gamma Y ⟨A, rfl⟩) g)) (hD.rec (by fun_prop)) continuous_const (c, z)
  (W.weak_approximation finite_empty).eq (fun ⟨γ, k, _⟩ ↦ by
  obtain ⟨⟨κ, hκ, t, -, -, c, z, x, e⟩, ⟨F, h⟩, T, τ, θ⟩ := H.iwasawa k, h (N H),
    k.eventually_atPlace_mem_Kw.exists_mem
  choose a p b q i K using (k⁻¹ * componentOn n Tᶜ (k * κ.2)).exists_supportedOn_mul_trivialOn S
  rw [hD.2 _ γ.2, ← on a p, ← hK b ⟨(K (by simp +contextual [mem_Kf_iff, ite_mem, mem_Kf_iff.1 hκ.2,
    θ])).2, q⟩, (by simp [closurePart, mul_assoc, ← i] : _ * _ = closurePart Tᶜ (↑k * κ)), e,
    map_mul, closurePart_radicalElt, N]
  refine (W₀.weak_approximation τ).induction_on x (isClosed_singleton.preimage_of_continuous
    (hD.1.comp (by simp [↓continuous_iff, Splitting.levi]; fun_prop))) fun ⟨⟨_, γ, rfl⟩, k, f⟩ ↦
    (witt_of_quasiReflection_mem exists_isUnit_sub_star W₀.conjTranspose_J (by simp) ⟨_, one_mul _⟩
    ⟨_, γ.1.4⟩ (by simp [mem_U.1]) (((((stabilizer _ᵈᵐᵃ D).unop.comap (closurePart Tᶜ)).comap
    H.levi).map (.snd ..)).comap W₀.ratEmbed) fun v σ e ↦ ?_).rec fun g ⟨⟨a, e, i⟩, l⟩ ↦ ?_
  -- the radicals reach the quasi-reflections in the Levi factor, up to the torus
  let c := W₀.x⁻¹.1 * (replicateCol Unit v).map toAdele
  let M x := H.symm.radicalElt (toAdele x • c) (toAdele (-j * x * (j * σ + 1) : E) • 1)
  refine (H.exists_eq_radicalElt_mul_levi (g := M σ⁻¹ * H.radicalElt 0 1 * M j) (a := toAdele
    (-j * σ : E) • 1) ?_).elim fun _ ⟨_, t, m, p, _, q⟩ ↦ ⟨(t, m), by simpa [closurePart_radicalElt,
    N, M, mul_assoc] using! congr((D <| closurePart Tᶜ ($p) * ·)).symm,
    ext_mat (q.trans ?_)⟩ <;> simp [M, radicalElt, (by ext1; simp [e, ← stdForm_vecAtPoint]; rfl :
    cᴴ * (stdForm E s₀ * c) = toAdele (σ + star ↑σ : E) • 1)]
  clear * -; match_scalars <;> simp only [← map_mul, ← map_add, ← map_neg, ← map_sub,
    ← map_one toAdele] <;> grind [σ.ne_zero, star_eq_zero]
  simp [c, quasiReflection, Matrix.map_sub, map_smul', vecMulVec_eq Unit, W₀.map_J,
    replicateRow_vecMul, mat_ratEmbed]; match_scalars <;> grind
  simpa +contextual [h, eq_of_supportedOn componentOn_mem_supportedOn (one_mem _), mem_trivialOn.1
    f, closurePart, ← i, ↓fun t g ↦ (ext_mat (by simp [Splitting.levi, cutGL,
    ← H.sum_frame_mul_coord_eq_one, -coe_units_inv]; module) : closurePart Tᶜ (H.levi (t, g)) =
    H.levi (cutGL idemAdele_cj_mul_self t, closurePart Tᶜ g)), (by ext; simp [← l] : γ = g)]
    using (congr($e 1) : D (closurePart _ _ * 1) = _)) hD.1
