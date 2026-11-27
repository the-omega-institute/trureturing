/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/ThetaIntegralLaws
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/ThetaIntegralLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.ThetaIntegralLaws. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/ThetaIntegralLaws.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.TwoLineTerms
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.FourierCoefficient
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Name for the real slice of a datum in the mixed model. Real part of the slice at an
isotropic line in the constant term. Basic laws of theta integrals: equivariance, linearity,
automorphy, boundedness for full-rank data. -/

/-- The slice of a real datum for (X,V) at the real part of the adelic matrix x: its value in the
mixed model of D, a real datum for (W₁,V). -/
noncomputable def realSlice {E} [Field E] [CMType E] [WeilData E] {n a b m} [Fintype n]
  [Fintype a] [Fintype b] [Fintype m] {s t r} {X : Space E m r} {W₁ : Space E n s}
  (D : X.Splitting W₁ b) (V : Space E a t) [IsBaseAdapted D] (x : Matrix a b (𝔸 E)) : PairFock E r t
  →L[ℂ] PairFock E s t := (isAdapted_homSource D V).mixedModel.slice fun p ↦ (matToVec x p.2).1 p.1

/-- The real counterpart of `lineTerm`: the slice, in the mixed model of the adapted
splitting chosen from `tsum_lineTerm`, at the point with last coordinates a ∈ ℂ^f and
others 0. -/
@[irreducible] noncomputable def lineTermReal {E} [Field E] [CMType E] [WeilData E] {n n' r r'}
  [Fintype n] [Fintype n'] [Fintype r] [Fintype r'] {s s' t t'} {W : Space E n s} {W' :
  Space E n' s'} {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X :
  V'.Splitting V Unit) [IsBaseAdapted A] [IsBaseAdapted X] β (a : _ → ℂ) := (tsum_lineTerm A X
  β).2.choose_spec.choose_spec.2.1.mixedModel.slice fun (x, y) ↦ a x * y.isRight.toNat

open Matrix MeasureTheory Space CompactlyCoherentSpace
variable {E : Type} {n} {n'} {F : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n']
  {s : n → ℤˣ} {s' : n' → ℤˣ} {μ : NumberField.InfinitePlace E → ℤ} (S : Space E n s)
  (T : Space E n' s') {v} [SemilocalField F] {A : Set (FinPlace E)} {φ : Matrix n' n F → ℂ}
  {π : 𝔸f E →+* F} {U : Set (Matrix n' n F)} (r : ReadsAt A π) (𝔠 : SplitTameChar E μ)

omit [WeilData E] in
lemma atPlaces_star {P} (g : Gf E n) : (g.1.1.map ((evalPlaces P).comp (starRingEnd _)))ᵀ =
  (atPlaces P g⁻¹).1 ∧ g.1.1.map (evalPlaces P) = (atPlaces P g).1 :=
  ⟨congr(map $(_root_.U.inv_val_eq_conjTranspose g) (evalPlaces P)).symm, rfl⟩

omit [WeilData E] [Fintype n] [Fintype n'] in
lemma ReadsAt.isSchwartzBruhat : ReadsAt A π → φ ∈ schwartzBruhat U →
  IsSchwartzBruhat A (φ <| vecToMat · |>.map π) | ⟨_, _, _, σ, _, k, h⟩, hφ => ⟨by
  simp [vecToMat, Matrix.map, ← h, k], hφ.1.comp_continuous (by continuity), (σ ∘ matToVec ·) '' _,
  hφ.2.1.image (by fun_prop [matToVec]), fun _ ↦ (⟨_, subset_closure ·, funext (by tauto)⟩)⟩

/-- The theta integral over [U(T)] of the datum v ⊗ Φ at the ramified places of 𝔠, both
characters being ν⁻¹υ^⌊n/2⌋, n = rk S. -/
noncomputable abbrev thetaLarge v Φ :=
  thetaIntegral S T (rankTwist 𝔠.ν⁻¹ n) (rankTwist 𝔠.ν⁻¹ n) (localDatum S T v Φ 𝔠.readsAt)

/-- There are B and C with |θ^{S,T}_{α,β}(f)(g,h)| ≤ C·ht(g)^B for all characters α, β and all
g, h: polynomial growth in g, uniformly in h. -/
def IsTargetBounded f := ∃ B C, ∀ α β g h, ‖pairTheta S T α β f (g, h)‖ ≤ C * S.height g ^ B

lemma exists_linear_thetaIntegral α β : ∃ Λ : _ →ₗ[ℂ] _, ∀ {f}, IsTargetBounded S T f → Λ f =
  thetaIntegral S T α β f := (LinearMap.exists_extend (K := ℂ) (p := ⟨⟨⟨(Integrable (ε := ℂ) · _),
  .add⟩, integrable_zero ..⟩, .smul⟩) ⟨⟨(integral _ ·.1), (integral_add ·.2 ·.2)⟩,
  (integral_smul · ·.1)⟩).imp' (.pi fun g ↦ · ∘ₗ .pi (θ _ ∘L pairWeil S T α β ⟨g, ·⟩)) fun _ h _ ⟨_,
  _, b⟩ ↦ funext (DFunLike.congr_fun h ⟨_, .of_bound (by fun_prop) _ <| .of_forall <| b _ _ ·⟩)

instance : Nontrivial (LocProd 𝔠.S) := Pi.nontrivial_at 𝔠.nonempty.coe_sort.some

variable {S} {T} {α : AutChar E} {β : AutChar E} {f : 𝒮 (S.hom T)} {g : Gf E n} {h : Gf E n'}

lemma ReadsAt.pairWeil_localDatum_of_mem_Kf (hφ : φ ∈ schwartzBruhat U) (hg : g ∈ _root_.Kf ..)
  (hh : h ∈ _root_.Kf ..) : pairWeil S T α β (g, h) (localDatum S T v φ r) = (α.1 (detFin s' h) *
  (β.1 (detFin s g))⁻¹).1 • localDatum S T v (φ <| h⁻¹.1.1.map π * · * g.1.1.map π) r := by simp_all
  [pairWeil_name_of_mem r.1 (hΨ := r.isSchwartzBruhat hφ), pairWeil_eq_smul_of_projOn_eq ⊤]

lemma thetaIntegral_pairWeil p g : thetaIntegral S T α β (pairWeil S T α β p f) g =
  thetaIntegral S T α β f (g * p.1) :=
  by simpa [lift] using! ((pairThetaKer ..).swap.lift_equivariant (isAutomorphic_const _ 1) ..).symm

lemma IsTargetBounded.isAutFunction_thetaIntegral : IsTargetBounded S T f → _root_.IsAutFunction S
  (thetaIntegral S T α β f) | ⟨_, C, h⟩ => ⟨isCoherentWith.continuous_iff.2 fun _ a ↦
  continuousOn_of_dominated (by fun_prop) (fun _ _ ↦ .of_forall fun _ ↦ by grw [h,
  (exists_mul_height_pow_le a _).choose_spec _ 1] <;> simp [*]) (by simp) (.of_forall
  (by fun_prop)), by simp_all [thetaIntegral, pairTheta, (pairThetaKer ..).theta_rat_mul]⟩

lemma ReadsAt.isTargetBounded [Nontrivial F] (hv : IsRapidDatum v) (hφ :
  φ ∈ schwartzBruhat (HasLeftInv ·ᵀ)) : IsTargetBounded S T (localDatum S T v φ r) :=
  (pairTheta_decay_of_onto S T 1 1 π r.1 (r.isSchwartzBruhat hφ) (fun _ ↦ @hφ.2.2 _) 0).imp
  fun _ ⟨_, _, h⟩ ↦ ⟨_, by simpa [pairWeil, pairTheta, hv _] using h v⟩
