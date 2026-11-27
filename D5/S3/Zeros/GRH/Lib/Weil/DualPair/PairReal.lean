/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/PairReal
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/PairReal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.PairReal. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/PairReal.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.MixedModel.NameModulus
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.Petersson
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.PairSplitting
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

Part of: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known result;
see Lib.Weil.Fock.OscillatorPair).

This file: Real dual pair on Fock space; maximal compact subgroups act by substitution and
character. -/

noncomputable section


section

variable (E : Type) [Field E] [NumberField E] {n n' : Type} [Fintype n] [Fintype n'] (s : n → ℤˣ)
  (s' : n' → ℤˣ) (γ γ' : _ → ℤ) {x : GInf E s} {y : GInf E s'}
open Matrix Kronecker Fintype Finset Space MvPolynomial Heisenberg.IsVacuum AutChar

/-- The Fock space for the signs s′_i s_j of Hom(S,T), repeated at every infinite place. -/
abbrev PairFock := fockSpace (realSigns E (homSigns s s'))

variable {E s s'}

/-- The homomorphism sending real points (x, y) to the action z ↦ y_w z x_w⁻¹ on matrices at
each infinite place w, as one block diagonal unitary matrix. -/
def pairHomInf := blockU.comp (.pi fun w ↦ (pairHom ..).comp ((Pi.evalMonoidHom _ w).prodMap
  (Pi.evalMonoidHom _ w)) : GInf .. × GInf .. →* GInf E (homSigns s s'))

/-- The real Weil representation of the pair with weights γ, γ′: (x, y) acts by ∏_w (det
y_w)^{γ_w} (det x_w)^{−γ′_w} times the Fock operator of z ↦ y z x⁻¹. -/
@[simps! -isSimp apply_apply] def realPairWeil := (⟨⟨fun p ↦ (∏ w, (p.2 w).1.1.det ^ γ w *
  (p.1 w).1.1.det ^ (-γ' w)) • realWeil (pairHomInf p), by simp⟩, by
  simp_intro .. [mul_zpow]; module⟩ : _ →* PairFock E s s' →L[ℂ] PairFock ..)

@[fun_prop] lemma continuous_realPairWeil : Continuous fun q : _ × PairFock E s s' ↦
  realPairWeil γ γ' q.1 q.2 := by
  have : Continuous (@pairHomInf E _ _ _ _ _ _ s
    s') := by simp [continuous_U_iff_matrix, pairHomInf]; fun_prop [kroneckerMap]
  simp [-prod_mul_distrib, realPairWeil]; fun_prop (disch := simp)

attribute [simp] principalMinor_of_forall principalMinor_of_forall_not

lemma det_eq_prod_principalMinor {u : USign s} (h : ↑u ∈ blockDiagAlg s) : u.1.1.det = ∏ σ,
  principalMinor u (s · = σ) := by
  simpa using! BlockTriangular.det_fintype (mem_blockDiagAlg.1 h · · ·.ne')

/-- For x, y block diagonal for signs s, s′ of signatures (p,q), (p′,q′): Ω(x,y)v_P = ∏_w (det
y⁺)^{γ−q}(det y⁻)^{γ−p}(det x⁺)^{q′−γ′}(det x⁻)^{p′−γ′} v_Q, Q from P by X_{ab} ↦ ∑
y_{ia}(x⁻¹)_{bj}X_{ij} if s′_a = s_b, else ∑ (y⁻¹)_{ai}x_{jb}X_{ij}. -/
lemma realPairWeil_polyVector (hx : ∀ w, ↑(x w) ∈ blockDiagAlg s) (hy : ∀ w,
  ↑(y w) ∈ blockDiagAlg s') P : realPairWeil γ γ' (x, y) (polyVector _ P) =
  (∏ w, ∏ σ ∈ {1, -1}, principalMinor (y w) (s' · = σ) ^ (γ w - Nat.card {i //
  s i = -σ}) * principalMinor (x w) (s · = σ) ^ (Nat.card {i // s' i = -σ} - γ' w)) •
  polyVector _ (aeval (fun c ↦ ∑ i, ∑ j, ite (s' c.2.1 = s c.2.2) ((y c.1).1.1 i c.2.1 *
  (x c.1)⁻¹.1.1 c.2.2 j) ((y c.1)⁻¹.1.1 c.2.1 i * (x c.1).1.1 j c.2.2) • X (c.1, i, j)) P) := by
  have e := maxCompactU.coe_inv ⟨pairHomInf (x, y), ?_⟩
  erw [_root_.smul_apply, weilRep_eq_integral, ← integrated_vacElem (polyVector _ (aeval _ P)),
    smul_smul, congr(_ * $(realMultiplier_blockU _)), ← prod_mul_distrib]
  congrm (∏ w, ?_) • ∫ _, ?_ • _ ∂_
  rw [realMultiplier, ← U.principalMinor_coe_inv,
    ← div_eq_of_eq_mul _ (principalMinor_mul (b := y w ⊗ₖ 1) _)]
  pick_goal 4
  simp [realVac, star_mulVec_dotProduct, *]
  simp [← e]; convert! (eval₂Hom_bind₁ ..).symm
  nth_rw 1 [holCoord_eq, e]; norm_cast
  repeat simp [← map_inv, principalMinor_kronecker_one, one_kronecker, pairHom, blockDiagonal_apply,
    sum_prod_type, holCoord_eq, ← fun w ↦ prod_fiberwise' s fun c ↦
    principalMinor (y w) (s' · * c = -1), mul_zpow, zpow_sub₀, pairHomInf, pairSign, ← fun w ↦
    prod_fiberwise' s' fun c ↦ principalMinor (x w) (c * s · = -1), det_eq_prod_principalMinor, *,
    entrywise, mem_blockDiagAlg, mem_maxCompactU, mul_eq_one_iff_eq_inv,
    apply_ite] <;> (try split) <;> grind [mul_eq_zero, mem_blockDiagAlg, → blockDiagAlg.inv_mem]

end

open Matrix Kronecker Fintype Finset Space MvPolynomial Heisenberg.IsVacuum AutChar

variable {E : Type} [Field E] [CMType E] {n n' : Type} [Fintype n] [Fintype n'] {s : n → ℤˣ}
  {s' : n' → ℤˣ} {γ γ' : _ → ℤ} {x : GInf E s} {y : GInf E s'} [WeilData E] (S : Space E n s)
  (T : Space E n' s') (a b : AutChar E) {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}
  {ψ' : (w : FinPlace E) → MulChar (ResField w) ℂ}

/-- The theta kernel of the pair S, T with characters a, b: the representation ω_{a,b} on
𝒮(Hom(S,T)) and the theta functional of Hom(S,T), as a `ThetaKernel`. -/
@[simps] abbrev pairThetaKer : ThetaKernel (𝒮 (S.hom T)) S T :=
  ⟨pairWeil S T a b, θ _, by fun_prop, by simp_all [← Prod.mk_mul_mk, pairWeil_of_mem_Gamma]⟩

attribute [local simp] pairWeil omega_integrated G.onHom_eq realPairWeil HasWeight.apply_eq
  pairHomInf MonoidHom.pi

/-- If a has weight γ and b has weight γ' (with tame parts ψ, ψ'), then for real points x, y,
ω_{a,b}(x,y)(v⊗f) = (Ω(x,y)v)⊗f, where Ω is the real Weil representation of the pair for the
weights γ, γ'. -/
lemma pairWeil_integrated [HasWeight a γ ψ] [HasWeight b γ' ψ'] x y v f :
  pairWeil S T a b ((x, 1), y, 1) (integrated _ v f) =
  integrated _ (realPairWeil γ γ' (x, y) v) f := by simp [← Submonoid.one_def]

@[simp] lemma pairWeil_integrated_fin k k' v f : pairWeil S T a b ((1, k), 1, k') (integrated _ v
  f) = integrated _ v (pairWeil S T a b ((1, k), 1, k') f) := by simp [← Pi.one_def]

variable {S T}

lemma pairWeil_integrated_right {f} [ha : HasWeight a γ ψ] h v : pairWeil S T a b (1, h, 1)
  (integrated _ v f) = integrated _ (realPairWeil γ 0 (1, h) v) f := by simp [← Submonoid.one_def]

lemma pairWeil_integrated_all {a b} [HasWeight a γ ψ] [HasWeight b γ' ψ'] x k y k' v f :
  pairWeil S T a b ((x, k), y, k')
  (integrated _ v f) = integrated _ (realPairWeil γ γ' (x, y) v) (pairWeil S T a b (k, k') f) := by
  rw [← pairWeil_integrated_fin, ← pairWeil_integrated S T a b, rep_apply_apply]; simp
