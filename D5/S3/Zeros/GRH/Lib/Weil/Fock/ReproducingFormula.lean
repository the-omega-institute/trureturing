/- GID: D5/S3/Zeros/GRH/Lib/Weil/Fock/ReproducingFormula
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Fock/ReproducingFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Fock.ReproducingFormula. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Fock/ReproducingFormula.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cohomology.Etale.TestRings
import D5.S3.Zeros.GRH.Lib.GaloisRep.EvenRank.ThetaLift
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: the basis problem in the stable range, as a reproducing formula. In this unitary
version at a fixed level, pairing with a holomorphic discrete series coefficient is a fixed finite
combination of values of theta lifts to a large definite group. This is deduced from injectivity by
linear duality. Source: S. Böcherer, Über die Fourier-Jacobi-Entwicklung Siegelscher
Eisensteinreihen, Math. Z. 183 (1983); J.-S. Li, Crelle 428 (1992).

Part of: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known result;
see Lib.Weil.Fock.OscillatorPair).

Part of: Harmonic highest vectors for (U(p,q), U(n)) give holomorphic vectors (known result; see
Lib.Weil.Lift.Staircase).

This file: Reproducing formula by theta lifts to large definite groups; holomorphic determinant
vectors. -/


open MeasureTheory Set Matrix MvPolynomial Finset Submodule NumberField Sum Sgn Heisenberg.IsVacuum
  Fintype ComplexConjugate Space Function Complex
variable {n n'} [Fintype n] [Fintype n'] {s O} (ho :
  @IsPosFirstOrder n s O) {E} [Field E] [CMType E] {p q} [Fintype.{0} p] [Fintype q] {s' : n' → _}
attribute [local simp] Matrix.map AlgHom.map_det vacuumWeight pairSign realConv pairHom pairHomInf
  letterMinor

lemma linSubst_letterMinor {i} {c : p → n} {κ} (hi : ∀ a, s' (i a) = κ) (hc : c.Injective) (h : ∀ k,
  s k = κ ↔ k ∈ range c) (u : GInf E s) τ : linSubst (complexLinearPart (pairHomInf (s' :=
  s') (u⁻¹, 1))) (letterMinor τ i c) = principalMinor (u τ) (s · = κ) • letterMinor τ i c := by
  rw [letterMinor, ← det_transpose, AlgHom.map_det, ← C_mul', principalMinor, ← det_reindex_self
    (.trans (.subtypeEquivRight h) (.symm (.ofInjective c hc))), C.map_det, ← det_mul]
  congr with; simp [complexLinearPart, linSubst, posProj, blockDiagonal_apply, (h _).2,
    @Matrix.mul_apply p, sum_prod_type, mul_eq_one_iff_eq_inv']
  rw [sum_of_injective c] <;> aesop

lemma realInner_realPairWeil_eq_holMinorsPi (s : n → _) (s' : n' → _) P (hP :
  P ∈ supported ℂ {p | realSigns E (homSigns s s') p = 1}) {ν c : _ → ℕ} γ e (h : ∀ u : GInf E s,
  linSubst (complexLinearPart (pairHomInf (s' := s') (u⁻¹, 1))) P =
  (∏ w, principalMinor (u w) (s · = 1) ^ ν w * principalMinor (u w) (s · = -1) ^ c w) • P) u :
  let v w i := ite (s i = 1) (-ν w : ℤ) ↑(card n' - negCount s') - c w - e w
  let k w i : ℤ := ite (s i = 1) (-(c w + negCount s')) 0
  let C u y := realInner P (realPairWeil (s' := s') γ e (u, y) P)
  C u 1 = C 1 1 * holMinorsPi s v u * conj (holMinorsPi s k u) := by
  simp [holMinorsPi, ite_sub, negCount, ← card_subtype_compl, realPairWeil]
  rw [← fockMatrixCoeff, fockMatrixCoeff_eq_realInner (d := const _ 0),
    ← congrArg (linSubst _) ((inv_smul_eq_iff₀ _).2 (h u⁻¹))]
  any_goals grind [_root_.pderiv_comm,
    pderiv_eq_zero_of_notMem_vars ∘ Set.notMem_subset (MvPolynomial.mem_supported.1 hP)]
  all_goals simp [← linSubst_mul, ← U.principalMinor_coe_inv, ← inv_eq_conj, holMinors_ite_sign,
    one_kronecker, jacobi_complementary_minor, ← fun w ↦ prod_fiberwise' s' fun σ ↦
    principalMinor (u w) (σ * s · = 1) / (u w).1.1.det, zpow_add₀, field,
    zpow_sub₀, div_pow, prod_ne_zero_iff, neg_eq_iff_eq_neg]

/-- For signature (p,q) and a definite second space of rank n′, the product over places of the
d-th power of a p×p minor in the positive columns is nonzero, and its Fock vector is
holomorphic of weight −d on positive, n′ on negative indices. -/
lemma prod_letterMinor_mem_holomorphicData {O} (ho : @IsPosFirstOrder (p ⊕ q) (1 ⊕ᵥ -1) O) (i :
  p ↪ n') d γ : let Q := ∏ w, ∏ _ : Fin d, letterMinor w i inl
  Q ≠ 0 ∧ polyVector _ Q ∈ holomorphicData (E := E) (1 ⊕ᵥ -1) 1 O (fun _ ↦ -d ⊕ᵥ card n') γ 0 := by
  apply prod_mem_holomorphicData ho (by tauto) fun w ↦
    IsLayering.joint_highest_prod_det (l := 0) ⟨const _ i.2, ?_, ?_, by tauto⟩
    ⟨const (Fin d) inl_injective, ?_, ?_, ?_⟩ rfl <;> simp [filter_eq']

lemma realPairWeil_mem_span_pairedDetProd i {Y : Matrix n' n' E} (hY : IsUnit Y) d γ y :
  realPairWeil (s := 1 ⊕ᵥ -1) (s' := 1) γ 0 (1, y) (polyVector _ (∏ w, ∏ _ : Fin d,
  letterMinor w i (@inl p q))) ∈ span ℂ (.range fun I : _ → Fin d → _ ↦
  polyVector _ (pairedDetProd (X ⟨·, ·, inl ·⟩) fun w k ↦ (Y.map (Φ w)).submatrix (I w k) id)) := by
  choose M e using fun w ↦ (hY.map (Φ w).mapMatrix).unit.mulRight.surjective (y w).1.1ᵀ
  rw [realPairWeil_polyVector]; simp_rw [map_prod]; rw [prod_congr _ _ fun w ↦
    prod_congr _ _ fun _ ↦ .trans ?_ ((detRowAlternating.restrictScalars ℂ).map_sum fun a c ↦
    M w (i a) c • fun b ↦ ∑ k, C (Φ w (Y c k)) * X (w, k, inl b))]
  simp_rw [MultilinearMap.map_smul_univ, Fintype.prod_sum, prod_smul]
  aesop (add safe sum_mem)
  simp [← ext_iff, mul_apply] at *; congr with
  all_goals simp [← e, sum_smul, mul_smul, C_mul', smul_sum] <;> rw [sum_comm]

include ho

/-- Let the orders o, O be those of an injective parameter l, and κ have no column longer than
the number of signs c. The highest vector of weight κ, in the letters of sign c, is a
nonzero polynomial, holomorphic of weight `staircaseWeight`.

Known result: Harmonic highest vectors for (U(p,q), U(n)) give holomorphic vectors. -/
lemma letterPoly_highestVector_holomorphic {o} {l : n → ℤ} (hl : ∀ a b, s a = s b → O a < O b →
  l a < l b) (hi : (-l).Injective) (hO : ∀ a, o a = #{b | s b = s a ∧ s a * l a < s a * l b}) c {κ γ
  w} (hκ : ∀ τ i, card {a // s a = c} < i → κ τ i = 0) : let Q := letterPoly s o c κ (highestVector
    κ fun _ ↦ (equivFin n' ·)); Q ≠ 0 ∧ polyVector _ Q ∈ holomorphicData (E := E) s 1 O (fun τ ↦
    staircaseWeight n' s o (Pi.single c (κ τ)) (-w τ)) γ w := by
  apply prod_mem_holomorphicData ho (fun _ ↦ hl) (fun τ ↦ staircase_harmonic_highest (l' :=
    (c * equivFin n' ·)) hi ?_ hO _ (by aesop) ?_ (by tauto)) <;> fin_cases c <;> simp [letterPoly,
    highestVector, weylKernel, highestPoly, tableauPoly, minor, _root_.permArray, fockLetters,
    ite_and, sum_filter, rowSubst, apply_ite, Fin.val_inj, decrPosition, Injective]

/-- Reproducing formula. Let 2n < n′, 𝔪 = (N) ≠ (1), c, b unramified, Q₀ ≠ 0 holomorphic of
dominant weight u, m = `holMinorsPi` s u integrable, Q spanning the U(n′)(ℝ)-translates of Q₀
at each class. For each x, ψ ↦ ∫ψ(xh)m(h)dh on rapid level-N ψ combines the pairings with
θ^{S,I_{n′}}_{c,b}[1_e,Q] linearly.

Known result: Basis problem in the stable range, as a reproducing formula. -/
lemma reproducing_formula_modKernel [WeilData E] {𝔪 N} [Fact (N ≠ 0)] (hN : 𝔪.ideal =
  .span {N}) (h𝔪 : Nonempty 𝔪.places) (S : Space E n s) {c b γ' γ u} (hc : c.HasWeight γ' 1) (hb :
  b.HasWeight γ 1) (hd : ∀ w, IsKDominant s O (u w)) (hi : Integrable (holMinorsPi s u)) (hn : 2 *
  card n < card n') (e : n ↪ n') {Q₀} (hQ : Q₀ ≠ 0 ∧ polyVector _ Q₀ ∈ holomorphicData s 1 O u γ' γ)
  {ι} [Fintype ι] (Q : StdClasses (principalLevel _ N) → ι → _) (hs : ∀ p y, realPairWeil (s :=
  s) (s' := 1) γ' 0 (1, y) (polyVector _ Q₀) ∈ span ℂ (.range (polyVector _ <| Q p ·))) x :
  ∃ a : _ × ι → ℂ, ∀ ψ ∈ rapidOfLevel S N, ∫ h, ψ (x * (h, 1)) * holMinorsPi s u h = ∑ i, a i * ∫ g,
  ψ g * modKernelI S c b 𝔪 (Pi.single (inclMatrix _ e) 1) (Q i.1 i.2) g i.1.out ∂S.quotMeasure := by
  let T := stdSpace E n'
  refine ((mem_span_range_iff_exists_fun _).1 (mem_span_of_iInf_ker_le_ker (L := fun i ↦ .proj
    (1, i.1.out) ∘ₗ (pairThetaKer S T ..).liftBilin _ ∘ₗ inclusion (p := rapidOfLevel S N)
    inf_le_left) (K := ⟨⟨(realConv (holMinorsPi s u) ·.1 x), ?_⟩, ?_⟩) fun ψ hψ ↦ ?_)).imp fun a e ψ
    l ↦ by simpa [mul_comm (ψ _)] using! congr($e.symm ⟨ψ, l⟩)
  on_goal 3 => have' := congrFun (realConv_eq_zero_of_lift_eq_zero
    (isSharp_modDatum T b _ (inclMatrix _ e)ᵀ ..) _
    (forall_mem_image.2 (congrFun <| ψ.2.2 ⟨·, (𝔪.mem_principalLevel_iff hN _).2 ·⟩)) ψ.2.1 _ (by
    ext y; choose p g w _ using
      exists_eq_map_mul_rep_mul T.embFin (principalLevel _ N) (·.out_eq) y.2
    rw [show y = T.ratEmbed g * ↑p.out * ↑w * ((T.ratEmbed g⁻¹ * y).1, 1) by aesop, lift_mul_right,
      lift_mul_right, ThetaKernel.fixesLeft_lift _ _ ⟨g, rfl⟩, pairWeil_integrated_right c,
      (by simpa [hc.apply_det_eq_one w.2.1, modDatum, (𝔪.mem_principalLevel_iff hN _).1] using
      (pairWeil_modDatum_Kf S T c b 𝔪 1 ⟨_, w.2.1⟩) :)]
    exact mem_span.1 (hs p _) (.proj _ ∘ₗ (pairThetaKer ..).liftBilin.flip _ ∘ₗ
      ((integrated _).flip _).1).ker (by aesop)) γ' _) x; revert this
  all_goals simp [*, (hQ.2 (realInner Q₀)).eq_holMinorsPi_mul ho hd (by
    rw [conj_modelInner, ← modelInner_weilRep (realAction _) <| pairHomInf ⟨·, 1⟩]
    simp [realPairWeil, rep_apply_apply, ← map_mul, inv_eq_conj]), hi.mul_const, mul_assoc, mul_add,
    eq_zero_of_modelInner_self.mt, mul_left_comm (holMinorsPi ..), integral_add,
    fun ψ : rapidOfLevel S N ↦
    IsBoundedMeasurable.integrable_mul_comp (.of ψ.2.1.2.bounded ψ.2.1.1.1) hi (x * ⟨·, 1⟩)]
