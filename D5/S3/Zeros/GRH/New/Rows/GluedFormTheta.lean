/- GID: D5/S3/Zeros/GRH/New/Rows/GluedFormTheta
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/GluedFormTheta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.GluedFormTheta. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/GluedFormTheta.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Curve.KatzDivisibility
import D5.S3.Zeros.GRH.New.Columns.SizeEstimates
import D5.S3.Zeros.GRH.New.Rows.MemberKernels
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Some jet is no more divisible than predicted. For orders near the weights w, every prime p and
every p-adic embedding, some jet on a fixed number of copies, divided by one non-zero number with
small conjugates that serves all p, is no more divisible by p than the prime weight predicts, and
this upper bound on valuations is needed to divide out the Hecke values. Sharpness for one curve
(slope p/(p^2-1), attained in infinitely many degrees) is known. Related work: Bannai–Kobayashi,
Algebraic theta functions and Eisenstein–Kronecker numbers (arXiv v1, Thm 4.1), 2006;
Bannai–Kobayashi–Yasuda, Radius of convergence of the p-adic sigma function, 2017;
Schneider–Teitelbaum, p-adic Fourier theory, 2001; Bannai–Kobayashi, Integral structures on p-adic
Fourier theory, 2016.

Part of: Integral comparison forms seeing the twist through one number (see
New.Rows.ComparisonForms).

This file: Some jet with indicator datum is no more divisible than predicted, at every prime. Glued
lattices at the level primes and the product forms from which
the comparison forms are built. Theta descent of the
comparison forms is an average of products of two kernels. -/
seal Finset.univ Finset.sum Finset.prod

open Finset _root_.Nat CMLattice ComplexConjugate Fintype IsUltrametricDist Matrix Modulus
  MvPowerSeries PadicInt Parameters Real Sum

/-- Let w(σ) ≤ m_σ ≤ w(σ) + x^42. Some t ≠ 0, with conjugates at most exp(fmb/k), works for all
moduli (ϖ) and ι: ℂ → ℂ_p: some indicator datum on Hom(I_1, I_12) has a scaled Taylor coefficient a
of degrees m_σ with |ι(κ₀^12·∏m_σ!·a/t)| ≥ p^{−F(p)}. Here w = `Data.nominalWeight`, F =
`Data.forcedPart`, κ₀ = `Parameters.vacuumScale`, ϖ = `Data.piGBar`; x, f, m, b, k are the data's.

Some jet is no more divisible than predicted. -/
lemma Data.depth_indicator_jet {P} (D : Data P) (m : _ → ℕ) (hm : ∀ σ, D.nominalWeight σ ≤ m σ ∧
  m σ ≤ D.nominalWeight σ + D.x ^ 42) : ∃ t ≠ 0, (∀ σ : ℂ ≃+* ℂ, ‖σ t‖ ≤ exp (D.f * D.m / D.k *
  D.b)) ∧ ∀ 𝔪, 𝔪.ideal = .span {D.piGBar} → ∀ p [Fact p.Prime] [PadicPlace p], ∃ α x₀,
  (∀ σ, ∑ i, α (σ, i, ()) = m σ) ∧ p ^ (-D.forcedPart p) ≤ ‖ιₚ (P.vacuumScale D.s ^ 12 / t * (∏ σ,
  (m σ)!) * coeff α (Space.jetSeries _ (conj ↑D.piG * P.jetScale D.s)
  (modDatum (stdSpace _ _) (stdSpace _ (Fin 12)) 𝔪 (Pi.single x₀ 1) vacVector)))‖ := by
  let V := (stdSpace D.E Unit).hom (stdSpace _ (Fin 12))
  obtain ⟨g0, y, t0⟩ := NeZero.ne D.gProd, exists_intVacuum_ne_zero (V := V)
  let Q := D.gProd ^ (2 * (D.f * 12)) * ∏ σ, D.depthLossInt (m σ)
  have Q0 : Q ≠ 0 := by unfold Q depthLossInt; positivity
  refine ⟨Q * _, by positivity, fun σ ↦ by
    grw [(P.exists_algEquiv_norm_eq σ).choose_spec, map_mul, norm_mul, norm_intVacuum_le,
      ← exp_nat_mul, ((le_add_of_nonneg_right (by positivity)).trans (add_assoc ..).ge : _ ≤ P.c)]
    simp [Q, depthLossInt]; grw [ascFactorial_le_pow_add, tsub_le_self, le_floor (hm _).2,
      nominalWeight_add_le, floor_le_ceil, le_exp_log (_ ^ _ * _), ← exp_add]
    simpa using D.le_of_hasLogBound, fun 𝔪 hS p o _ ↦ ?_⟩
  obtain ⟨a, rfl⟩ : ∃ a : _ × _ →₀ _, (a ⟨·, ()⟩) = m := ⟨Finsupp.equivFunOnFinite.2 (m ·.1), rfl⟩
  obtain ⟨q, hp1, J, _, w, c, hw, hc, i, h⟩ := o.1.pos, o.1.one_lt, @exists_isTightFrame P D.s p _ _
    D.gProd (a.degree * 3)
    (by rify [Finsupp.degree_eq_sum]; grw [(hm _).2, nominalWeight_add_le]; simpa using
    D.le_of_hasLogBound)
  set S := P.periodFactor _
  let μ i := fun (x, ()) ↦ ιₚ (S * conj (Φ x (w i)))
  let Θ := ∏ i, (taylorVia ιₚ P.cmCurve.θ).subst (linearSeries (μ i)) ^ c i
  choose e he hN' using exists_monomial_max_norm_coeff (P.cmCurve.multiPhiRing μ) rfl Θ
  let Φ α :=
    (∏ i, (taylorVia ιₚ P.cmCurve.translatedWpDeriv).subst (linearSeries (μ i)) ^ e α i) * Θ
  let N α := ‖coeff α (Φ α)‖₊
  have hΘ H h : IsCarriedBy N 1 (H * Θ) := (⟨![·], by simpa using! hN' _ _ h⟩)
  have r : IsCarriedBy N 5 Θ⁻¹
  obtain ⟨⟨_, _, H⟩, j, hj⟩ := P.cmCurve.exists_log_theta, isClosed_property denseRange_natCast
    (isCompact_range (f := (∑ b, · b ^ 2)) (by fun_prop)).isClosed (·.sum_four_squares.elim
    fun a ⟨b, c, d, e⟩ ↦ ⟨![(a : ℤ_[p]), b, c, d], by simp [← e]⟩) (-1 + -1)
  have r b {k H} (h : IsCarriedBy N k H) := h.mul (H' := Θ.rescale fun _ ↦ (j b).1 • 1)
    (hΘ 1 (by simp) · |>.mono (by simp; grw [norm_le_one]; simp))
  have ⟨u, v, k⟩ := P.cmCurve.isSeriesGenerator_translatedWpDeriv.exists_mul_eq_one (SetLike.coe_mem
    (∏ b, ⟨_, (H.2.2.2.2.2 ((j b).1 • 1, (j
    b).1 ^ 2 • 1) (denseRange_natCast.induction_on (j b) (isClosed_closure.preimage (by fun_prop))
    (subset_closure ⟨·, by simp [sq, Algebra.smul_def]⟩))).2.1⟩)) (by simp [*])
  convert r 3 (r 2
    (r 1 (r 0 (hΘ _ (SetLike.coe_mem (∏ i, ⟨_, subst_mem_multiPhiRing _ v i⟩ ^ c i))))))
  refine .mp ?_ congr(∏ i, PowerSeries.substAlgHom (a := linearSeries (μ i)) (by simp) $k ^ c i)
  simp [*, Θ, MvPowerSeries.inv_eq_iff_mul_eq_one, expSubst_add, rescale_subst, add_smul,
    ← sum_smul, mul_pow, ← expSubst_sum, by simpa using congr(($hj).1)]; ring
  have h6 := by simpa [mul_assoc, Θ] using (hΘ · · |>.mul r)
  choose f k l using katz_divisibility_limit P.cmCurve
  have hC a := by simpa [norm_natCast_eq_inv_pow_padicValNat, ← rpow_natCast, ← rpow_mul, q,
    ← rpow_sum_of_pos] using ((h6 _ (subst_mem_multiPhiRing _ (k _) i) a).mono
    (by simp [μ, -map_mul, h]; grw [← norm_mul, ← l]) :)
  obtain ⟨α, hα, H⟩ : HasLargeSplit N 12 a (p ^ (-D.forcedPart p - ∑ x,
    ↑(padicValNat p (D.depthLossInt (a x))) + ∑ x, ↑(padicValNat p (a x)!)))
  · by_cases l : chiK P.d p = 1
    · convert ((hC a).mul (hC 0)).mono _ <;> simp [forcedPart, localAsk, nonsplitWeight, *,
        Finset.sum_nonneg]
    have k i := (coprime_primes o.1 (D.g_prime i)).2 (l <|
      chiK_eq_one_of_modEq_one <| · ▸ D.g_modEq_one _)
    obtain ⟨s1, i, y, A, h4⟩ := (@norm_iota_periodFactor_eq_one P D.s p _ · (l ∘ chiK_eq_one_of_dvd
      _ o.1)), D.exists_isFrobPacking hm o.1 l
    obtain ⟨b, e, τ, t, u, z, G⟩ := exists_hasLargeSplit_of_pairs l A (by simpa using hΘ 1)
      (by simp [Θ]) r ⟨_, _, _, _, 1, S, 0, hw.repeat_vectors, by
      simpa [Θ, μ, S, *, prod_prod_type, Fintype.prod_sigma] using .mul_right (k 0) (k 1)⟩
    obtain ⟨⟨a, rfl⟩, ⟨h, rfl, h4⟩ | h4⟩ := exists_add_of_le e, h4
    obtain ⟨F, H⟩ : ∃ F : P.cmCurve.multiPhiRing μ,
      IsLowestTerm 1 F a (ιₚ (conj S * S * D.gProd) ^ a.degree) := a.toMultiset_toFinsupp ▸
      a.toMultiset.induction_on ⟨1, by simp [IsLowestTerm]⟩ fun (x, _) _ ⟨F, v⟩ ↦ by
      simp_rw [← Multiset.singleton_add, map_add, pow_add]
      refine ⟨⟨_, ∑ i, .C (c i * ⟨_, norm_periodFactor_mul_conj_le_one (ι :=
        ⟨ιₚ.comp conj⟩) (hw.1 i) x⟩) * .X i, RingHom.comp_apply ..⟩ * F, .mul (fun d hd ↦ ?_) v⟩
      simp [Finsupp.weight_apply, le_succ_iff, Finsupp.sum_eq_one_iff, map_mul, -map_natCast,
        ↓substAlgHom_X, coeff_monomial, mul_assoc, @eq_comm _ d] at hd ⊢
      obtain rfl | ⟨y, _, ⟨⟩⟩ := hd.imp_left d.degree_eq_zero_iff.1 <;> simp [Finsupp.single_apply]
      simpa [μ, mul_sum, mul_assoc, mul_left_comm (ιₚ S), apply_ite ιₚ, cast_comm,
        apply_ite factorial, Finsupp.single_left_inj] using congr(ιₚ (conj S * S * $(hw.2 _ y)))
    apply (G.mul (h6 _ F.2 _)).mono
    simp [H a, gProd, (k _).norm_natCast_eq_one, show ‖ιₚ (conj _)‖ = 1 from s1 ⟨.comp ..⟩, *, S,
      nonsplitWeight, sq,
      ← sum_mul, sum_prod_type, field, mul_self_sub_one, ← cast_sum] at h4 ⊢; linarith
    apply (G.mul (hC a)).mono
    have v {x n} (h : n ≤ (b + a) x) := @padicValNat_factorial_mem_Icc p _ n (D.b₂ * 2) (by
      grw [h, pow_mul, ← Nat.lt_pow_self hp1, ← @cast_le ℝ, (hm _).2]
      use D.le_of_hasLogBound)
    grw [(v le_rfl).2, ← (v le_add_self).1, ← (v (t _)).1] <;> simp [← rpow_add, ← cast_sum, ← z,
      hp1, q, ← mul_sum, div_eq_inv_mul, Finsupp.degree_eq_sum, sum_prod_type] at h4 ⊢ <;> linarith
  let γ := Finsupp.equivFunOnFinite.2 fun (s, i, ()) ↦ α i (s, ())
  set L := V.jetSeries _
  have he b i : e (α b) i * 3 ≤ c i
  grw [Finsupp.le_degree, he, ← hc, ← hα, map_sum, ← single_le_sum] <;> simp
  obtain ⟨F, -, hF, hA, K, u, k, hx, hK, hs⟩ := exists_finitePart_of_isTightFrame V D.piG g0
    (by simpa [gProd] using congr($(D.norm_piG).val.1)) hw (fun (i, b, _) ↦ (_, 0, e (α b) i))
    (Nat.sub_add_cancel <| he _ ·.1) omega₀_mem_cmCurve_lattice
    (by simp [QuadField.area_eq_of_eq_scaledIdeal latticeModule_cmCurve])
  obtain ⟨x, -, E⟩ := (by simpa only [(exists_heis_vacElem_eq_sum_modDatum _ _ hS (hx
    _)).choose_spec, sum_smul, map_sum, V, map_smul, map_mul, mul_sum, ← sum_product',
    Space.rho_finVec, LinearMap.comp_apply, ← coeff_map, smul_eq_mul] using congr(ιₚ (V.θ (V.ϱ
    (finVec y) $(hs (coeff γ ∘ₗ L))))) : _) ▸ exists_norm_finsetSum_le ..
  use γ, x.2, by simp [γ, ← hα]
  rw [(by simpa using (hF 0).2 :), show _ * _ = S by simp [jetScale, field], (?_ : MvPowerSeries.map
    ιₚ _ = ∏ b, rename (·.1, b, ()) (Φ (α b))), (?_ : coeff _ _ = ∏ b, coeff _ (Φ (α b)))] at E
  simp [Q, N, intVacuum, prod_prod_type, rpow_add, rpow_sub, q, rpow_sum_of_pos,
    prod_eq_zero_iff] at Q0 E H t0 ⊢
  grw [hA, norm_natCast_le_one, ← H] at E
  simp [field, *, norm_natCast_eq_inv_pow_padicValNat] at E ⊢; linarith
  simp [coeff_prod, coeff_rename, prod_univ_sum]
  rw [sum_comm' (t' := {α}) (s' := fun β ↦ {∑ b, .single b ((β b).mapDomain (·.1, b, ()))})] <;>
    simp [Finsupp.ext_iff, ite_and, Finsupp.mapDomain, Finsupp.sum_fintype, Finsupp.single_apply,
      sum_prod_type, @eq_comm _ (ite ..)]
  clear * -; aesop
  simp (disch := fun_prop) [Φ, Θ, taylorAtZero_congr _ (monomialSection_eq _ _), taylorVia]
  simp [μ, rename_eq_subst, subst_comp_subst_apply, he, subst_mul, PowerSeries.subst, map_subst,
    subst_pow, ← prod_mul_distrib, prod_prod_type_right, PowerSeries.map]
  simp [← rename_eq_subst, linearSeries, sum_prod_type, mul_comm (_ ^ c _), smul_eq_C_mul]

/-- A point γ of G_f supported on the chosen places M and their conjugates, with ϖγ⁻¹ integral,
where ϖ = `AuxPair.genIdele` is the idele generating M. -/
structure DividedLattice {E r n} [Field E] [CMType E] [Fintype r] [Fintype n] (O :
  AuxPair E r n) where
  γ : Gf E n
  mem_supportedOn : γ ∈ Gf.supportedOn n (Set.range O.chosenPlace)
  integral a b : O.genIdele * γ⁻¹.1.1 a b ∈ Ô E

variable {E r n N m a} [Field E] [CMType E] [Fintype r] [Fintype n] [Fintype N] [Fintype m] [Fintype
  a] [WeilData E] {O : AuxPair E r n} {z} (V : DividedSplitting N m a O z) (s :
  Matrix a N O.chosenModulusSq.ResRing) (L : DividedLattice O)

/-- The reduction of the integral matrix ϖγ⁻¹ modulo M², the square of the product of the chosen
places. -/
noncomputable def DividedLattice.reducedInverse := of fun a b ↦
  O.chosenModulusSq.reduction ⟨_, L.integral a b⟩

/-- The number χ(δ)|δ|^(−r/2), with δ the idele equal to det γ at the chosen places and 1
elsewhere, r the rank of W, χ = `AutChar.spaceChar` of O.a and r. -/
noncomputable def DividedLattice.weilScalar : ℂ := let δ := detOn (Set.range O.chosenPlace) L.γ.1
                      (O.a.spaceChar (Fintype.card r)).1 δ / √(ideleAbs δ) ^ Fintype.card r

section

omit [WeilData E]

/-- If j ∈ K₀ is 1 modulo M², then γ⁻¹jγ lies in K₀ and reduces to 1 at every chosen place. -/
lemma DividedLattice.reduceAt_conj_eq_one j (t : O.chosenModulusSq.reductionK₀ j = 1) : ∃ h, ∀ i,
  Kf.reduceAt (O.chosenPlace i) ⟨L.γ⁻¹ * j.1 * L.γ,
  h⟩ = 1 := have F k (h : O.chosenModulusSq.reductionK₀ k = 1) c d :=
    reduction_levelModulus_eq_zero_iff.1 ((Kf.map_eq_one n).1 h c d)
  have H c d : star O.genIdele⁻¹.1 * (O.genIdele⁻¹ ^ 2 * (j.1.1.1 - 1) c d) ∈ _ :=
    mem_Ô.2 fun w ↦ by
    obtain _ := U.inv_val_eq_conjTranspose j.1,
      star_mem_Ô (mul_mem O.genIntAdele.2 (F j⁻¹ (by simp [t]) d c)), F j t c d
    obtain _ | _ := imp_iff_not_or.1 (@Set.disjoint_left.1 O.chosenModulusSq.disjoint_places_star
      w) <;> simp_all [-F, mem_Ô, places_levelModulus_false, genIdele_apply_of_notMem, sq,
      mul_assoc, v_inv, apply_ite star, @eq_comm n]
  have G a b : O.genIdele⁻¹ * ((L.γ⁻¹ * j * L.γ).1.1 - 1) a b ∈ Ô E := by
    rw [(by simp [mul_sub, sub_mul] : _ - 1 = L.γ⁻¹.1.1 * (j.1.1.1 - 1) * L.γ.1.1)]
    simpa [mul_apply, sum_mul, mul_sum, sq, mul_assoc, mul_left_comm, ← Units.coe_star,
      -Units.coe_star_inv] using sum_mem fun d _ ↦ sum_mem fun c _ ↦ mul_mem (mul_mem
      (L.integral a c) (H c d)) (star_mem_Ô (U.inv_val_eq_conjTranspose L.γ ▸ L.integral b d :))
  ⟨mem_Kf.2 (by simpa [sub_eq_add_neg, add_mem_cancel_right,
    ite_mem] using mul_mem O.genIntAdele.2 <| G · ·), fun i ↦ (Kf.map_eq_one _).2 fun a b ↦ by
    simp [← modulusResidue_reduction (O.levelModulus 1 _) (places_levelModulus_false.ge ⟨i, rfl⟩),
      reduction_levelModulus_eq_zero_iff.2, by simpa using G]⟩

/-- If C and G are matrices over Ô with CG = ϖ·1, then some L has ϖγ⁻¹ ≡ G modulo M². -/
lemma DividedLattice.exists_reducedInverse_eq (C G : Matrix n n (Ô E)) (h : C * G = O.genIntAdele •
  1) : ∃ L : DividedLattice O, L.reducedInverse = G.map O.chosenModulusSq.reduction := by
  let c := cutGL (idem_mul_self O.chosenModulusSq.places)
    ⟨C.map (Ô E).subtype, O.genIdele⁻¹.1 • G.map (Ô E).subtype, ?e, mul_eq_one_comm.1 ?e⟩
  case e => ext; simp [← Matrix.map_mul, h, apply_ite, -Subring.coe_subtype]
  have e := idem_mul_star O.chosenModulusSq.disjoint_places_star
  have k : Commute (star c) c := Units.ext (by
    simp [c, cutGL, mul_add, add_mul, smul_smul, e, mul_comm]; ac_rfl)
  refine ⟨⟨⟨star c⁻¹ * c, Units.val_inj.2 (by simp [k.inv_right.eq] : star (_ * c) * 1 * _ = 1)⟩,
    by simp +contextual [Gf.atPlace, c, map_evalAt_cutGL, Units.ext_iff,
    evalAt_star_GL (star_star _), places_levelModulus_false], fun a b ↦ ?_⟩, Matrix.ext fun a b ↦
    reduction_congr _ fun w m ↦ ?_⟩ <;> simp (maxDischargeDepth := 5) [c, cutGL, mul_add, add_mul,
    e, mul_left_comm O.genIdele.1, ← mul_assoc (star _), mul_comm (star _),
    star_mem_Ô, O.genIntAdele.2, add_mem, mul_mem, sub_mem, ite_mem]
  split <;> simp [idem_apply] <;> grind [disjoint_places_star]

/-- For an a×N matrix s over O_E/M², the matrix obtained by stacking s over ϖ·1_N, where ϖ is
the class of the generator `AuxPair.genIdele` of M. -/
noncomputable def DividedSplitting.stackOverGenScalar :=
  s.fromRows (V.genResidue • 1 : Matrix N N _)

omit [Fintype a] in
/-- The level `rowFixingLevel`, formed from the rows of s stacked on ϖ·1 and the columns
`V.fixedEmb`, lies in the principal level at the places of M: its elements are integral and reduce
to 1 at each such place. -/
lemma rowFixingLevel_le_levelOf : rowFixingLevel _ (V.stackOverGenScalar s) V.fixedEmb ≤
  levelOf O.chosenPlace ⊥ := fun _ ⟨k, a, b⟩ ↦ ⟨k, funext fun l ↦
  Units.ext ((reductionK₀_map_modulusResidue ..).symm.trans ((V.genResidue_smul_eq_iff _ id).1
  (by simpa [DividedSplitting.stackOverGenScalar, inclMatrix] using congrArg toRows₂ a.2) l)), b⟩

/-- The subgroup of GL_r(O_E/M²) of matrices that are 1 modulo M, defined as the stabiliser of the
scalar matrix ϖ·1 (`DividedSplitting.genResidue`) under multiplication. -/
noncomputable def DividedSplitting.congruenceGroup := MulAction.stabilizer
  (GL r O.chosenModulusSq.ResRing) (V.genResidue • 1 : Matrix r r O.chosenModulusSq.ResRing)

omit [Fintype a] in
lemma DividedSplitting.reduceAt_liftMod_congruenceGroup (Y : V.congruenceGroup) i : Kf.reduceAt
  (O.placeAt (inl i)) (liftMod Y.1) = 1 := Units.ext ((reductionK₀_map_modulusResidue ..).symm.trans
  ((V.genResidue_smul_eq_iff ..).1 (by simpa using! show _ * _ = _ from Y.2) i))

/-- L is glued for s: the indicator of Gx = ϖ·inc is the sum over Y ≡ 1 (ϖ) of the indicators of
block conditions on xY, and some invertible K makes ϖG″K vanish off the columns `V.dividedEmb`. -/
structure DividedSplitting.IsGlued where
  indicator_eq_sum (x : Matrix n r O.chosenModulusSq.ResRing) (c : ℂ) : ite (L.reducedInverse * x =
    V.genResidue • inclMatrix _ O.incl) c 0 = ∑ Y : V.congruenceGroup, ite
    ((x * Y.1.1).submatrix (V.ε ∘ inr) id = inclMatrix _ z ∧ V.stackOverGenScalar s *
    (x * Y.1.1).submatrix (V.ε ∘ inl) id = V.stackOverGenScalar s * inclMatrix _ V.fixedEmb) c 0
  exists_cols_eq_zero : ∃ K : GL N O.chosenModulusSq.ResRing, ∀ x, ∀ y ∉ univ.map V.dividedEmb,
    V.genResidue * (L.reducedInverse.submatrix id (V.ε ∘ inl) * K.1) x y = 0

/-- The linear map sending η to the point form (`pointForm`) of the product y·η (`cartanProduct`) at
diag(h₁, h₂)·γ_L, with columns `O.incl` at M and rows ε ∘ inl ∘ `V.fixedEmb` at Q. -/
noncomputable def DividedSplitting.productForm h (y : WeylIndex N O.colsPlus → ℂ) :=
  pointForm (U.block V.ε h * L.γ) (fun _ ↦ inclMatrix_mulVecLin_injective O.incl _)
  (V.fixedEmb.trans (.trans .inl V.toEmbedding)) ∘ₗ cartanProduct V.ε 1 y

omit [Fintype a] in
lemma DividedSplitting.exists_congruenceGroup_inv_eq_one_sub {Y} (h : V.genResidue • Y = 0) : ∃ A :
    V.congruenceGroup, A⁻¹.1.1 = 1 - Y := (IsNilpotent.isUnit_one_sub ⟨2,
  by choose X e using (reduction_surjective _ <| Y · ·)
     simp_all [-e, ← e, ↓← ext_iff, mul_apply, sq, ← map_mul, ↓reduction_levelModulus_eq_zero_iff,
       mul_mul_mul_comm, mul_mem,
       Finset.sum_eq_zero]⟩).elim (⟨⟨·, show _ * _ = _ by simp [*, smul_sub]⟩⁻¹, ·⟩)

/-- For every matrix s modulo M² there is a lattice L glued for s (`DividedSplitting.IsGlued`). -/
lemma DividedSplitting.exists_isGlued : ∃ L, V.IsGlued s L := by
  choose t hs using (reduction_surjective _ <| s · ·)
  obtain ⟨U, -, D, -, P, Q⟩ :=
    isValuationPair_Ohat.top.hermite .inr ((of t).fromRows (O.genIntAdele • 1))
  obtain ⟨L, e⟩ := DividedLattice.exists_reducedInverse_eq (O := O) ((fromBlocks U.1.toBlocks₂₂
    (inclMatrix (Ô E) V.fixedEmb * (inclMatrix (Ô E) z)ᵀ) 0 (.diagonal (if · ∈ Set.range z then 1
    else O.genIntAdele))).reindex V.ε V.ε) ((fromBlocks D (-D.submatrix id V.fixedEmb *
    (inclMatrix (Ô E) z)ᵀ) 0 (.diagonal (if · ∈ Set.range z then O.genIntAdele else 1))).reindex
    V.ε V.ε) (by simp +contextual [← mul_inclMatrix, ← U.1.toBlocks₂₂.mul_assoc,
                   inclMatrix_transpose_mul, Matrix.mul_assoc
                   _ _ᵀ, show U.1.toBlocks₂₂ * D = O.genIntAdele • 1 from congr(toRows₂ $P).symm]
                 simp [entrywise, reindex_equiv V.ε, inclMatrix, diagonal_apply, mul_sum])
  apply_fun (·.map O.chosenModulusSq.reduction) at P Q
  simp [map_smul', (Matrix.ext hs : (of t).map O.chosenModulusSq.reduction = s)] at P Q
  refine ⟨L, fun x c ↦ .trans ?_ (Finset.sum_congr rfl fun Y _ ↦ if_congr (P := x.submatrix O.incl
    id = Y⁻¹.1 ∧ L.reducedInverse * x = V.genResidue • inclMatrix _ O.incl) ?_ rfl rfl),
    ((isValuationPair_resRing _).exists_mul_clear_cols s V.dividedEmb).imp fun K h ↦ ?_⟩
  · split_ifs with h <;> simp [h]
    have ⟨Y, f⟩ := V.exists_congruenceGroup_inv_eq_one_sub (Y := 1 - x.submatrix O.incl id)
      (Matrix.ext (by simpa [e, ← V.ε_ι, apply_ite, mul_apply, inclMatrix, diagonal_apply,
      mul_sub, reindex_equiv V.ε] using congrFun₂ h.symm <| O.incl ·))
    simp at f; rw [← f]; norm_cast; simp
  · erw [show ∀ X Y : Matrix N r O.chosenModulusSq.ResRing, V.stackOverGenScalar s * X =
      V.stackOverGenScalar s * Y ↔ D.map O.chosenModulusSq.reduction * X =
      D.map O.chosenModulusSq.reduction * Y by grind [Matrix.mul_assoc, stackOverGenScalar],
      ← Units.mul_eq_one_iff_eq_inv, ← inclMatrix_transpose_mul, ←
      mul_left_inj_of_invertible (m := n) Y.1, smul_mul, ← Matrix.mul_smul,
      (mul_smul_one ..).symm.trans Y.2, Matrix.mul_assoc, L.reducedInverse.mul_assoc]
    generalize x * Y.1.1 = X
    simp +contextual [e, entrywise, reindex_equiv V.ε, ← V.ε_ι, inclMatrix,
      apply_ite O.chosenModulusSq.reduction, diagonal_apply, iff_def, sum_mul, sum_comm]
    grind
  simp [e, ← submatrix_map, reindex_equiv V.ε, mul_apply, -map_apply]
  simp +contextual [↓← mul_apply (M := D.map _), ← Q, Matrix.mul_assoc, h, mul_sum, ← map_mul, sq,
    mul_apply (N := fromRows _ _), mul_left_comm V.genResidue, reduction_levelModulus_eq_zero_iff.2,
    mul_assoc, ← mul_assoc V.genResidue]

end

attribute [-simp] coe_units_inv Set.Sum.elim_range Sum.elim_inl Sum.elim_inr

variable {L : DividedLattice O} {s : Matrix a N O.chosenModulusSq.ResRing} {b b'} (H :
  V.IsGlued s L) (hb : b * b' = O.b)

omit [Fintype a] in
/-- The theta lift of the point form of v at hγ is conj(β_L·K), β_L = `DividedLattice.weilScalar`,
K the kernel at h
with polynomial P_v̄ and datum ∏_Q ψ(det S_e) where GS = ϖ·inc mod ϖ², else 0; G =
`DividedLattice.reducedInverse`. -/
lemma DividedSplitting.theta_pointForm e v g h :
  O.θ (pointForm (h * L.γ) (fun _ ↦ inclMatrix_mulVecLin_injective O.incl _) e v) g = conj
  (L.weilScalar * modKernelI O.W O.a O.b (O.levelModulus 2) (fun S ↦
  ite (L.reducedInverse * S.map reduceToR₀ = V.genResidue • inclMatrix _ O.incl) (∏ i, O.ψ _
  ((S.map (levelResidueAt (inr i))).submatrix e id).det) 0) (O.harmonicPoly (star v)) g h) := by
  erw [_root_.theta_pointForm, ← mul_one g, ← Prod.one_mk_mul_one_mk, modKernel, ← Prod.mk_mul_mk,
    pairTheta_mul,
    pairWeil_integrated_fin, pairWeil_name_on (disjoint_places_star _), (_ : detOn _ _ = _)]
  simp [pairTheta, ← V.genResidue_smul_eq_iff, DividedLattice.weilScalar]; congr with y
  simp [liftFn_apply, vecToMat, ← ext_iff, mul_apply, DividedLattice.reducedInverse, ← map_mul,
    ← map_sum, Matrix.map]
  split <;> rename_i h
  · rw [dite_eq_left]; congr! 8
    · ext; simp [matToVec, mul_apply, mul_sum]; ring
    · congrm ⟦⟨_ * ?_, _⟩⟧
      set_option synthInstance.maxHeartbeats 200000 in
      simpa using! congr($(Matrix.map_mul.trans congr($(atPlace_twistPlace_eq_one
        (inv_mem L.mem_supportedOn) _).1 * _)) _ _)
    simp [idem_mul_mem_Ô]; exact fun a b w
      m ↦ by simpa [mul_assoc, mul_left_comm, ← mul_sum, matToVec, ← mul_apply, ← Matrix.mul_assoc,
      m, genIdele_apply_of_notMem fun ⟨i, e⟩ ↦ (disjoint_places_star _).le_bot ⟨m,
      places_levelModulus.ge ⟨inl i, e⟩⟩] using mem_Ô.1 (sum_mem (t := univ) fun c _ ↦
      mul_mem (star_mem_Ô (U.inv_val_eq_conjTranspose L.γ ▸ L.integral c a :)) (h c b)) w
  split_ifs with _ H; absurd h; peel H
  simpa [matToVec, mul_assoc, mul_apply, mul_sum, mul_left_comm, inclMatrix, sq,
    reduction_levelModulus_eq_zero_iff.2, ← map_mul,
    reduction_levelModulus_eq_zero_iff, ← map_sum] using congr(V.genResidue * $this)
  all_goals have := L.mem_supportedOn; aesop (add simp [places_levelModulus,
    atPlace_twistPlace_eq_one, Set.Sum.elim_range])

include H hb

/-- For L glued for s and bb′ = O.b, the theta lift of the form of y·η at (h, h′) is the
conjugate of β_L·S, with S the sum, over Y ≡ 1 mod ϖ, of the Y-translates of a product of
kernels on V″ (for y) and V° (for η). -/
lemma DividedSplitting.theta_productForm h h' y η g : O.θ (V.productForm L (h, h') y η) g = conj
  (L.weilScalar * ∑ Y : V.congruenceGroup, let g := g * (liftMod Y.1).1
  modKernelI O.W O.a b _ (columnDatum (charOfTamePart _ O.ψ) reduceToR₀ (V.stackOverGenScalar s)
    V.fixedEmb) (letterPoly O.signs O.ord 1 _ (star y)) g h *
  modKernelI O.W O.a b' O.chosenModulusSq (Pi.single (inclMatrix _ z) 1)
    (letterPoly O.signs O.ord (-1) _ (star η)) g h') := by
  erw [V.theta_pointForm]
  simp_rw [modKernel, ← modDatum_factor levelModulus_ideal_le, ← modKernel.eq_1, ← modKernelI_block
    V.ε, hb, modKernel_mul_Kf_left, ← modKernelBilin_apply, ← LinearMap.sum_apply, ← map_sum]
  congr; ext
  simp [← ite_and, ← submatrix_map, columnDatum, reduceAt_liftMod_congruenceGroup,
    H.indicator_eq_sum, O.hasWeight.hasWeight_rankTwist.apply_det_eq_prod O.apart.1 O.tame_eq_one]
  congr!
  simp [finprod_eq_prod_of_fintype, RingHom.map_det, ← submatrix_map, -Matrix.map_mul,
    show charOfTamePart _ _ _ = ∏ᶠ j, O.ψ _ (levelResidueAt j _) from (finprod_comp_equiv
    (.trans (.ofInjective _ O.apart.1) (Set.equivOfEq places_levelModulus.symm))).symm]
  rw [@Finset.prod_eq_one O.ChosenIndex]; simp [Kf.reduceAt_eq_one_of_atPlace (w :=
    O.placeAt (inr _)) (atPlace_twistPlace_eq_one (liftMod_mem_supportedOn _) _)]; rfl
  intros; rw [← Function.id_comp id, ← submatrix_submatrix, submatrix_map,
    (V.genResidue_smul_eq_iff _ V.fixedEmb).1
    (by simp_all [stackOverGenScalar, ← submatrix_map, fromRows_ext_iff])]; simp [inclMatrix]
  simp [show star _ = _ from map_cartanProduct V.low.1 V.low.2 _ _ _ conj, V.low, HasColumnsBelow,
    AuxPair.harmonicPoly, mixedCartan_mulVec_cartanProduct, letterPoly,
    rowSubst, fockLetters, inclMatrix, MvPolynomial.rename_bind₁, MvPolynomial.bind₁_bind₁]; rfl

/-- If `DividedSplitting.IsGlued` s L and bb′ = O.b, the theta lift at g of ∑_h
`DividedSplitting.productForm`(h, h′)(conj(c·y(h)), η), class sum at level `rowFixingLevel`, is
conj(β_L c)·∑_Y conj(`cosetKernelSum`(y)·θ^{W,V°}[1_{inc z}, η̄](·, h′)) at gỸ, over Y ∈ GL_r(O/M²),
Y ≡ 1 mod M, Ỹ lifts. -/
lemma DividedSplitting.theta_stdClassSum_productForm h' c y η g : O.θ (stdClassSum (rowFixingLevel _
  (V.stackOverGenScalar s) V.fixedEmb) fun h ↦ V.productForm L (h, h') (star (c • y h)) η) g = conj
  (L.weilScalar * c) * ∑ Y : V.congruenceGroup, let g := g * (liftMod Y.1).1
  conj (cosetKernelSum O b (V.stackOverGenScalar s) V.fixedEmb y g * modKernelI O.W O.a b'
    O.chosenModulusSq (Pi.single (inclMatrix _ z) 1) (letterPoly O.signs O.ord (-1) _ (star η)) g
    h') := show (.proj g ∘ₗ O.θ) _ = _ by simp [cosetKernelSum, map_classSum, ← classSum_sum,
  mul_classSum, ↓V.theta_productForm H hb, ← modKernelBilin_apply, mul_sum, mul_assoc]
