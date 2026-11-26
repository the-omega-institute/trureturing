import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.AdeleSelfDual
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: self-duality of a number field in its adeles, strong approximation, and the
Poisson inequality. The file treats totally complex fields, for which the field is its own
annihilator and the pairing is non-degenerate. Strong approximation omitting a nonempty set of
finite places is deduced from duality, and Poisson summation is an inequality for nonnegative lower
semicontinuous functions. Source: J. Tate, Fourier analysis in number fields and Hecke's
zeta-functions, thesis 1950, in Cassels-Fröhlich ch. XV, Theorem 4.1.4; for strong approximation,
Cassels, ch. II §15. -/

open MeasureTheory Measure Complex QuotientAddGroup NumberField Finset Circle

/-- One-sided Poisson summation on the adeles of E: let F ≥ 0 be integrable and lower
semicontinuous at the points of a finite set T ⊂ E. If S bounds all finite sums of |∫
ψ(−ξx)F(x) dx| over ξ in E, then ∑_{t∈T} F(t) ≤ S. -/
lemma IsDualFamily.sum_le_of_fourier {E} [Field E] [NumberField E] [IsTotallyComplex E]
  [PlaceEmbedding E] {S} {F : 𝔸 E → ℝ} (hF : Integrable F) (h₀ : 0 ≤ F) (T : Finset (ratAdeles E))
  (hT : ∀ t ∈ T, LowerSemicontinuousAt F t) (hS : ∀ Y, ∑ i ∈ Y, ‖∫ x, stdAddChar E (toAdele
  i * -x) * ofReal (F x)‖ ≤ S) : ∑ t ∈ T, F t ≤ S := le_of_forall_lt_imp_le_of_dense fun m _ ↦ by
  choose f _ fc f₀ hf _ using exists_continuousMap_one_of_isCompact_subset_isOpen
    isCompact_singleton (isOpenMap_coe _ isOpen_setOfPred_eventually_nhds) (forall_eq.2 ⟨0,
    lowerSemicontinuousAt_sum (a := T) (add_zero ·.1 ▸ hT _ · |>.comp (by fun_prop)) m (by simpa),
    mk_zero (ratAdeles E)⟩)
  refine have p : IsContPeriodic (ratAdeles E) (f ·) := ⟨by fun_prop, ?_⟩
    have J := f.2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := addHaarMeasure ⊤) (x := 0)
      fc hf ?_
    have := (average_quotMeasure_eq_quotMean _ volume p).symm
    have c Y := by
      grw [← hS, mul_sum]; gcongr; simp [quotMean, ← integral_const_mul, ← mul_assoc]
      rw [integral_integral_swap ((hF.comp_snd _).ofReal.bdd_mul (c := 1) ((isDualFamily_ratAdeles.1
        x).integrable_out.1.comp_fst.mul (by fun_prop)) ?_)]
      simp [↓integral_mul_const, AddChar.map_neg_eq_inv, mul_right_comm, by
        simpa [quotMean, ← eq_inv_mul_iff_mul_eq₀] using mul_quotMean_translate p x]
      grw [mul_comm, norm_integral_le_integral_norm]; simp_all [norm_coe, abs_of_nonneg]
    le_of_mul_le_mul_left (.trans ?_ (le_of_tendsto' (hasSum_re
      (isDualFamily_ratAdeles.fourier_inversion (F := fun z ↦ ∫ x, f (.mk'' (z + x)) * F x)
      ⟨continuous_of_dominated (by fun_prop) ?_ hF (.of_forall (by fun_prop)), ?_⟩
      (summable_of_sum_le ?_ c).of_norm (fun _ ↦ rfl) 0)) ((sum_le_sum ?_).trans ∘' c))) J <;>
    simp_all [quotMean, Pi.le_def, norm_coe, mul_le_of_le_one_left, abs_of_nonneg, ← eq_zero_iff,
    re_le_norm, ← ofReal_mul, integral_complex_ofReal, ← integral_mul_const, average_eq_integral]
  refine (measurePreserving_addOrbitMeasure.fubini (hF.bdd_mul (by fun_prop) (.of_forall
    (f.norm_coe_le_norm ·)))).elim fun I ↦ (integral_mono_ae (.mul_const (.of_integral_ne_zero
    J.ne') _) I.integral_prod_left (I.prod_right_ae.mono fun x h ↦ ?_)).trans_eq
  cases (hf x).eq_or_lt' <;> simp_all [-integral_const_mul, AddSubgroup.vadd_def, (eq_zero_iff _).2]
  choose u hu e using f₀ (subset_closure (ne_of_gt ‹_›))
  grw [hu.self_of_nhds]; simpa [add_assoc, mul_sum] using! sum_le_hasSum (T.map (addRightEmbedding
    ⟨_, eq_iff_sub_mem.1 e⟩)) (by aesop) (hasSum_integral_measure h)
