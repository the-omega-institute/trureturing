/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticChart
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreAnalyticChart
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSAnalyticFold, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFoldCurvature, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLocalization, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformZeroCorner]
   utility: none
   digest: Normalized coherence folds after straightening seven regular observations, and separated fold pairs yield generic recovery against all actual competitors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSAnalyticFold
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFoldCurvature
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreLocalization
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformZeroCorner

/-! Analytic fold coordinates for the literal two-site observations at the uniform
independent-set witness. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticChart

open PeriodicMPSUniformHardCoreFirstJet
open PeriodicMPSUniformHardCoreFoldCurvature
open PeriodicMPSUniformHardCoreTransferRecurrence (hardCoreChart)
open PeriodicMPSUniformHardCoreLocalization
open PeriodicMPSUniformHardCoreMarginalWitness (Pair)
open PeriodicMPSUniformHardCorePencilDecoder
  (ordinaryInvariants firstRoot firstRoot_base analyticAt_firstRoot eventually_firstRoot decodedPencil)
open PeriodicMPSUniformDeterminantPencil (witnessCore)
open PeriodicMPSProjectiveCoordinates (projector mass projector_scale)
open PeriodicMPSUniformZeroCorner (listTrace_eq_of_invariants)
open PeriodicMPSParentIntersection (Bond Word twoFlattening)
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open UniformMPSExpectedDimensionRefutation (traceWord)
open PeriodicMPSAnalyticFold (verticalDeriv)
open Set Filter Asymptotics
open scoped Topology

open private twoMass normalizedTwo from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFirstJet
open private exists_regularCoordinates_equiv coherence_derivative mass_pos_witness
  hasDerivAt_deriv_comp_of_stationary smooth_amplitude from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreFoldCurvature
open private deriv_slice analyticAt_verticalDeriv verticalDeriv_neg from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSAnalyticFold

open private traceWord_eq_listTrace from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformZeroCorner

noncomputable section

abbrev Regular := (Fin 4 → ℝ) × (Fin 3 → ℝ)

/-- The last coordinate is the imaginary part of the first chart parameter. -/
def straighten (r : ℕ) (x : Coord) : Regular × ℝ :=
  (regularReadout r x, (x 0).im)

def foldBase (r : ℕ) : Regular × ℝ := (regularReadout r witness, 0)

@[simp] theorem straighten_witness (r : ℕ) : straighten r witness = foldBase r := rfl

private theorem analyticAt_coreEntry (i j k : Fin 2) (x : Coord) :
    AnalyticAt ℝ (fun y : Coord => cores y i j k) x := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | exact analyticAt_const | exact (ContinuousLinearMap.proj _ : Coord →L[ℝ] ℂ).analyticAt x

private theorem analyticAt_wordEntry (w : List (Fin 2)) (i j : Fin 2) (x : Coord) :
    AnalyticAt ℝ (fun y : Coord => (w.map (cores y)).prod i j) x := by
  induction w generalizing i j with
  | nil => exact analyticAt_const
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    exact Finset.analyticAt_sum Finset.univ fun l _ => (analyticAt_coreEntry k i l x).mul (ih l j)

private theorem analyticAt_flattening (r : ℕ) (p : Pair) (w : Word (r + 2)) (x : Coord) :
    AnalyticAt ℝ (fun y : Coord => twoFlattening (cores y) r p w) x := by
  simp only [twoFlattening, traceWord, Matrix.trace, Matrix.diag, List.ofFn_comp']
  exact Finset.analyticAt_sum Finset.univ fun i _ => analyticAt_wordEntry _ i i x

private theorem analyticAt_rawTwo (r : ℕ) (p q : Pair) (x : Coord) :
    AnalyticAt ℝ (fun y : Coord => rawTwo (cores y) r p q) x := by
  simp only [rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.analyticAt_fun_sum
  intro w _
  exact (analyticAt_flattening r p w x).mul
    ((Complex.conjCLE.toContinuousLinearEquiv.analyticAt _).comp (analyticAt_flattening r q w x))

private theorem analyticAt_twoMass (r : ℕ) (x : Coord) :
    AnalyticAt ℝ (fun y : Coord => twoMass (cores y) r) x :=
  (Complex.reCLM.analyticAt _).comp (Finset.analyticAt_sum Finset.univ fun p _ => analyticAt_rawTwo r p p x)

theorem analyticAt_component (r : ℕ) (hr : 3 ≤ r) (imag : Bool) (i : Fin 8) :
    AnalyticAt ℝ (component imag r i) witness := by
  have h := ((analyticAt_twoMass r witness).inv (mass_pos_witness r hr).ne').smul
    (analyticAt_rawTwo r (entry i).1 (entry i).2 witness)
  cases imag
  · exact (Complex.reCLM.analyticAt _).comp h
  · exact (Complex.imCLM.analyticAt _).comp h

theorem analyticAt_straighten (r : ℕ) (hr : 3 ≤ r) :
    AnalyticAt ℝ (straighten r) witness := by
  have hR : AnalyticAt ℝ (regularReadout r) witness := by
    apply AnalyticAt.prod <;> apply AnalyticAt.pi <;> intro i <;> fin_cases i
    all_goals first | exact analyticAt_component r hr false _ | exact analyticAt_component r hr true _
  let π : Coord →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.proj 0)
  exact hR.prod (π.analyticAt witness)

/-- The derivative of the coordinate change sends the regular kernel tangent to
the unit vector in the last coordinate. -/
theorem exists_straighten_equiv (r : ℕ) (hr : 3 ≤ r) :
    ∃ L : Coord ≃L[ℝ] (Regular × ℝ),
      HasFDerivAt (straighten r) (L : Coord →L[ℝ] _) witness ∧
      L (nullDirection (r + 4)) = (0, 1) := by
  obtain ⟨L, hL, ht⟩ := exists_regularCoordinates_equiv r hr
  let P := ContinuousLinearEquiv.prodComm ℝ ℝ Regular
  exact ⟨L.trans P, P.hasFDerivAt.comp witness hL, by
    change P (L (nullDirection (r + 4))) = _
    rw [ht]
    rfl⟩

/-- The literal coherence in straightened coordinates. -/
def coherence (r : ℕ) (e : OpenPartialHomeomorph Coord (Regular × ℝ)) :
    Regular × ℝ → ℝ := component false r 3 ∘ e.symm

/-- The literal forbidden diagonal in straightened coordinates. -/
def forbidden (r : ℕ) (e : OpenPartialHomeomorph Coord (Regular × ℝ)) :
    Regular × ℝ → ℝ := component false r 6 ∘ e.symm

theorem exists_analytic_chart (r : ℕ) (hr : 3 ≤ r) :
    ∃ e : OpenPartialHomeomorph Coord (Regular × ℝ),
      (e : Coord → Regular × ℝ) = straighten r ∧ witness ∈ e.source ∧
      AnalyticAt ℝ e.symm (foldBase r) ∧
      AnalyticAt ℝ (coherence r e) (foldBase r) ∧
      AnalyticAt ℝ (forbidden r e) (foldBase r) ∧
      verticalDeriv (coherence r e) (foldBase r) = 0 ∧
      verticalDeriv (forbidden r e) (foldBase r) = 0 ∧
      verticalDeriv (verticalDeriv (coherence r e)) (foldBase r) < 0 ∧
      verticalDeriv (verticalDeriv (forbidden r e)) (foldBase r) = 0 := by
  obtain ⟨L, hL, hLnull⟩ := exists_straighten_equiv r hr
  have ha := analyticAt_straighten r hr
  have hs := ha.hasStrictFDerivAt
  rw [hL.fderiv] at hs
  let e := hs.toOpenPartialHomeomorph (straighten r)
  have he : (e : Coord → Regular × ℝ) = straighten r := rfl
  have hw : witness ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  have hT : foldBase r ∈ e.target := e.map_source hw
  have hiw : e.symm (foldBase r) = witness := e.left_inv hw
  have hi : AnalyticAt ℝ e.symm (foldBase r) := by
    exact e.analyticAt_symm' hw (by rwa [he]) (i := L) (by rw [he, hL.fderiv])
  have hh := (analyticAt_component r hr false 3).comp_of_eq hi hiw
  have hj := (analyticAt_component r hr false 6).comp_of_eq hi hiw
  let slice (t : ℝ) : Regular × ℝ := (regularReadout r witness, t)
  let γ := e.symm ∘ slice
  have hslice : AnalyticAt ℝ slice 0 := analyticAt_const.prod analyticAt_id
  have hγ : AnalyticAt ℝ γ 0 := hi.comp_of_eq hslice rfl
  have hγ0 : γ 0 = witness := hiw
  have hslice' : HasDerivAt slice (0, 1) 0 :=
    (hasDerivAt_const 0 (regularReadout r witness)).prodMk (hasDerivAt_id 0)
  have hInv : HasFDerivAt e.symm (L.symm : _ →L[ℝ] Coord) (foldBase r) :=
    hs.to_localInverse.hasFDerivAt
  have hγ' : HasDerivAt γ (nullDirection (r + 4)) 0 := by
    simpa only [← hLnull, ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] using
      hInv.comp_hasDerivAt 0 hslice'
  have hR : ∀ᶠ t in 𝓝 (0 : ℝ), regularReadout r (γ t) = regularReadout r witness := by
    filter_upwards [hslice.continuousAt (e.open_target.mem_nhds hT)] with t ht
    exact congrArg Prod.fst (e.right_inv ht)
  have hh' : HasDerivAt (component false r 3 ∘ γ) 0 0 := by
    have h := (coherence_derivative r hr).comp_hasDerivAt_of_eq 0 hγ' hγ0.symm
    have hk : fderiv ℝ (regularReadout r) witness (nullDirection (r + 4)) = 0 := by
      rw [fderiv_regularReadout_apply r hr, regularJet_nullDirection _ (by omega)]
    simpa [hk] using h
  have hj' : HasDerivAt (component false r 6 ∘ γ) 0 0 := by
    simpa using (forbidden_corner_hasFDerivAt r hr).comp_hasDerivAt_of_eq 0 hγ' hγ0.symm
  have hh2 := coherence_curvature_on_regular_level r hr γ hγ.contDiffAt hγ0 hγ' hR
  have hj2 := hasDerivAt_deriv_comp_of_stationary
    (analyticAt_component r hr false 6).contDiffAt (forbidden_corner_hasFDerivAt r hr)
    hγ.contDiffAt hγ0 hγ'
  have curvature {f : Regular × ℝ → ℝ} (hf : AnalyticAt ℝ f (foldBase r)) :
      deriv (deriv (f ∘ slice)) 0 = verticalDeriv (verticalDeriv f) (foldBase r) := by
    have hEq : deriv (f ∘ slice) =ᶠ[𝓝 (0 : ℝ)] verticalDeriv f ∘ slice := by
      filter_upwards [hslice.continuousAt hf.eventually_analyticAt] with t ht
      exact deriv_slice ht
    rw [hEq.deriv.eq_of_nhds]
    exact deriv_slice (analyticAt_verticalDeriv hf)
  have hj2zero := hj2.deriv.trans (forbidden_corner_hessian_zero r hr)
  refine ⟨e, he, hw, hi, hh, hj, ?_, ?_, ?_, ?_⟩
  · exact (deriv_slice hh).symm.trans hh'.deriv
  · exact (deriv_slice hj).symm.trans hj'.deriv
  · exact (curvature hh) ▸ hh2
  · exact (curvature hj) ▸ hj2zero

/-- The projected marginal has two analytic branches in straightened coordinates,
with its coherence sign reversed so the fold has a minimum. -/
theorem exists_coherence_fold (r : ℕ) (hr : 3 ≤ r) :
    ∃ e : OpenPartialHomeomorph Coord (Regular × ℝ),
      (e : Coord → Regular × ℝ) = straighten r ∧ witness ∈ e.source ∧
      ∃ C : PeriodicMPSAnalyticFold.FoldChart (-coherence r e) (foldBase r),
        C.U ×ˢ Icc C.left C.right ⊆ e.target ∧ Nonempty C.Branches := by
  obtain ⟨e, he, hw, _, hh, _, hh₁, _, hh₂, _⟩ := exists_analytic_chart r hr
  have hT : foldBase r ∈ e.target := by simpa [he] using e.map_source hw
  obtain ⟨C, hC⟩ := PeriodicMPSAnalyticFold.exists_foldChart_pos hh.neg
    (by rw [verticalDeriv_neg, Pi.neg_apply, hh₁, neg_zero])
    (by rw [verticalDeriv_neg, verticalDeriv_neg, Pi.neg_apply]; exact neg_pos.mpr hh₂)
    (e.open_target.mem_nhds hT)
  exact ⟨e, he, hw, C, hC, C.exists_branches⟩

/-- The two sheets of the projected marginal have different forbidden entries
arbitrarily close to the independent-set witness. -/
def HasSeparatedPairs (r : ℕ) : Prop :=
  ∀ U : Set Coord, U ∈ 𝓝 witness → ∃ x ∈ U, ∃ z ∈ U,
    (regularReadout r x, component false r 3 x) =
      (regularReadout r z, component false r 3 z) ∧
    component false r 6 x ≠ component false r 6 z

/-- A nonzero fourth-order coefficient of the difference of paired readout
germs supplies the separation hypothesis. The pair may lie over moving regular outputs. -/
theorem hasSeparatedPairs_of_quartic_limit {r : ℕ} {x z : ℝ → Coord} {k : ℝ}
    (hx : Tendsto x (𝓝[≠] (0 : ℝ)) (𝓝 witness))
    (hz : Tendsto z (𝓝[≠] (0 : ℝ)) (𝓝 witness))
    (hpair : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      (regularReadout r (x t), component false r 3 (x t)) =
        (regularReadout r (z t), component false r 3 (z t)))
    (hquartic : Tendsto (fun t => (component false r 6 (x t) -
      component false r 6 (z t)) / t ^ 4) (𝓝[≠] (0 : ℝ)) (𝓝 k))
    (hk : k ≠ 0) : HasSeparatedPairs r := by
  intro U hU
  have hn := hquartic (isOpen_compl_singleton.mem_nhds (show k ∈ ({0} : Set ℝ)ᶜ from hk))
  have hdiff : ∀ᶠ t in 𝓝[≠] (0 : ℝ), component false r 6 (x t) ≠ component false r 6 (z t) := by
    filter_upwards [hn] with t ht
    intro he
    apply ht
    simp [he]
  have hxU : ∀ᶠ t in 𝓝[≠] (0 : ℝ), x t ∈ U := hx hU
  have hzU : ∀ᶠ t in 𝓝[≠] (0 : ℝ), z t ∈ U := hz hU
  obtain ⟨t, ht₁, ht₂, ht₃, ht₄⟩ := (hxU.and (hzU.and (hpair.and hdiff))).exists
  exact ⟨x t, ht₁, z t, ht₂, ht₃, ht₄⟩

/-- The fourth-order expansion of the exact paired readouts can be supplied directly
with a little-o remainder. -/
theorem hasSeparatedPairs_of_quartic_expansion {r : ℕ} {x z : ℝ → Coord} {k : ℝ}
    (hx : Tendsto x (𝓝[≠] (0 : ℝ)) (𝓝 witness))
    (hz : Tendsto z (𝓝[≠] (0 : ℝ)) (𝓝 witness))
    (hpair : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      (regularReadout r (x t), component false r 3 (x t)) =
        (regularReadout r (z t), component false r 3 (z t)))
    (hquartic : (fun t => component false r 6 (x t) - component false r 6 (z t) - k * t ^ 4)
      =o[𝓝[≠] (0 : ℝ)] (fun t => t ^ 4))
    (hk : k ≠ 0) : HasSeparatedPairs r := by
  apply hasSeparatedPairs_of_quartic_limit hx hz hpair _ hk
  have h := hquartic.tendsto_div_nhds_zero.const_add k
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := {0}ᶜ)] with t ht
  have ht' : t ≠ 0 := ht
  field_simp [ht']
  ring

/-- The actual nine marginal readouts have singleton fibers on a relatively open dense
subset of a chart about the witness, with competitors ranging over the whole chart. -/
theorem exists_generic_chart_reconstruction (r : ℕ) (hr : 3 ≤ r)
    (hpair : HasSeparatedPairs r) {U : Set Coord} (hU : U ∈ 𝓝 witness) :
    ∃ S : Set Coord, IsOpen S ∧ witness ∈ S ∧ S ⊆ U ∧
      ∃ G : Set S, IsOpen G ∧ Dense G ∧
        ∀ x ∈ G, ∀ z : S, observation r z = observation r x → z = x := by
  obtain ⟨e, he, hw, hi, hh, hj, hh₁, _, hh₂, _⟩ := exists_analytic_chart r hr
  have htarget : foldBase r ∈ e.target := by simpa [he] using e.map_source hw
  have hinv : e.symm (foldBase r) = witness := by simpa [← straighten_witness, ← he] using e.left_inv hw
  have hiU : e.symm ⁻¹' U ∈ 𝓝 (foldBase r) :=
    (hi.continuousAt.tendsto.trans (le_of_eq (congrArg nhds hinv))) hU
  have hpair' (V : Set (Regular × ℝ)) (hV : V ∈ 𝓝 (foldBase r)) :
      ∃ y ∈ V, ∃ q ∈ V, (y.1, coherence r e y) = (q.1, coherence r e q) ∧
        forbidden r e y ≠ forbidden r e q := by
    have hpre : e ⁻¹' V ∈ 𝓝 witness := e.continuousAt hw (by simpa [he] using hV)
    obtain ⟨x, hx, z, hz, hobs, hne⟩ :=
      hpair _ (inter_mem (e.open_source.mem_nhds hw) hpre)
    refine ⟨e x, hx.2, e z, hz.2, ?_, ?_⟩
    · change ((e x).1, component false r 3 (e.symm (e x))) =
        ((e z).1, component false r 3 (e.symm (e z)))
      rw [e.left_inv hx.1, e.left_inv hz.1, he]
      exact hobs
    · simpa [forbidden, e.left_inv hx.1, e.left_inv hz.1] using hne
  obtain ⟨T, hTo, hTw, hT, G, hGo, hGd, hG⟩ :=
    PeriodicMPSAnalyticFold.exists_generic_singleton_fibers hh hj hh₁ hh₂.ne hpair'
      (inter_mem (e.open_target.mem_nhds htarget) hiU)
  have hsub : T ⊆ e.target := fun _ ht => (hT ht).1
  let S := e.symm '' T
  let H : T ≃ₜ S := e.symm.homeomorphOfImageSubsetSource hsub rfl
  refine ⟨S, e.symm.isOpen_image_of_subset_source hTo hsub,
    ⟨foldBase r, hTw, hinv⟩, ?_, H.symm ⁻¹' G, hGo.preimage H.symm.continuous,
    hGd.preimage H.symm.isOpenMap, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hT hy).2
  · intro x hx z hobs
    apply H.symm.injective
    apply hG (H.symm x) hx (H.symm z)
    have hread (y : T) :
        (y.val.1, coherence r e y, forbidden r e y) = observation r (H y).val := by
      have h := e.right_inv (hsub y.property)
      change (y.val.1, coherence r e y, forbidden r e y) = observation r (e.symm y)
      rw [he] at h
      exact Prod.ext (congrArg Prod.fst h).symm rfl
    rw [hread, hread, H.apply_symm_apply, H.apply_symm_apply, hobs]

private abbrev Ordinary := ℂ × ℂ × ℂ × ℂ

private def chartA (p : Ordinary) : ℂ := -firstRoot (1, p.2.1)
private def chartTrace (p : Ordinary) : ℂ := 1 + chartA p
private def chartD (p : Ordinary) : ℂ := chartTrace p * p.1
private def chartB (p : Ordinary) : ℂ := chartTrace p ^ 2 * p.2.2.2 - chartA p * chartD p

/-- Choose the chart representative of the four trace-normalized invariants. The
small determinant root supplies the first diagonal entry and the mixed trace fixes
the off-diagonal entry that is nonzero at the witness. -/
private def fromOrdinary (p : Ordinary) : Coord :=
  ![chartA p, chartB p, -(chartTrace p ^ 2 * p.2.2.1) / chartB p, chartD p]

private theorem ordinary_witness : ordinaryInvariants witnessCore = (0, 0, 0, 1) := by
  norm_num [ordinaryInvariants, witnessCore, Matrix.trace, Matrix.diag, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]

private theorem fromOrdinary_base : fromOrdinary (0, 0, 0, 1) = witness := by
  ext i
  fin_cases i <;> simp [fromOrdinary, chartD, chartB, chartTrace, chartA, witness]

private theorem continuousAt_fromOrdinary : ContinuousAt fromOrdinary (0, 0, 0, 1) := by
  have hp : ContinuousAt (fun p : Ordinary => ((1 : ℂ), p.2.1)) (0, 0, 0, 1) :=
    continuousAt_const.prodMk continuous_snd.fst.continuousAt
  have ha : ContinuousAt chartA (0, 0, 0, 1) :=
    (analyticAt_firstRoot.continuousAt.comp_of_eq hp rfl).neg
  have ht : ContinuousAt chartTrace (0, 0, 0, 1) := continuousAt_const.add ha
  have hd : ContinuousAt chartD (0, 0, 0, 1) := ht.mul continuous_fst.continuousAt
  have hb : ContinuousAt chartB (0, 0, 0, 1) :=
    ((ht.pow 2).mul continuous_snd.snd.snd.continuousAt).sub (ha.mul hd)
  have hb0 : chartB (0, 0, 0, 1) ≠ 0 := by simp [chartB, chartTrace, chartA, chartD]
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact (((ht.pow 2).mul continuous_snd.snd.fst.continuousAt).neg).div hb hb0
  · exact hd

private theorem eventually_chartTrace (p₀ : Ordinary) (hp₀ : p₀ = (0, 0, 0, 1)) :
    ∀ᶠ p in 𝓝 p₀, chartTrace p ≠ 0 ∧ chartB p ≠ 0 ∧ chartA p = p.2.1 * chartTrace p ^ 2 := by
  subst p₀
  have ha : ContinuousAt chartA (0, 0, 0, 1) :=
    (continuous_apply (0 : Fin 4)).continuousAt.comp continuousAt_fromOrdinary
  have ht : ContinuousAt chartTrace (0, 0, 0, 1) := continuousAt_const.add ha
  have hb : ContinuousAt chartB (0, 0, 0, 1) :=
    (continuous_apply (1 : Fin 4)).continuousAt.comp continuousAt_fromOrdinary
  have ht0 : chartTrace (0, 0, 0, 1) ≠ 0 := by simp [chartTrace, chartA]
  have hb0 : chartB (0, 0, 0, 1) ≠ 0 := by simp [chartB, chartTrace, chartA, chartD]
  have hd : ContinuousAt (fun p : Ordinary => ((1 : ℂ), p.2.1)) (0, 0, 0, 1) :=
    continuousAt_const.prodMk continuous_snd.fst.continuousAt
  filter_upwards [ht.eventually_ne ht0, hb.eventually_ne hb0, hd.eventually eventually_firstRoot]
    with p ht' hb' h
  refine ⟨ht', hb', ?_⟩
  simp [chartA, chartTrace, decodedPencil] at h ⊢
  linear_combination -h

private theorem traceWord_rescale (A : Fin 2 → Bond) (z : ℂ) (n : ℕ) :
    traceWord 2 2 n (fun i => z • A i) = z ^ n • traceWord 2 2 n A := by
  have h (w : List (Fin 2)) : (w.map fun i => z • A i).prod = z ^ w.length • (w.map A).prod := by
    induction w with
    | nil => simp
    | cons i w ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, ih, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, pow_succ]
  funext w
  rw [traceWord_eq_listTrace, Pi.smul_apply, traceWord_eq_listTrace]
  simp only [PeriodicMPSUniformZeroCorner.listTrace]
  rw [h, List.length_ofFn, Matrix.trace_smul, smul_eq_mul]

private theorem coreInvariants (p : Ordinary) :
    let B := cores (fromOrdinary p)
    (B 0).trace = chartTrace p ∧ (B 1).trace = chartD p ∧
    (B 0).det = chartA p ∧ (B 1).det =
      -(chartB p * (-(chartTrace p ^ 2 * p.2.2.1) / chartB p)) ∧
    (B 0 * B 1).trace = chartB p + chartA p * chartD p := by
  simp [cores, hardCoreChart, fromOrdinary, chartTrace, Matrix.trace, Matrix.diag,
    Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

private theorem traceWord_eq_scaled_chart (A : Fin 2 → Bond) (hA : (A 0).trace ≠ 0)
    {p : Ordinary} (hp : p = ordinaryInvariants A)
    (ht : chartTrace p ≠ 0) (hb : chartB p ≠ 0)
    (ha : chartA p = p.2.1 * chartTrace p ^ 2) (n : ℕ) :
    ∃ z : ℂ, z ≠ 0 ∧ traceWord 2 2 n A =
      z • traceWord 2 2 n (cores (fromOrdinary p)) := by
  let B := cores (fromOrdinary p)
  let t := chartTrace p
  let s := (A 0).trace / t
  let C i := s • B i
  have hCt : (C 0).trace = (A 0).trace := by
    change (s • B 0).trace = _
    rw [Matrix.trace_smul, (coreInvariants p).1, smul_eq_mul]
    exact div_mul_cancel₀ _ ht
  have hCs : (C 1).trace = (A 1).trace := by
    change (s • B 1).trace = _
    rw [Matrix.trace_smul, (coreInvariants p).2.1, smul_eq_mul]
    have hp' : p.1 = (A 1).trace / (A 0).trace := congrArg Prod.fst hp
    change ((A 0).trace / t) * (t * p.1) = _
    rw [hp']
    field_simp [show t ≠ 0 from ht]
  have hCd₀ : (C 0).det = (A 0).det := by
    change (s • B 0).det = _
    rw [Matrix.det_smul, Fintype.card_fin, (coreInvariants p).2.2.1, ha]
    dsimp [s, t]
    nth_rw 2 [hp]
    simp only [ordinaryInvariants]
    field_simp
  have hCd₁ : (C 1).det = (A 1).det := by
    change (s • B 1).det = _
    rw [Matrix.det_smul, Fintype.card_fin, (coreInvariants p).2.2.2.1]
    have hb' : -(chartB p * (-(t ^ 2 * p.2.2.1) / chartB p)) = t ^ 2 * p.2.2.1 := by
      field_simp
    rw [hb']
    have hp' : p.2.2.1 = (A 1).det / (A 0).trace ^ 2 := congrArg (fun q : Ordinary => q.2.2.1) hp
    rw [hp']
    dsimp [s]
    field_simp [show t ≠ 0 from ht]
  have hCm : (C 0 * C 1).trace = (A 0 * A 1).trace := by
    change ((s • B 0) * (s • B 1)).trace = _
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hBm : (B 0 * B 1).trace = chartB p + chartA p * chartD p := (coreInvariants p).2.2.2.2
    rw [hBm]
    have hB : chartB p + chartA p * chartD p = t ^ 2 * p.2.2.2 := by simp [chartB, t]
    have hp' : p.2.2.2 = (A 0 * A 1).trace / (A 0).trace ^ 2 :=
      congrArg (fun q : Ordinary => q.2.2.2) hp
    rw [hB, hp']
    dsimp [s]
    field_simp [show t ≠ 0 from ht]
  refine ⟨s ^ n, pow_ne_zero _ (div_ne_zero hA ht), ?_⟩
  rw [← traceWord_rescale B s n]
  funext w
  rw [traceWord_eq_listTrace, traceWord_eq_listTrace]
  exact listTrace_eq_of_invariants A C hCt.symm hCs.symm hCd₀.symm hCd₁.symm hCm.symm _

private def chartProjector (r : ℕ) (x : Coord) : StateMatrix (r + 2) :=
  projector (traceWord 2 2 (2 + (r + 2)) (cores x))

private theorem continuousAt_chartProjector (r : ℕ) (x : Coord)
    (hx : traceWord 2 2 (2 + (r + 2)) (cores x) ≠ 0) :
    ContinuousAt (chartProjector r) x := by
  have h (w : Word (2 + (r + 2))) :
      Continuous (fun y : Coord => traceWord 2 2 (2 + (r + 2)) (cores y) w) :=
    (smooth_amplitude 1 w).continuous
  have hm : Continuous (fun y : Coord => mass (traceWord 2 2 (2 + (r + 2)) (cores y))) :=
    continuous_finsetSum _ fun w _ => Complex.continuous_normSq.comp (h w)
  have hx' := PeriodicMPSProjectiveCoordinates.mass_pos _ hx
  apply continuousAt_pi.mpr
  intro u
  apply continuousAt_pi.mpr
  intro v
  exact (hm.continuousAt.inv₀ hx'.ne').smul
    ((h u).mul (Complex.conjCLE.continuous.comp (h v))).continuousAt

private theorem eventually_nonzero_traceWord (r : ℕ) (hr : 3 ≤ r) :
    ∀ᶠ x in 𝓝 witness, traceWord 2 2 (2 + (r + 2)) (cores x) ≠ 0 := by
  have hm := (analyticAt_twoMass r witness).continuousAt.eventually_ne (mass_pos_witness r hr).ne'
  filter_upwards [hm] with x hx hx0
  apply hx
  unfold twoMass
  rw [← PeriodicMPSUniformHardCoreMarginalWitness.pairGram_traceWord,
    ← PeriodicMPSUniformHardCoreMarginalWitness.mass_eq_trace, hx0]
  simp [PeriodicMPSUniformHardCoreMarginalWitness.mass]

private theorem exists_chart_localization (r : ℕ) (hr : 3 ≤ r)
    {U : Set Coord} (hU : U ∈ 𝓝 witness) :
    ∃ W : Set (Matrix Pair Pair ℂ), IsOpen W ∧
      normalizedMarginal (r + 2) witnessCore ∈ W ∧
      ∀ P ∈ actualProjectors (r + 2), twoSiteObservation (r + 2) P ∈ W →
        ∃ x ∈ U, chartProjector r x = P := by
  have hp : ContinuousAt fromOrdinary (ordinaryInvariants witnessCore) := by
    rw [ordinary_witness]
    exact continuousAt_fromOrdinary
  have hU' : ∀ᶠ p in 𝓝 (ordinaryInvariants witnessCore), fromOrdinary p ∈ U := by
    apply hp
    rwa [ordinary_witness, fromOrdinary_base]
  have he := eventually_chartTrace _ ordinary_witness
  obtain ⟨W, hWo, hWw, hW⟩ := exists_open_normalizedMarginal_localization
    (m := r + 2) (by omega) (hU'.and he)
  refine ⟨W, hWo, hWw, ?_⟩
  rintro _ ⟨A, hA, rfl⟩ hAW
  rw [twoSiteObservation_traceWord] at hAW
  obtain ⟨hAt, hU, ht, hb, ha⟩ := hW A hA hAW
  obtain ⟨c, hc, heq⟩ := traceWord_eq_scaled_chart A hAt rfl ht hb ha (2 + (r + 2))
  refine ⟨_, hU, ?_⟩
  change chartProjector r _ = projector (traceWord 2 2 (2 + (r + 2)) A)
  rw [heq, projector_scale _ hc]
  rfl

private theorem observation_eq_of_marginal_eq {r : ℕ} {x z : Coord}
    (h : normalizedMarginal (r + 2) (cores x) = normalizedMarginal (r + 2) (cores z)) :
    observation r x = observation r z := by
  rw [normalizedMarginal_eq_rawTwo, normalizedMarginal_eq_rawTwo] at h
  have hc (imag : Bool) (i : Fin 8) : component imag r i x = component imag r i z := by
    have he := congrArg (fun A : Matrix Pair Pair ℂ => A (entry i).1 (entry i).2) h
    cases imag
    · simpa [component, normalizedTwo, twoMass] using congrArg Complex.re he
    · simpa [component, normalizedTwo, twoMass] using congrArg Complex.im he
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (hc false 3) (hc false 6))
  · funext i
    fin_cases i <;> exact hc false _
  · funext i
    fin_cases i <;> exact hc true _

/-- A witness neighborhood in the actual periodic MPS projector space has a relatively
open dense subset whose two-site marginals determine the full state among all actual
bond-two periodic MPS. The only hypothesis beyond the length bound is sheet separation. -/
theorem exists_generic_actual_reconstruction (r : ℕ) (hr : 3 ≤ r)
    (hpair : HasSeparatedPairs r) :
    ∃ N : Set (actualProjectors (r + 2)), IsOpen N ∧
      (⟨witnessProjector (r + 2), witnessProjector_mem_actualProjectors (by omega)⟩ :
        actualProjectors (r + 2)) ∈ N ∧
      ∃ G : Set N, IsOpen G ∧ Dense G ∧
        ∀ P ∈ G, ∀ Q : actualProjectors (r + 2),
          twoSiteObservation (r + 2) Q.val = twoSiteObservation (r + 2) P.val.val →
          Q.val = P.val.val := by
  obtain ⟨S, hSo, hSw, hS, G, hGo, hGd, hG⟩ :=
    exists_generic_chart_reconstruction r hr hpair (eventually_nonzero_traceWord r hr)
  obtain ⟨K, hKc, hKw, hKS⟩ := exists_compact_subset hSo hSw
  obtain ⟨W, hWo, hWw, hW⟩ := exists_chart_localization r hr
    (isOpen_interior.mem_nhds hKw)
  let P := chartProjector r
  let F := twoSiteObservation (r + 2)
  let X := actualProjectors (r + 2)
  let G₀ : Set Coord := Subtype.val '' G
  let N : Set X := {x | F x.val ∈ W}
  -- Compactness makes the projectors with a representative outside G₀ a closed set.
  let excluded : Set (StateMatrix (r + 2)) := P '' (K ∩ G₀ᶜ)
  have hG₀ : IsOpen G₀ := hSo.isOpenMap_subtype_val _ hGo
  have hPc : ContinuousOn P S := fun x hx => (continuousAt_chartProjector r x (hS hx)).continuousWithinAt
  have hPmem (x : Coord) (hx : x ∈ S) : P x ∈ X := ⟨cores x, hS hx, rfl⟩
  have hF : Continuous F := continuous_twoSiteObservation _
  have hN : IsOpen N := hWo.preimage (hF.comp continuous_subtype_val)
  have hNw : (⟨witnessProjector (r + 2), witnessProjector_mem_actualProjectors (by omega)⟩ : X)
      ∈ N := by
    change (twoSiteObservation (r + 2)) (witnessProjector (r + 2)) ∈ W
    rw [witnessProjector, PeriodicMPSUniformHardCorePencilDecoder.witnessTensor,
      twoSiteObservation_traceWord]
    exact hWw
  have hEx : IsClosed excluded :=
    ((hKc.inter_right hG₀.isClosed_compl).image_of_continuousOn
      (hPc.mono fun _ hx => hKS hx.1)).isClosed
  have hGinj {x z : Coord} (hx : x ∈ G₀) (hz : z ∈ S) (he : F (P z) = F (P x)) :
      z = x := by
    obtain ⟨x', hx', rfl⟩ := hx
    have ho := observation_eq_of_marginal_eq (r := r) (x := z) (z := x'.val) (by
      simpa only [F, P, chartProjector, twoSiteObservation_traceWord] using he)
    exact congrArg Subtype.val (hG x' hx' ⟨z, hz⟩ ho)
  have hGood {x : Coord} (hx : x ∈ G₀) : P x ∉ excluded := by
    rintro ⟨z, hz, he⟩
    exact hz.2 ((hGinj hx (hKS hz.1) (congrArg F he)).symm ▸ hx)
  let G' : Set N := {q | q.val.val ∉ excluded}
  refine ⟨N, hN, hNw, G', hEx.isOpen_compl.preimage
    (continuous_subtype_val.comp continuous_subtype_val), ?_, ?_⟩
  · rw [dense_iff_inter_open]
    intro V hVo hVne
    obtain ⟨q, hq⟩ := hVne
    obtain ⟨V₀, hV₀, hVe⟩ := isOpen_induced_iff.mp hVo
    obtain ⟨V₁, hV₁, hV₀e⟩ := isOpen_induced_iff.mp hV₀
    have hqV : q.val.val ∈ V₁ := by
      rw [← hVe, ← hV₀e] at hq
      exact hq
    obtain ⟨x, hx, he⟩ := hW q.val.val q.val.property q.property
    let T : Set S := Subtype.val ⁻¹' interior K ∩
      (F ∘ P ∘ Subtype.val) ⁻¹' W ∩ (P ∘ Subtype.val) ⁻¹' V₁
    have hT : IsOpen T :=
      ((isOpen_interior.preimage continuous_subtype_val).inter
        (hWo.preimage (hF.comp hPc.domRestrict))).inter (hV₁.preimage hPc.domRestrict)
    have hTne : T.Nonempty := by
      refine ⟨⟨x, hKS (interior_subset hx)⟩, ⟨hx, ?_⟩, ?_⟩
      · change F (chartProjector r x) ∈ W
        rw [he]
        exact q.property
      · change chartProjector r x ∈ V₁
        rwa [he]
    obtain ⟨z, hzT, hzG⟩ := dense_iff_inter_open.mp hGd T hT hTne
    let q' : N := ⟨⟨P z, hPmem z z.property⟩, hzT.1.2⟩
    refine ⟨q', ?_, hGood ⟨z, hzG, rfl⟩⟩
    rw [← hVe, ← hV₀e]
    exact hzT.2
  · intro q hq Q he
    obtain ⟨x, hx, hxq⟩ := hW q.val.val q.val.property q.property
    have hxG : x ∈ G₀ := by
      by_contra hxG
      exact hq ⟨x, ⟨interior_subset hx, hxG⟩, hxq⟩
    have hQ : F Q.val ∈ W := he.symm ▸ q.property
    obtain ⟨z, hz, hzQ⟩ := hW Q.val Q.property hQ
    have hxz := hGinj hxG (hKS (interior_subset hz))
      ((congrArg F hzQ).trans (he.trans (congrArg F hxq).symm))
    exact hzQ.symm.trans ((congrArg P hxz).trans hxq)

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticChart

#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticChart.exists_analytic_chart
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticChart.exists_coherence_fold
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticChart.hasSeparatedPairs_of_quartic_expansion
#print axioms D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCoreAnalyticChart.exists_generic_actual_reconstruction
