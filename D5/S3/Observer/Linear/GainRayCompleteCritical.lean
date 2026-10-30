/- GID: D5/S3/Observer/Linear/GainRayCompleteCritical
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayCompleteCritical
   mirror-E: none(waiver:whole-world-critical-complete-target)
   anchors: []
   utility: none
   digest: Exact source partners and literal-history critical complete-target exclusion. -/

import D5.S3.Observer.Linear.GainRayCriticalSpan
import D5.S3.Observer.Linear.GainRayAdaptive
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! Source partners on a common open chart, with original literal histories. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

private def partner (A P : Mat) : Mat := A⁻¹ * P.transpose * A

private theorem native_symm (a : Bool) : (action a).IsSymm := by
  cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [action_m_shape, action_j_shape]

private theorem native_power_unit (a : Bool) (k : ℕ) : IsUnit (action a ^ k) := by
  rw [← acquisition_pure]
  exact acquisition_unit _

private theorem partner_rank_trace (A P : Mat) (hA : IsUnit A) :
    (partner A P).rank = P.rank ∧ Matrix.trace (partner A P) = Matrix.trace P := by
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hA
  constructor
  · rw [partner, Matrix.rank_mul_eq_left_of_isUnit_det A _ hd,
      Matrix.rank_mul_eq_right_of_isUnit_det A⁻¹ _ (Matrix.isUnit_nonsing_inv_det _ hd),
      Matrix.rank_transpose]
  · rw [partner, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hd,
      one_mul, Matrix.trace_transpose]

private theorem partner_test (A P K : Mat) (hA : IsUnit A)
    (hs : A.IsSymm) (hK : K.transpose * A = A * K) :
    Matrix.trace (K * partner A P) = Matrix.trace (K * P) := by
  have hd := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have he : A⁻¹ * K.transpose * A = K := by
    rw [Matrix.mul_assoc, hK, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, one_mul]
  calc
    Matrix.trace (K * partner A P) = Matrix.trace ((A⁻¹ * K.transpose * A) * P) := by
      rw [partner]
      conv_lhs => rw [← Matrix.trace_transpose]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hs.eq,
        hs.inv.eq]
      simp only [Matrix.mul_assoc]
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_comm (A * P) (A⁻¹ * K.transpose)
    _ = Matrix.trace (K * P) := by rw [he]

private theorem partner_continuous (A : Mat) : Continuous (partner A) := by
  exact (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const

private theorem perron_line (r : ℝ) (k : ℕ) :
    ∃ s : ℝ, 0 < s ∧ action false ^ k * sourceChart phi r = s • sourceChart phi r := by
  have hm : action false * sourceChart phi r = phi • sourceChart phi r := by
    have hp := Real.goldenRatio_sq
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [action_m_shape, sourceChart, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals nlinarith [congrArg (fun z : ℝ => (1+phi*r)⁻¹*z) hp,
      congrArg (fun z : ℝ => (1+phi*r)⁻¹*r*z) hp]
  cases k with
  | zero => exact ⟨1, zero_lt_one, by simp⟩
  | succ k =>
    obtain ⟨a,b,ha,hb,he⟩ := m_power_coordinates k
    refine ⟨a+b*phi, by positivity, ?_⟩
    rw [he, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, one_mul, hm,
      smul_smul, ← add_smul]

private theorem partner_line_fixed (r : ℝ) (k : ℕ) :
    partner (action false ^ k) (sourceChart phi r) = sourceChart phi r ↔
      (sourceChart phi r).transpose = sourceChart phi r := by
  let A := action false ^ k
  let P := sourceChart phi r
  have hA : IsUnit A := native_power_unit false k
  have hs : A.IsSymm := (native_symm false).pow k
  obtain ⟨s,hspos,hAP⟩ := perron_line r k
  change A * P = s • P at hAP
  have hPt : P.transpose * A = s • P.transpose := by
    have hh := congrArg Matrix.transpose hAP
    simpa only [Matrix.transpose_mul, hs.eq, Matrix.transpose_smul] using hh
  constructor
  · intro h
    have hh := congrArg (fun B : Mat => A * B) h
    change A * (A⁻¹ * P.transpose * A) = A * P at hh
    rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc A,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hA), one_mul,
      hPt, hAP] at hh
    exact (smul_right_injective _ (ne_of_gt hspos)) hh
  · intro h
    change A⁻¹ * P.transpose * A = P
    rw [Matrix.mul_assoc, hPt, h, ← hAP,
      Matrix.nonsing_inv_mul_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det A).mp hA)]


private def positiveChart : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2}

private theorem positiveChart_open : IsOpen positiveChart :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const continuous_snd)

private theorem chart_continuous : ContinuousOn (fun q : ℝ × ℝ => sourceChart q.1 q.2)
    positiveChart := by
  have hd : Continuous (fun q : ℝ × ℝ => 1 + q.1*q.2) := by fun_prop
  have hi := hd.continuousOn.inv₀ (s := positiveChart) (by
    intro q hq
    have hx := hq.1
    have hr := hq.2
    positivity)
  apply hi.smul
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp <;> fun_prop

private def positivePartners (L : ℕ) : Set Mat :=
  {P | ∀ a : Fin (L+1), ∀ i j, 0 < partner (action false ^ a.val) P i j}

private theorem positivePartners_open (L : ℕ) : IsOpen (positivePartners L) := by
  simp only [positivePartners, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro a
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt continuous_const ((partner_continuous _).matrix_elem i j)

private theorem perron_symmetric : (sourceChart phi phi).transpose = sourceChart phi phi := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceChart]

private theorem partner_perron (a : ℕ) :
    partner (action false ^ a) (sourceChart phi phi) = sourceChart phi phi :=
  (partner_line_fixed phi a).mpr perron_symmetric

private theorem line_nonsymmetric (r : ℝ) (hr : phi < r) :
    (sourceChart phi r).transpose ≠ sourceChart phi r := by
  intro he
  have hp : 0 < phi := Real.goldenRatio_pos
  have hrpos : 0 < r := hp.trans hr
  have hden : 0 < 1+phi*r := by positivity
  have hh := congrArg (fun P : Mat => P 0 1) he
  have hh' : (1+phi*r)⁻¹*phi = (1+phi*r)⁻¹*r := by
    simpa [sourceChart, Matrix.transpose_apply] using hh
  exact (ne_of_lt hr) (mul_left_cancel₀ (inv_ne_zero (ne_of_gt hden)) hh')

private theorem j_partner_shape (P : Mat) :
    partner (action true) P = !![P 1 1, P 0 1; P 1 0, P 0 0] := by
  have hj : action true * action true = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [action_j_shape, Matrix.mul_apply, Fin.sum_univ_two]
  have hinv : (action true)⁻¹ = action true :=
    Matrix.inv_eq_right_inv hj
  rw [partner, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [action_j_shape, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private def commonChart (L : ℕ) : Set (ℝ × ℝ) :=
  positiveChart ∩ (fun q : ℝ × ℝ => sourceChart q.1 q.2) ⁻¹'
    (positivePartners L ∩ {P | P 0 0 ≠ P 1 1} ∩
      {P | ∀ a : Fin (L+1), partner (action false ^ a.val) P ≠ P})

private theorem commonChart_open (L : ℕ) : IsOpen (commonChart L) := by
  apply chart_continuous.isOpen_inter_preimage positiveChart_open
  apply IsOpen.inter
  · exact (positivePartners_open L).inter
      (isOpen_ne_fun (continuous_apply 0 |>.comp (continuous_apply 0))
        (continuous_apply 1 |>.comp (continuous_apply 1)))
  · simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro a
    exact isOpen_ne_fun (partner_continuous _) continuous_id

private theorem commonChart_nonempty (L : ℕ) : (commonChart L).Nonempty := by
  let W := positiveChart ∩ (fun q : ℝ × ℝ => sourceChart q.1 q.2) ⁻¹' positivePartners L
  have hWo : IsOpen W := chart_continuous.isOpen_inter_preimage
    positiveChart_open (positivePartners_open L)
  have hbase : (phi,phi) ∈ W := by
    refine ⟨⟨Real.goldenRatio_pos, Real.goldenRatio_pos⟩, ?_⟩
    intro a i j
    rw [partner_perron]
    exact (source_chart_legal phi phi Real.goldenRatio_pos Real.goldenRatio_pos).1 i j
  have hs : IsOpen ((fun r : ℝ => (phi,r)) ⁻¹' W) :=
    hWo.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨l,u,hlu,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hs.mem_nhds hbase)
  let r := (phi+u)/2
  have hr : phi < r := by dsimp [r]; linarith [hlu.2]
  have hw : (phi,r) ∈ W := hsub ⟨by dsimp [r]; linarith [hlu.1,hlu.2],
    by dsimp [r]; linarith [hlu.2]⟩
  refine ⟨(phi,r),hw.1,⟨hw.2, ?_⟩, ?_⟩
  · have hp : 1 < phi := Real.one_lt_goldenRatio
    have hd : 0 < 1+phi*r := by have := hw.1.2; positivity
    intro he
    have hh : (1+phi*r)⁻¹ * 1 = (1+phi*r)⁻¹ * (phi*r) := by
      simpa [sourceChart] using he
    have hn := mul_left_cancel₀ (inv_ne_zero (ne_of_gt hd)) hh
    nlinarith
  · intro a h
    exact line_nonsymmetric r hr ((partner_line_fixed r a.val).mp h)


private theorem mixed_plane (w : List Bool) (hM : false ∈ w) (hJ : true ∈ w)
    (hdim : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))) = 3) :
    ∃ a : Bool, ∃ k : ℕ, 0 < k ∧ k ≤ w.length ∧
      ∀ i : Fin (w.length+1), acquisition (w.take i.val) ∈ Submodule.span ℝ
        (Set.range ![(1 : Mat), action a, action (!a) * action a ^ k]) := by
  obtain ⟨a,k,r,hk,hw⟩ := switch_decomposition w hM hJ
  obtain ⟨h0,h1,h2⟩ := first_switch_generators_mem w a k r hk hw
  let H := Submodule.span ℝ
    (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))
  let B := Submodule.span ℝ (Set.range ![(1 : Mat), action a, action (!a) * action a ^ k])
  have hle : B ≤ H := Submodule.span_le.mpr (by
    rintro A ⟨i,rfl⟩
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;> assumption)
  have heq : B = H := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [finrank_span_eq_card (first_switch_independent a k hk)]
    simpa [H] using hdim.symm)
  refine ⟨a,k,hk,by simp [hw],?_⟩
  intro i
  change acquisition (w.take i.val) ∈ B
  rw [heq]
  exact Submodule.subset_span ⟨i,rfl⟩

private theorem partner_span_agrees (a : Bool) (k : ℕ) (P : Mat) :
    ∀ K ∈ Submodule.span ℝ
      (Set.range ![(1 : Mat), action a, action (!a) * action a ^ k]),
      Matrix.trace (K * partner (action a ^ k) P) = Matrix.trace (K * P) := by
  let A := action a ^ k
  have hA : IsUnit A := native_power_unit a k
  have hs : A.IsSymm := (native_symm a).pow k
  have hgen (i : Fin 3) :
      Matrix.trace ((![(1 : Mat), action a, action (!a) * A] i) * partner A P) =
      Matrix.trace ((![(1 : Mat), action a, action (!a) * A] i) * P) := by
    apply partner_test A P _ hA hs
    fin_cases i
    · simp
    · change (action a).transpose * A = A * action a
      rw [(native_symm a).eq]
      exact (Commute.self_pow (action a) k).eq
    · change (action (!a) * A).transpose * A = A * (action (!a) * A)
      simp only [Matrix.transpose_mul, hs.eq, (native_symm (!a)).eq, Matrix.mul_assoc]
  intro K hK
  induction hK using Submodule.span_induction with
  | mem K hK => obtain ⟨i,rfl⟩ := hK; exact hgen i
  | zero => simp
  | add K T hK hT ihK ihT => simpa only [Matrix.add_mul, Matrix.trace_add, ihK, ihT]
  | smul c K hK ih => simpa only [Matrix.smul_mul, Matrix.trace_smul, ih]

private theorem native_partner_legal (L : ℕ) (x r : ℝ) (hq : (x,r) ∈ commonChart L)
    (a : Bool) (k : ℕ) (hk : k ≤ L) :
    LegalSource (partner (action a ^ k) (sourceChart x r)) ∧
      partner (action a ^ k) (sourceChart x r) ≠ sourceChart x r := by
  have hP := source_chart_legal x r hq.1.1 hq.1.2
  have hrt := partner_rank_trace (action a ^ k) (sourceChart x r) (native_power_unit a k)
  have hzero := hq.2.2 (⟨0,by omega⟩ : Fin (L+1))
  cases a with
  | false =>
      exact ⟨⟨hq.2.1.1 ⟨k,by omega⟩, hrt.1.trans hP.2.1, hrt.2.trans hP.2.2⟩,
        hq.2.2 ⟨k,by omega⟩⟩
  | true =>
      have hj : action true ^ 2 = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [action_j_shape, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
      rw [pow_eq_pow_mod k hj]
      rcases Nat.mod_two_eq_zero_or_one k with hm | hm
      · simp only [hm,pow_zero]
        have he : partner (1 : Mat) (sourceChart x r) =
            partner (action false ^ 0) (sourceChart x r) := by simp
        rw [he]
        exact ⟨⟨hq.2.1.1 ⟨0,by omega⟩,
          (partner_rank_trace _ _ (native_power_unit false 0)).1.trans hP.2.1,
          (partner_rank_trace _ _ (native_power_unit false 0)).2.trans hP.2.2⟩,hzero⟩
      · simp only [hm,pow_one]
        have hu : IsUnit (action true) := by simpa using native_power_unit true 1
        have ht := partner_rank_trace (action true) (sourceChart x r) hu
        refine ⟨⟨?_, ht.1.trans hP.2.1, ht.2.trans hP.2.2⟩, ?_⟩
        · intro i j
          rw [j_partner_shape]
          fin_cases i <;> fin_cases j <;> exact hP.1 _ _
        · intro he
          apply hq.2.1.2
          have hh := congrArg (fun P : Mat => P 1 1) he
          rw [j_partner_shape] at hh
          exact hh

private theorem pure_partner_agrees (a : Bool) (n : ℕ) (P : Mat)
    (i : Fin ((List.replicate n a).length+1)) :
    Matrix.trace (acquisition ((List.replicate n a).take i.val) *
      partner (action false ^ 0) P) =
      Matrix.trace (acquisition ((List.replicate n a).take i.val) * P) := by
  rw [List.take_replicate, acquisition_pure]
  apply partner_test _ _ _ (native_power_unit false 0) ((native_symm false).pow 0)
  simp only [pow_zero, Matrix.mul_one, Matrix.one_mul]
  exact ((native_symm a).pow _).eq

private theorem word_partner (L : ℕ) (x r : ℝ) (hq : (x,r) ∈ commonChart L)
    (w : List Bool) (hL : w.length ≤ L)
    (hshape : (¬ (false ∈ w ∧ true ∈ w)) ∨ Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))) = 3) :
    ∃ P' : Mat, LegalSource P' ∧ P' ≠ sourceChart x r ∧
      ∀ i : Fin (w.length+1),
        Matrix.trace (acquisition (w.take i.val) * P') =
        Matrix.trace (acquisition (w.take i.val) * sourceChart x r) := by
  by_cases hM : false ∈ w
  · by_cases hJ : true ∈ w
    · have hdim := hshape.resolve_left (by simp [hM,hJ])
      obtain ⟨a,k,hk,hkw,hplane⟩ := mixed_plane w hM hJ hdim
      obtain ⟨hlegal,hne⟩ := native_partner_legal L x r hq a k (hkw.trans hL)
      exact ⟨_,hlegal,hne,fun i => partner_span_agrees a k _ _ (hplane i)⟩
    · have hw : w = List.replicate w.length false := List.eq_replicate_length.mpr (by
        intro a ha
        cases a
        · rfl
        · exact (hJ ha).elim)
      obtain ⟨hl,hn⟩ := native_partner_legal L x r hq false 0 (by omega)
      refine ⟨_,hl,hn,?_⟩
      obtain ⟨n,rfl⟩ : ∃ n, w = List.replicate n false := ⟨w.length,hw⟩
      exact pure_partner_agrees false _ _
  · have hw : w = List.replicate w.length true := List.eq_replicate_length.mpr (by
      intro a ha
      cases a
      · exact (hM ha).elim
      · rfl)
    obtain ⟨hl,hn⟩ := native_partner_legal L x r hq false 0 (by omega)
    refine ⟨_,hl,hn,?_⟩
    obtain ⟨n,rfl⟩ : ∃ n, w = List.replicate n true := ⟨w.length,hw⟩
    exact pure_partner_agrees true _ _


/-- Exact answers and gain rays are required at the same actual terminal history. -/
def CompleteCorrect {d : ℕ} (P : Protocol d)
    (answer : ∀ w : List Bool, History w → Mat × Polynomial ℝ × ℝ) (N : ℕ) : Prop :=
  ∀ W : World d, ∃ w C, Terminates P W w C ∧ w.length+1 ≤ N ∧
    Succeeds W w C.1 ∧ answer w (readings W w) = (W.source,gain d W.coeff,W.drift)

private theorem terminal_source_injective {d N : ℕ} (P : Protocol d)
    (answer : ∀ w : List Bool, History w → Mat × Polynomial ℝ × ℝ)
    (hcorrect : CompleteCorrect P answer N) (W W' : World d) (w : List Bool)
    (C : {C : Readout d w // C ∈ P.palette w})
    (ht : Terminates P W w C) (he : readings W w = readings W' w) :
    W.source = W'.source := by
  have exact_at (V : World d) (v : List Bool)
      (D : {D : Readout d v // D ∈ P.palette v}) (hv : Terminates P V v D) :
      answer v (readings V v) = (V.source,gain d V.coeff,V.drift) := by
    obtain ⟨u,E,hu,hN,hs,hex⟩ := hcorrect V
    have hvu := terminal_extends_reached P V v u E hv.1 hu
    have huv := terminal_extends_reached P V u v D hu.1 hv
    have hword : u = v := huv.eq_of_length (Nat.le_antisymm huv.length_le hvu.length_le)
    subst u
    exact hex
  have ht' : Terminates P W' w C := by
    refine ⟨(identical_prefix_transfer P W W' w ht.1 he).1, ?_⟩
    rw [← he]
    exact ht.2
  have h := (exact_at W w C ht).symm.trans ((congrArg (answer w) he).trans (exact_at W' w C ht'))
  exact congrArg Prod.fst h

private theorem partner_forbids_terminal {d N : ℕ} (P : Protocol d)
    (answer : ∀ w : List Bool, History w → Mat × Polynomial ℝ × ℝ)
    (hcorrect : CompleteCorrect P answer N) (L : ℕ) (x r : ℝ)
    (hq : (x,r) ∈ commonChart L) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ)
    (w : List Bool) (hL : w.length ≤ L)
    (hshape : (¬ (false ∈ w ∧ true ∈ w)) ∨ Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))) = 3)
    (C : {C : Readout d w // C ∈ P.palette w}) :
    ¬ Terminates P (chartWorld d x r hq.1.1 hq.1.2 β hβ δ) w C := by
  intro ht
  obtain ⟨S,hS,hne,htrace⟩ := word_partner L x r hq w hL hshape
  let W' : World d := ⟨S,hS,β,hβ,δ⟩
  have he : readings (chartWorld d x r hq.1.1 hq.1.2 β hβ δ) w = readings W' w := by
    ext i
    change (gain d β).eval _ * Matrix.trace (acquisition (w.take i.val) * sourceChart x r) + δ =
      (gain d β).eval _ * Matrix.trace (acquisition (w.take i.val) * S) + δ
    rw [htrace i]
  exact hne (terminal_source_injective P answer hcorrect _ W' w C ht he).symm

private theorem chart_parameters_reconstruct (d : ℕ) (a : Fin (d+4) → ℝ) :
    chartParameters d (a 0) (a 1) (fun k => a ⟨k.val+2,by omega⟩)
      (a ⟨d+3,by omega⟩) = a := by
  ext i
  simp only [chartParameters]
  split_ifs with h h0 hβ
  · exact congrArg a (Fin.ext h0.symm)
  · have hi : i.val = 1 := by omega
    exact congrArg a (Fin.ext hi.symm)
  · exact congrArg a (Fin.ext (by dsimp; omega))
  · exact congrArg a (Fin.ext (by dsimp; omega))

/-- The original full-domain complete target cannot stop at the critical gain-only budget. -/
theorem critical_complete_exclusion (d : ℕ) (hd : 1 ≤ d) (P : Protocol d)
    (answer : ∀ w : List Bool, History w → Mat × Polynomial ℝ × ℝ) :
    ¬ CompleteCorrect P answer (2*d+3) := by
  classical
  intro hcorrect
  let L := 2*(d+1)
  let I := (w : List Bool) × {C : Readout d w // C ∈ P.palette w}
  letI (w : List Bool) : Countable {C : Readout d w // C ∈ P.palette w} :=
    (P.countable w).to_subtype
  have certificate (c : I) : ∃ p : ChartPolynomial d, p ≠ 0 ∧
      ∀ (x r : ℝ) (hq : (x,r) ∈ commonChart L) (β : Coeff d) (hβ : β ≠ 0) (δ : ℝ),
      Terminates P (chartWorld d x r hq.1.1 hq.1.2 β hβ δ) c.1 c.2 →
      c.1.length+1 ≤ 2*d+3 → Succeeds (chartWorld d x r hq.1.1 hq.1.2 β hβ δ) c.1 c.2.1 →
      MvPolynomial.eval (chartParameters d x r β δ) p = 0 := by
    by_cases hu : ∀ W : World d, Collinear W.coeff (c.2.1.mulVec (readings W c.1))
    · refine ⟨1,one_ne_zero,?_⟩
      intro x r hq β hβ δ ht hN hs
      have hL : c.1.length ≤ L := by dsimp [L]; omega
      by_cases hm : false ∈ c.1 ∧ true ∈ c.1
      · obtain ⟨hb,he⟩ := universal_scalar_identity d hd c.1 c.2.1 hu
        have hn := successful_scalar_nonzero c.1 c.2.1 hb he _ hs
        by_cases hshort : c.1.length+1 ≤ 2*(d+1)
        · exact (hn (by rw [mixed_scalar_obstruction d hd c.1 hm.1 hm.2 hshort c.2.1 hb he]; rfl)).elim
        · have hdim := critical_scalar_span d hd c.1 hm.1 hm.2 (by omega) c.2.1 hb he
            (by intro hz; apply hn; rw [hz]; rfl)
          exact (partner_forbids_terminal P answer hcorrect L x r hq β hβ δ c.1 hL
            (Or.inr hdim) c.2 ht).elim
      · exact (partner_forbids_terminal P answer hcorrect L x r hq β hβ δ c.1 hL
          (Or.inl hm) c.2 ht).elim
    · obtain ⟨j,k,hp⟩ := (chart_wedge_nonzero_iff d c.1 c.2.1).mpr hu
      exact ⟨chartWedge d c.1 c.2.1 j k,hp,fun x r hq β hβ δ _ _ hs =>
        success_chart_wedge_zero d c.1 c.2.1 x r hq.1.1 hq.1.2 β hβ δ hs j k⟩
  choose p hp hcert using certificate
  let U : Set (Fin (d+4) → ℝ) := {a | (a 0,a 1) ∈ commonChart L ∧
    (fun k : Fin (d+1) => a ⟨k.val+2,by omega⟩) ≠ 0}
  have ho : IsOpen U := ((commonChart_open L).preimage
    ((continuous_apply 0).prodMk (continuous_apply 1))).inter
      (isOpen_ne.preimage (continuous_pi (fun _ => continuous_apply _)))
  have hne : U.Nonempty := by
    obtain ⟨⟨x,r⟩,hq⟩ := commonChart_nonempty L
    let β : Coeff d := Pi.single 0 1
    have hβ : β ≠ 0 := by intro hz; have hh := congrFun hz 0; simpa [β] using hh
    refine ⟨chartParameters d x r β 0, ?_, ?_⟩
    · simpa [chartParameters] using hq
    · convert hβ using 1
      ext k
      simp [chartParameters]
      omega
  obtain ⟨a,ha,havoid⟩ := countable_polynomial_avoidance (d+4) p hp U ho hne
  let x := a 0
  let r := a 1
  let β : Coeff d := fun k => a ⟨k.val+2,by omega⟩
  let δ := a ⟨d+3,by omega⟩
  have hq : (x,r) ∈ commonChart L := ha.1
  have hβ : β ≠ 0 := ha.2
  obtain ⟨w,C,ht,hN,hs,hex⟩ := hcorrect (chartWorld d x r hq.1.1 hq.1.2 β hβ δ)
  apply havoid ⟨w,C⟩
  rw [← chart_parameters_reconstruct d a]
  exact hcert ⟨w,C⟩ x r hq β hβ δ ht hN hs

#print axioms critical_complete_exclusion
end D5.S3.Observer.Linear.GainRay
