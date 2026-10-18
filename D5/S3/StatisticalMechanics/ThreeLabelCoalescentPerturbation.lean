/- GID: D5/S3/StatisticalMechanics/ThreeLabelCoalescentPerturbation
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/ThreeLabelCoalescentPerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Seven-rate open-neighborhood stability of the two simple association crossings. -/

import D5.S3.StatisticalMechanics.ThreeLabelCoalescentTail
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Open stability of two association crossings -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.StatisticalMechanics.ThreeLabelCoalescentPerturbation
open D5.S3.StatisticalMechanics.ThreeLabelCoalescent Set Filter
open scoped Topology

private def rawOperator (r : Fin 7 → ℝ) : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := generalForward r
    map_add' := by
      intro q p; ext i; fin_cases i <;> simp [generalForward] <;> ring
    map_smul' := by
      intro c q; ext i; fin_cases i <;> simp [generalForward] <;> ring }

private def generator (r : Fin 7 → ℝ) : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  ∑ i, r i • rawOperator (Pi.single i 1)

private lemma generator_apply (r : Fin 7 → ℝ) (q : Fin 5 → ℝ) :
    generator r q = generalForward r q := by
  ext i
  fin_cases i <;>
    norm_num [generator, rawOperator, generalForward, outgoing, Fin.sum_univ_succ,
      Pi.single_apply] <;> ring

private lemma generator_continuous : Continuous generator := by
  unfold generator
  fun_prop

private def model (r : Fin 7 → ℝ) (t : ℝ) : Fin 5 → ℝ :=
  (NormedSpace.exp (t • generator r)) initial

private lemma model_start (r : Fin 7 → ℝ) : model r 0 = initial := by
  simp [model]

private lemma model_derivative (r : Fin 7 → ℝ) (t : ℝ) :
    HasDerivAt (model r) (generalForward r (model r t)) t := by
  have hd := (hasDerivAt_exp_smul_const' (generator r) t).clm_apply
    (hasDerivAt_const t initial)
  simpa [model, mul_apply_eq_comp, generator_apply] using! hd

private lemma model_continuous : Continuous (fun rt : (Fin 7 → ℝ) × ℝ => model rt.1 rt.2) := by
  have hc : Continuous (fun rt : (Fin 7 → ℝ) × ℝ => rt.2 • generator rt.1) :=
    continuous_snd.smul (generator_continuous.comp continuous_fst)
  have he : Continuous (NormedSpace.exp : ((Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ)) → _) :=
    continuous_iff_continuousAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt
  exact (he.comp hc).clm_apply continuous_const

private lemma model_unique (r : Fin 7 → ℝ) (p : ℝ → Fin 5 → ℝ)
    (hp : GeneralForwardLaw r p) (t : ℝ) (ht : 0 ≤ t) : p t = model r t := by
  have hd (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt (fun t => p t - model r t) (generator r (p s - model r s)) s := by
    have hp' : HasDerivAt p (generalForward r (p s)) s :=
      hasDerivAt_pi.mpr (hp.equation s hs)
    simpa only [map_sub, generator_apply] using! hp'.sub (model_derivative r s)
  have h0 : p 0 - model r 0 = 0 := by rw [hp.start, model_start, sub_self]
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun t => p t - model r t) (f' := fun t => generator r (p t - model r t))
    (K := ‖generator r‖) (a := 0) (b := t)
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hd s hs.1).hasDerivWithinAt) h0
    (fun s _ => (generator r).le_opNorm _) t ⟨ht, le_rfl⟩
  exact sub_eq_zero.mp hz

private def assocDerivative (r : Fin 7 → ℝ) (q : Fin 5 → ℝ) : ℝ :=
  generalForward r q 0 * q 3 + q 0 * generalForward r q 3 -
    (generalForward r q 1 * q 2 + q 1 * generalForward r q 2)

private lemma association_continuous :
    Continuous (fun rt : (Fin 7 → ℝ) × ℝ => delta (model rt.1 rt.2)) ∧
    Continuous (fun rt : (Fin 7 → ℝ) × ℝ => assocDerivative rt.1 (model rt.1 rt.2)) := by
  have hc := model_continuous
  constructor
  · unfold delta
    fun_prop
  · unfold assocDerivative generalForward outgoing
    fun_prop


private def association (r : Fin 7 → ℝ) (t : ℝ) : ℝ := delta (model r t)
private def slope (r : Fin 7 → ℝ) (t : ℝ) : ℝ := assocDerivative r (model r t)

private lemma association_derivative (r : Fin 7 → ℝ) (t : ℝ) :
    HasDerivAt (association r) (slope r t) t := by
  have hd := hasDerivAt_pi.mp (model_derivative r t)
  convert ((hd 0).mul (hd 3)).sub ((hd 1).mul (hd 2)) using 1 <;> rfl

/-- Two positive simple zeros and the signs on all three intervening intervals. -/
def TwoSimpleCrossings (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ a < b ∧ f a = 0 ∧ f b = 0 ∧
    deriv f a ≠ 0 ∧ deriv f b ≠ 0 ∧
    (∀ t, 0 < t → t < a → 0 < f t) ∧
    (∀ t, a < t → t < b → f t < 0) ∧
    (∀ t, b < t → 0 < f t)

private lemma compact_sign (f : (Fin 7 → ℝ) → ℝ → ℝ)
    (hc : Continuous (fun rt : (Fin 7 → ℝ) × ℝ => f rt.1 rt.2))
    (r₀ : Fin 7 → ℝ) (S : Set ℝ) (hS : IsCompact S)
    (hn : ∀ t ∈ S, f r₀ t ≠ 0) :
    ∃ U : Set (Fin 7 → ℝ), IsOpen U ∧ r₀ ∈ U ∧
      ∀ r ∈ U, ∀ t ∈ S, 0 < f r t * f r₀ t := by
  have hb : Continuous (fun rt : (Fin 7 → ℝ) × ℝ => f r₀ rt.2) :=
    hc.comp (continuous_const.prodMk continuous_snd)
  obtain ⟨U, V, hU, _, hbase, hSV, hUV⟩ := generalized_tube_lemma
    (isCompact_singleton (x := r₀)) hS (isOpen_lt continuous_const (hc.mul hb)) (by
      rintro ⟨r, t⟩ ⟨hr, ht⟩
      have he : r = r₀ := mem_singleton_iff.mp hr
      subst r
      exact mul_self_pos.mpr (hn t ht))
  refine ⟨U, hU, hbase (mem_singleton r₀), ?_⟩
  intro r hr t ht
  exact hUV (show (r,t) ∈ U ×ˢ V from ⟨hr, hSV ht⟩)

private lemma small_window (g : ℝ → ℝ) (hc : Continuous g)
    (a l u : ℝ) (hla : l < a) (hau : a < u) (ha : g a ≠ 0) :
    ∃ al ar : ℝ, l < al ∧ al < a ∧ a < ar ∧ ar < u ∧
      ∀ t ∈ Icc al ar, g t ≠ 0 := by
  have hn : {t | g t ≠ 0} ∩ Ioo l u ∈ 𝓝 a :=
    inter_mem ((isOpen_ne_fun hc continuous_const).mem_nhds ha) (Ioo_mem_nhds hla hau)
  obtain ⟨b, c, ⟨hab, hac⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  have hleft : (b + a) / 2 ∈ Ioo b c := by constructor <;> linarith
  have hright : (c + a) / 2 ∈ Ioo b c := by constructor <;> linarith
  refine ⟨(b+a)/2, (c+a)/2, (hsub hleft).2.1, by linarith,
    by linarith, (hsub hright).2.2, ?_⟩
  intro t ht
  exact (hsub (show t ∈ Ioo b c by constructor <;> linarith [ht.1, ht.2])).1

private lemma compact_root_stability
    (f df : (Fin 7 → ℝ) → ℝ → ℝ)
    (hc : Continuous (fun rt : (Fin 7 → ℝ) × ℝ => f rt.1 rt.2))
    (hdc : Continuous (fun rt : (Fin 7 → ℝ) × ℝ => df rt.1 rt.2))
    (hd : ∀ r t, HasDerivAt (f r) (df r t) t)
    (r₀ : Fin 7 → ℝ) (hroots : TwoSimpleCrossings (f r₀))
    (Valid : (Fin 7 → ℝ) → Prop)
    (Ue Ut : Set (Fin 7 → ℝ)) (hUe : IsOpen Ue) (hUt : IsOpen Ut)
    (hre : r₀ ∈ Ue) (hrt : r₀ ∈ Ut)
    (ε T : ℝ) (hε : 0 < ε)
    (he : ∀ r ∈ Ue, Valid r → ∀ t, 0 < t → t < ε → 0 < f r t)
    (htail : ∀ r ∈ Ut, Valid r → ∀ t, T ≤ t → 0 < f r t) :
    ∃ U : Set (Fin 7 → ℝ), IsOpen U ∧ r₀ ∈ U ∧
      ∀ r ∈ U, Valid r → TwoSimpleCrossings (f r) := by
  obtain ⟨a, b, ha, hab, hza, hzb, hda, hdb, hpos, hneg, hlate⟩ := hroots
  have hdf (t : ℝ) : Continuous (df r₀) := hdc.comp (continuous_const.prodMk continuous_id)
  have hda' : df r₀ a ≠ 0 := by simpa [(hd r₀ a).deriv] using hda
  have hdb' : df r₀ b ≠ 0 := by simpa [(hd r₀ b).deriv] using hdb
  obtain ⟨al, ar, hal, hala, haar, harm, had⟩ :=
    small_window (df r₀) (hdf a) a 0 ((a+b)/2) ha (by linarith) hda'
  obtain ⟨bl, br, hmbl, hblb, hbbr, hbru, hbd⟩ :=
    small_window (df r₀) (hdf b) b ((a+b)/2) (b+1) (by linarith) (by linarith) hdb'
  have harbl : ar < bl := harm.trans hmbl
  let e := min (ε/2) (al/2)
  let B := max T (br+1)
  have hep : 0 < e := by dsimp [e]; positivity
  have heε : e < ε := (min_le_left _ _).trans_lt (by linarith)
  have heal : e < al := (min_le_right _ _).trans_lt (by linarith)
  have hbrB : br < B := lt_of_lt_of_le (by linarith : br < br+1) (le_max_right _ _)
  let S : Set ℝ := Icc e B \ (Ioo al ar ∪ Ioo bl br)
  have hS : IsCompact S := isCompact_Icc.diff (isOpen_Ioo.union isOpen_Ioo)
  have hbasezero (t : ℝ) (ht : 0 < t) (hz : f r₀ t = 0) : t = a ∨ t = b := by
    rcases lt_trichotomy t a with hlt | heq | hgt
    · exact (ne_of_gt (hpos t ht hlt) hz).elim
    · exact Or.inl heq
    · rcases lt_trichotomy t b with hlt | heq | hgt'
      · exact (ne_of_lt (hneg t hgt hlt) hz).elim
      · exact Or.inr heq
      · exact (ne_of_gt (hlate t hgt') hz).elim
  have hSn (t : ℝ) (ht : t ∈ S) : f r₀ t ≠ 0 := by
    intro hz
    rcases hbasezero t (hep.trans_le ht.1.1) hz with heq | heq
    · subst t; exact ht.2 (Or.inl ⟨hala, haar⟩)
    · subst t; exact ht.2 (Or.inr ⟨hblb, hbbr⟩)
  obtain ⟨Us, hUs, hrs, hsign⟩ := compact_sign f hc r₀ S hS hSn
  obtain ⟨Ua, hUa, hra, hasign⟩ := compact_sign df hdc r₀ (Icc al ar) isCompact_Icc had
  obtain ⟨Ub, hUb, hrb, hbsign⟩ := compact_sign df hdc r₀ (Icc bl br) isCompact_Icc hbd
  let U := Ue ∩ Ut ∩ Us ∩ Ua ∩ Ub
  refine ⟨U, (((hUe.inter hUt).inter hUs).inter hUa).inter hUb,
    ⟨⟨⟨⟨hre, hrt⟩, hrs⟩, hra⟩, hrb⟩, ?_⟩
  intro r hr hv
  rcases hr with ⟨⟨⟨⟨hre', hrt'⟩, hrs'⟩, hra'⟩, hrb'⟩
  have hfc : Continuous (f r) := hc.comp (continuous_const.prodMk continuous_id)
  have hspos (t : ℝ) (ht : t ∈ S) (hp : 0 < f r₀ t) : 0 < f r t :=
    (mul_pos_iff_of_pos_right hp).mp (hsign r hrs' t ht)
  have hsneg (t : ℝ) (ht : t ∈ S) (hp : f r₀ t < 0) : f r t < 0 := by
    have := hsign r hrs' t ht
    nlinarith
  have halS : al ∈ S := by
    refine ⟨⟨heal.le, ?_⟩, ?_⟩
    · linarith
    · rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩) <;> linarith
  have harS : ar ∈ S := by
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩) <;> linarith
  have hblS : bl ∈ S := by
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩) <;> linarith
  have hbrS : br ∈ S := by
    refine ⟨⟨by linarith, hbrB.le⟩, ?_⟩
    rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩) <;> linarith
  have halpos := hspos al halS (hpos al hal hala)
  have harneg := hsneg ar harS (hneg ar haar (by linarith))
  have hblneg := hsneg bl hblS (hneg bl (by linarith) hblb)
  have hbrpos := hspos br hbrS (hlate br hbbr)
  obtain ⟨x, hx, hzx⟩ := intermediate_value_Icc' (show al ≤ ar by linarith)
    hfc.continuousOn ⟨harneg.le, halpos.le⟩
  obtain ⟨y, hy, hzy⟩ := intermediate_value_Icc (show bl ≤ br by linarith)
    hfc.continuousOn ⟨hblneg.le, hbrpos.le⟩
  have halx : al < x := lt_of_le_of_ne hx.1 (by intro h; subst x; linarith)
  have hxar : x < ar := lt_of_le_of_ne hx.2 (by intro h; subst x; linarith)
  have hbly : bl < y := lt_of_le_of_ne hy.1 (by intro h; subst y; linarith)
  have hybr : y < br := lt_of_le_of_ne hy.2 (by intro h; subst y; linarith)
  have hxy : x < y := hxar.trans (harbl.trans hbly)
  have hlocal (l u z : ℝ) (hdn : ∀ t ∈ Icc l u, df r t ≠ 0)
      (hz : z ∈ Icc l u) (hzz : f r z = 0) :
      ∀ t ∈ Icc l u, f r t = 0 → t = z := by
    intro t ht hzt
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨c, hct, hcz⟩ := exists_hasDerivAt_eq_zero hlt hfc.continuousOn
        (hzt.trans hzz.symm) (fun s _ => hd r s)
      exact hdn c ⟨ht.1.trans hct.1.le, hct.2.le.trans hz.2⟩ hcz
    · obtain ⟨c, hct, hcz⟩ := exists_hasDerivAt_eq_zero hgt hfc.continuousOn
        (hzz.trans hzt.symm) (fun s _ => hd r s)
      exact hdn c ⟨hz.1.trans hct.1.le, hct.2.le.trans ht.2⟩ hcz
  have hdan (t : ℝ) (ht : t ∈ Icc al ar) : df r t ≠ 0 := by
    have := hasign r hra' t ht
    exact fun he => by rw [he, zero_mul] at this; exact lt_irrefl _ this
  have hdbn (t : ℝ) (ht : t ∈ Icc bl br) : df r t ≠ 0 := by
    have := hbsign r hrb' t ht
    exact fun he => by rw [he, zero_mul] at this; exact lt_irrefl _ this
  have honly (t : ℝ) (ht : 0 < t) (hz : f r t = 0) : t = x ∨ t = y := by
    by_cases htε : t < e
    · exact (ne_of_gt (he r hre' hv t ht (htε.trans heε)) hz).elim
    by_cases htT : B ≤ t
    · exact (ne_of_gt (htail r hrt' hv t ((le_max_left _ _).trans htT)) hz).elim
    by_cases hta : t ∈ Ioo al ar
    · exact Or.inl (hlocal al ar x hdan hx hzx t ⟨hta.1.le, hta.2.le⟩ hz)
    by_cases htb : t ∈ Ioo bl br
    · exact Or.inr (hlocal bl br y hdbn hy hzy t ⟨htb.1.le, htb.2.le⟩ hz)
    have hs : t ∈ S := ⟨⟨le_of_not_gt htε, (lt_of_not_ge htT).le⟩, by simpa using And.intro hta htb⟩
    have := hsign r hrs' t hs
    rw [hz, zero_mul] at this
    exact (lt_irrefl _ this).elim
  have hn (t : ℝ) (ht : 0 < t) (htx : t ≠ x) (hty : t ≠ y) : f r t ≠ 0 := by
    intro hz; rcases honly t ht hz with he | he
    · exact htx he
    · exact hty he
  refine ⟨x, y, hal.trans halx, hxy, hzx, hzy,
    by simpa [(hd r x).deriv] using hdan x hx,
    by simpa [(hd r y).deriv] using hdbn y hy, ?_, ?_, ?_⟩
  · intro t ht htx
    by_contra hnot
    obtain ⟨z, hz, hzero⟩ := isPreconnected_Ioo.intermediate_value₂
      (show t ∈ Ioo 0 x from ⟨ht, htx⟩) (show al ∈ Ioo 0 x from ⟨hal, halx⟩)
      hfc.continuousOn continuousOn_const (le_of_not_gt hnot) halpos.le
    exact hn z hz.1 (ne_of_lt hz.2) (ne_of_lt (hz.2.trans hxy)) hzero
  · intro t hxt hty
    by_contra hnot
    obtain ⟨z, hz, hzero⟩ := isPreconnected_Ioo.intermediate_value₂
      (show ar ∈ Ioo x y from ⟨hxar, harbl.trans hbly⟩)
      (show t ∈ Ioo x y from ⟨hxt, hty⟩)
      hfc.continuousOn continuousOn_const harneg.le (le_of_not_gt hnot)
    exact hn z ((hal.trans halx).trans hz.1) (ne_of_gt hz.1) (ne_of_lt hz.2) hzero
  · intro t hyt
    by_contra hnot
    obtain ⟨z, hz, hzero⟩ := isPreconnected_Ioi.intermediate_value₂
      (show t ∈ Ioi y from hyt) (show br ∈ Ioi y from hybr)
      hfc.continuousOn continuousOn_const (le_of_not_gt hnot) hbrpos.le
    exact hn z ((hal.trans halx).trans (hxy.trans hz)) (ne_of_gt (hxy.trans hz))
      (ne_of_gt hz) hzero


private lemma model_probability (r : Fin 7 → ℝ) (hr : ∀ i, 0 < r i) :
    GeneralForwardLaw r (model r) := by
  have hd (t : ℝ) := hasDerivAt_pi.mp (model_derivative r t)
  have hn (s : ℝ) : HasDerivAt
      (fun t => Real.exp (outgoing r * t) * model r t 0) 0 s := by
    convert (((hasDerivAt_id s).const_mul (outgoing r)).exp).mul (hd s 0) using 1
    · ext t; rfl
    · simp only [generalForward, Matrix.cons_val_zero]; ring
  have hnconst := is_const_of_deriv_eq_zero
    (fun t => (hn t).differentiableAt) (fun t => (hn t).deriv)
  have hN (t : ℝ) : 0 < model r t 0 := by
    have he := hnconst t 0
    simp only [mul_zero, Real.exp_zero, model_start, initial, Matrix.cons_val_zero, one_mul] at he
    apply (mul_pos_iff_of_pos_left (Real.exp_pos (outgoing r * t))).mp
    rw [he]; norm_num
  have branch (i : Fin 5) (a d : ℝ) (ha : 0 ≤ a) (hi : initial i = 0)
      (he : ∀ t, generalForward r (model r t) i = a * model r t 0 - d * model r t i)
      (t : ℝ) (ht : 0 ≤ t) : 0 ≤ model r t i := by
    have hw (s : ℝ) : HasDerivAt (fun u => Real.exp (d*u) * model r u i)
        (a * Real.exp (d*s) * model r s 0) s := by
      convert (((hasDerivAt_id s).const_mul d).exp).mul (hd s i) using 1
      · ext u; rfl
      · rw [he s]; simp only [id_eq]; ring
    have hm : MonotoneOn (fun s => Real.exp (d*s) * model r s i) (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · intro s _; exact (hw s).continuousAt.continuousWithinAt
      · intro s _; exact (hw s).differentiableAt.differentiableWithinAt
      · intro s _; rw [(hw s).deriv]; exact mul_nonneg (mul_nonneg ha (Real.exp_pos _).le) (hN s).le
    have he := hm (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
    simp only [mul_zero, Real.exp_zero, model_start, hi, mul_zero] at he
    exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp he
  have hA (t : ℝ) (ht : 0 ≤ t) : 0 ≤ model r t 1 :=
    branch 1 (r 0) (r 4) (hr 0).le (by norm_num [initial])
      (fun _ => by simp [generalForward]) t ht
  have hB (t : ℝ) (ht : 0 ≤ t) : 0 ≤ model r t 2 :=
    branch 2 (r 1) (r 5) (hr 1).le (by norm_num [initial])
      (fun _ => by simp [generalForward]) t ht
  have hC (t : ℝ) (ht : 0 ≤ t) : 0 ≤ model r t 4 :=
    branch 4 (r 2) (r 6) (hr 2).le (by norm_num [initial])
      (fun _ => by simp [generalForward]) t ht
  have hT : MonotoneOn (fun t => model r t 3) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t _; exact (hd t 3).continuousAt.continuousWithinAt
    · intro t _; exact (hd t 3).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t 3).deriv]
      have ht0 : 0 ≤ t := interior_subset ht
      change 0 ≤ r 3 * model r t 0 + r 4 * model r t 1 +
        r 5 * model r t 2 + r 6 * model r t 4
      exact add_nonneg (add_nonneg (add_nonneg
        (mul_nonneg (hr 3).le (hN t).le) (mul_nonneg (hr 4).le (hA t ht0)))
        (mul_nonneg (hr 5).le (hB t ht0))) (mul_nonneg (hr 6).le (hC t ht0))
  have hsum (t : ℝ) : HasDerivAt (fun s => ∑ i, model r s i) 0 t := by
    convert ((((hd t 0).add (hd t 1)).add (hd t 2)).add (hd t 3)).add (hd t 4) using 1
    · ext s; simp [Fin.sum_univ_five] <;> ring
    · norm_num [generalForward, outgoing]; ring
  have hsumconst := is_const_of_deriv_eq_zero
    (fun t => (hsum t).differentiableAt) (fun t => (hsum t).deriv)
  refine ⟨model_start r, fun t _ => hd t, ?_, ?_⟩
  · intro t ht i
    fin_cases i
    · exact (hN t).le
    · exact hA t ht
    · exact hB t ht
    · have he := hT (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
      simpa [model_start, initial] using he
    · exact hC t ht
  · intro t _
    simpa [model_start, initial, Fin.sum_univ_five] using hsumconst t 0

private lemma base_general (h : ℝ) (hh : 0 < h) :
    GeneralForwardLaw (baseRates h) (explicit h) := by
  have hp := (positive_probability_solution h hh).1
  have hL : outgoing (baseRates h) = ell h := by dsimp [outgoing, baseRates, ell]; ring
  refine ⟨hp.start, ?_, ?_, ?_⟩
  · intro t ht i
    convert hp.equation t ht i using 1
    fin_cases i <;> simp only [generalForward, forward, hL] <;>
      simp [baseRates] <;> ring
  · intro t ht i
    rcases eq_or_lt_of_le ht with he | he
    · rw [← he, hp.start]; fin_cases i <;> norm_num [initial]
    · exact ((positive_probability_solution h hh).2 _ hp t he).2.2.1 i |>.le
  · intro t ht
    rcases eq_or_lt_of_le ht with he | he
    · rw [← he, hp.start]; norm_num [initial, Fin.sum_univ_succ]
    · exact ((positive_probability_solution h hh).2 _ hp t he).2.1

private lemma base_crossings (h : ℝ) (hh : 0 < h) (hc : TwoCrossings h) :
    TwoSimpleCrossings (association (baseRates h)) := by
  have hp := base_general h hh
  have hformula (t : ℝ) (ht : 0 ≤ t) : association (baseRates h) t = v h t * H h t := by
    rw [association, ← model_unique _ _ hp t ht]
    exact (forward_solution h hh _ (positive_probability_solution h hh).1 t ht).2
  obtain ⟨a,b,ha,hab,hza,hzb,hda,hdb,hpos,hneg,hlate⟩ := hc
  have hslope (t : ℝ) (ht : 0 < t) (hz : H h t = 0) (hd : deriv (H h) t ≠ 0) :
      deriv (association (baseRates h)) t ≠ 0 := by
    have heq : association (baseRates h) =ᶠ[𝓝 t] (fun s => v h s * H h s) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact hformula s hs.le
    have hv : DifferentiableAt ℝ (v h) t := by unfold v; fun_prop
    have hH : DifferentiableAt ℝ (H h) t := by unfold H u v; fun_prop
    have hprod : HasDerivAt (fun s => v h s * H h s)
        (deriv (v h) t * H h t + v h t * deriv (H h) t) t := by
      simpa only [Pi.mul_apply] using! hv.hasDerivAt.mul hH.hasDerivAt
    rw [heq.deriv_eq, hprod.deriv, hz, mul_zero, zero_add]
    exact mul_ne_zero (ne_of_gt (Real.exp_pos _)) hd
  refine ⟨a,b,ha,hab,?_,?_,hslope a ha hza hda,
    hslope b (ha.trans hab) hzb hdb,?_,?_,?_⟩
  · rw [hformula a ha.le, hza, mul_zero]
  · rw [hformula b (ha.trans hab).le, hzb, mul_zero]
  · intro t ht hta; rw [hformula t ht.le]
    exact mul_pos (Real.exp_pos _) (hpos t ht hta)
  · intro t hat htb; rw [hformula t (ha.trans hat).le]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (hneg t hat htb)
  · intro t hbt; rw [hformula t (ha.trans (hab.trans hbt)).le]
    exact mul_pos (Real.exp_pos _) (hlate t hbt)

/-- Every two-crossing base vector has an open neighborhood preserving exactly
 two positive simple association zeros and the full positive-negative-positive order. -/
theorem seven_rate_two_crossings_stable (h : ℝ) (hh : 0 < h) (hc : TwoCrossings h) :
    ∃ U : Set (Fin 7 → ℝ), IsOpen U ∧ baseRates h ∈ U ∧
      (∀ r ∈ U, ∀ i, 0 < r i) ∧
      (∀ r ∈ U, ∃ p : ℝ → Fin 5 → ℝ, GeneralForwardLaw r p) ∧
      ∀ r ∈ U, ∀ p : ℝ → Fin 5 → ℝ, GeneralForwardLaw r p →
        TwoSimpleCrossings (fun t => delta (p t)) := by
  obtain ⟨Ue, hUe, hre, ε, hε, he⟩ :=
    ThreeLabelCoalescentTail.uniform_positive_near_zero h hh
  obtain ⟨Ut, hUt, hrt, T, hT, htail⟩ := ThreeLabelCoalescentTail.uniform_positive_tail
  let Valid := fun r => ∃ p, GeneralForwardLaw r p
  obtain ⟨U, hU, hrU, hstable⟩ := compact_root_stability association slope
    association_continuous.1 association_continuous.2 association_derivative
    (baseRates h) (base_crossings h hh hc) Valid Ue Ut hUe hUt hre (hrt h hh) ε T hε
    (by intro r hr ⟨p,hp⟩ t ht htε
        rw [association, ← model_unique _ _ hp t ht.le]
        exact he r hr p hp t ht htε)
    (by intro r hr ⟨p,hp⟩ t ht
        have ht0 : 0 ≤ t := hT.trans ht
        rw [association, ← model_unique _ _ hp t ht0]
        exact htail r hr p hp t ht)
  let P : Set (Fin 7 → ℝ) := {r | ∀ i, 0 < r i}
  have hP : IsOpen P := by
    simpa only [P, setOf_forall] using isOpen_iInter_of_finite
      (fun i : Fin 7 => isOpen_lt continuous_const (continuous_apply i))
  have hrP : baseRates h ∈ P := by
    intro i; fin_cases i <;> norm_num [baseRates, ell] <;> linarith
  refine ⟨U ∩ P, hU.inter hP, ⟨hrU,hrP⟩, fun _ hr => hr.2,
    (fun r hr => ⟨model r, model_probability r hr.2⟩), ?_⟩
  intro r hr p hp
  obtain ⟨a,b,ha,hab,hza,hzb,hda,hdb,hpos,hneg,hlate⟩ :=
    hstable r hr.1 ⟨p,hp⟩
  have heq (t : ℝ) (ht : 0 < t) : delta (p t) = association r t := by
    rw [model_unique r p hp t ht.le]; rfl
  have hdeq (t : ℝ) (ht : 0 < t) :
      deriv (fun s => delta (p s)) t = deriv (association r) t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact heq s hs
  refine ⟨a,b,ha,hab,(heq a ha).trans hza,(heq b (ha.trans hab)).trans hzb,
    by simpa [hdeq a ha] using hda,
    by simpa [hdeq b (ha.trans hab)] using hdb, ?_, ?_, ?_⟩
  · intro t ht hta
    change 0 < delta (p t)
    rw [heq t ht]
    exact hpos t ht hta
  · intro t hat htb
    change delta (p t) < 0
    rw [heq t (ha.trans hat)]
    exact hneg t hat htb
  · intro t hbt
    change 0 < delta (p t)
    rw [heq t (ha.trans (hab.trans hbt))]
    exact hlate t hbt

#print axioms seven_rate_two_crossings_stable
end D5.S3.StatisticalMechanics.ThreeLabelCoalescentPerturbation
