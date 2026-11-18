import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonSigns

/-! The phase at a common cube neighbor after translating two opposite spokes. -/

set_option autoImplicit false
noncomputable section

open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsSwitching flip)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private flip_comm switching_ne_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff diff_flip diff_of_adj_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private diff_injective diff_symm diff_self from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open private switching_sq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

private def spokePhase {n : ℕ} (sigma : Q n → ℝ) (z : Q n) (a : Fin n) : ℝ :=
  huangMatrix n z (flip z a) * sigma (flip z a)

private lemma square_paths_opposite {n : ℕ} (z : Q n) {a b : Fin n} (hab : a ≠ b) :
    huangMatrix n z (flip z a) * huangMatrix n (flip z a) (flip (flip z a) b) =
      -(huangMatrix n z (flip z b) * huangMatrix n (flip z b) (flip (flip z b) a)) := by
  simpa only [Pi.neg_apply, BalancedCriticalSpectrum.gamma_apply, mul_one] using
    congrFun (BalancedCubeGirth.gamma_anticommute hab (fun _ => (1 : ℝ))) z

private lemma spoke_phase_neg {n : ℕ} {S : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching S sigma) (z : Q n) {a b : Fin n} (hab : a ≠ b)
    (ha : flip z a ∈ S) (hb : flip z b ∈ S) (hm : flip (flip z a) b ∈ S) :
    spokePhase sigma z a = -spokePhase sigma z b := by
  have h := square_paths_opposite z hab
  rw [flip_comm z b a,
    hs.2 _ ha _ hm (BalancedCriticalSpectrum.flip_adj _ b),
    hs.2 _ hb _ hm (by rw [flip_comm z a b]; exact BalancedCriticalSpectrum.flip_adj _ a)] at h
  apply mul_right_cancel₀ (switching_ne_zero hs hm)
  dsimp [spokePhase]
  linear_combination h

private lemma translate_spoke_phase {n : ℕ} {S : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching S sigma) (z : Q n) {a f : Fin n} (haf : a ≠ f)
    (ha : flip z a ∈ S) (hb : flip (flip z f) a ∈ S) :
    spokePhase sigma (flip z f) a =
      -huangMatrix n z (flip z f) * spokePhase sigma z a := by
  let k := huangMatrix n z (flip z f)
  let u := huangMatrix n z (flip z a)
  let v := huangMatrix n (flip z f) (flip (flip z f) a)
  let x := sigma (flip z a)
  let y := sigma (flip (flip z f) a)
  have h := square_paths_opposite z haf
  rw [flip_comm z a f, hs.2 _ ha _ hb
    (by rw [flip_comm z f a]; exact BalancedCriticalSpectrum.flip_adj _ f)] at h
  change u * (x * y) = -(k * v) at h
  have hk : k ^ 2 = 1 :=
    SupportedEigenSaturation.matrix_sq_of_adj (BalancedCriticalSpectrum.flip_adj z f)
  have hy : y ^ 2 = 1 := switching_sq hs hb
  change v * y = -k * (u * x)
  calc
    v * y = v * y * k ^ 2 := by rw [hk, mul_one]
    _ = (k * v) * (k * y) := by ring
    _ = -(u * (x * y)) * (k * y) := by rw [neg_eq_iff_eq_neg.mpr h]
    _ = -k * (u * x) * y ^ 2 := by ring
    _ = _ := by rw [hy, mul_one]

/-- Two consecutive compressed edges at a star make the outer spokes have
equal phase. Edge translation preserves that equality, excluding the far
midpoint between the translated outer endpoints. -/
private lemma translated_far_midpoint_excluded
    {n : ℕ} {S : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching S sigma) (z : Q n) {a b c f : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (haf : a ≠ f) (hcf : c ≠ f)
    (ha : flip z a ∈ S) (hb : flip z b ∈ S) (hc : flip z c ∈ S)
    (habS : flip (flip z a) b ∈ S) (hbcS : flip (flip z b) c ∈ S)
    (hafS : flip (flip z f) a ∈ S) (hcfS : flip (flip z f) c ∈ S) :
    flip (flip (flip z f) a) c ∉ S := by
  intro hm
  have hl := spoke_phase_neg hs z hab ha hb habS
  have hr := spoke_phase_neg hs z hbc hb hc hbcS
  have he : spokePhase sigma z a = spokePhase sigma z c := by linarith
  have ht : spokePhase sigma (flip z f) a = spokePhase sigma (flip z f) c := by
    rw [translate_spoke_phase hs z haf ha hafS, translate_spoke_phase hs z hcf hc hcfS, he]
  have hn := spoke_phase_neg hs (flip z f) hac hafS hcfS hm
  have hz : spokePhase sigma (flip z f) a = 0 := by linarith
  have hsq := SupportedEigenSaturation.matrix_sq_of_adj
    (BalancedCriticalSpectrum.flip_adj (flip z f) a)
  have hmat : huangMatrix n (flip z f) (flip (flip z f) a) ≠ 0 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  exact mul_ne_zero hmat (switching_ne_zero hs hafS) hz

#print axioms translated_far_midpoint_excluded

/-- If a selected point joins the translated opposite spokes, it is the
translated center itself. The other common neighbor has the wrong phase. -/
private lemma translated_opposite_midpoint
    {n : ℕ} {S : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching S sigma) (z : Q n) {a b c f : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (haf : a ≠ f) (hcf : c ≠ f)
    (ha : flip z a ∈ S) (hb : flip z b ∈ S) (hc : flip z c ∈ S)
    (habS : flip (flip z a) b ∈ S) (hbcS : flip (flip z b) c ∈ S)
    (hafS : flip (flip z f) a ∈ S) (hcfS : flip (flip z f) c ∈ S)
    {m : Q n} (hm : m ∈ S)
    (ham : (hypercube n).Adj (flip (flip z f) a) m)
    (hcm : (hypercube n).Adj (flip (flip z f) c) m) : m = flip z f := by
  classical
  by_contra hne
  let u := flip z f
  have hma : a ∈ diff u m ∧ (diff u m).card = 2 :=
    diff_of_adj_flip (Ne.symm hne) a ham
  have hmc : c ∈ diff u m ∧ (diff u m).card = 2 :=
    diff_of_adj_flip (Ne.symm hne) c hcm
  have hdiff : diff u m = {a, c} := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hma.1, hmc.1⟩
    · simp [hac, hma.2]
  have hmfar : m = flip (flip u a) c := by
    apply diff_injective u
    change diff m u = diff (flip (flip u a) c) u
    rw [diff_symm m u, hdiff, diff_flip, diff_flip, diff_self]
    simp [hac, Ne.symm hac, Finset.pair_comm]
  exact translated_far_midpoint_excluded hs z hab hbc hac haf hcf ha hb hc
    habS hbcS hafS hcfS (hmfar ▸ hm)

#print axioms translated_opposite_midpoint
