/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FormalIntervalMomentBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interval correlation estimates control the formal second, cubic and fourth moment values. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.SignedCubeMomentModel

/-! Uniform formal interval moment estimates from centered interval correlations. -/

open scoped BigOperators Topology
open Set Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

def intervalWeight (H : ℝ) (S : Finset ℕ) (a b : ℝ) (d : S) : ℝ :=
  if d.val ∈ points H a b then 1 else 0

def IsIntervalWeight (M H : ℝ) (S : Finset ℕ) (f : S → ℝ) : Prop :=
  ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ M ∧ f = intervalWeight H S a b

private lemma geom_points_inter (H a b c d : ℝ) (hH : 0 ≤ H) :
    points H a b ∩ points H c d = points H (max a c) (max (max a c) (min b d)) := by
  unfold points
  rw [Finset.Ioc_inter_Ioc]
  simp_rw [max_mul_of_nonneg _ _ hH, min_mul_of_nonneg _ _ hH,
    Nat.floor_mono.map_max, Nat.floor_mono.map_min]
  ext n
  simp only [Finset.mem_Ioc]
  omega
private lemma geom_points_card (H a b : ℝ) (hH : 0 ≤ H) (ha : 0 ≤ a) (hab : a ≤ b) :
    |((points H a b).card : ℝ) - H * (b-a)| ≤ 2 := by
  have hf : ⌊a*H⌋₊ ≤ ⌊b*H⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_right hab hH)
  rw [points, Nat.card_Ioc, Nat.cast_sub hf]
  have hfa := Nat.abs_floor_sub_le (mul_nonneg ha hH)
  have hfb := Nat.abs_floor_sub_le (mul_nonneg (ha.trans hab) hH)
  rw [abs_le] at hfa hfb ⊢
  constructor <;> nlinarith
/-- A nonnegative scaled interval in [0, M] contains at most M * H positive integer shifts. -/
lemma geom_points_card_le (M H a b : ℝ) (hH : 0 ≤ H) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ M) :
    ((points H a b).card : ℝ) ≤ M * H := by
  have hf : ⌊a*H⌋₊ ≤ ⌊b*H⌋₊ := Nat.floor_mono (mul_le_mul_of_nonneg_right hab hH)
  rw [points, Nat.card_Ioc, Nat.cast_sub hf]
  have hfb := Nat.floor_le (mul_nonneg (ha.trans hab) hH)
  have hfa : (0 : ℝ) ≤ (⌊a*H⌋₊ : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_right hb hH
  linarith
private lemma geom_indicator_sum (P S : Finset ℕ) (hS : P ⊆ S) :
    (∑ d : S, (if d.val ∈ P then (1 : ℝ) else 0)) = (P.card : ℝ) := by
  classical
  calc
    _ = ∑ n ∈ S, if n ∈ P then (1 : ℝ) else 0 :=
      Finset.sum_coe_sort S (fun n : ℕ => if n ∈ P then (1 : ℝ) else 0)
    _ = _ := by rw [Finset.sum_boole, Finset.filter_mem_eq_of_subset hS]

private lemma geom_overlap_count (H a b c d : ℝ) (S : Finset ℕ)
    (hH : 0 ≤ H) (ha : 0 ≤ a) (_hc : 0 ≤ c)
    (hS : points H a b ∩ points H c d ⊆ S) :
    |indexSum ((fun x : S => if x.val ∈ points H a b then (1 : ℝ) else 0) *
      (fun x : S => if x.val ∈ points H c d then (1 : ℝ) else 0)) -
      H * sigma a b c d| ≤ 2 := by
  have hp : indexSum ((fun x : S => if x.val ∈ points H a b then (1 : ℝ) else 0) *
      (fun x : S => if x.val ∈ points H c d then (1 : ℝ) else 0)) =
      ((points H a b ∩ points H c d).card : ℝ) := by
    rw [indexSum]
    convert geom_indicator_sum (points H a b ∩ points H c d) S hS using 1
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Pi.mul_apply, Finset.mem_inter]
    simpa only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Finset.mem_inter, Pi.one_apply, Pi.mul_apply] using
      (congrFun (Set.inter_indicator_one
        (s := {x : S | x.val ∈ points H a b})
        (t := {x : S | x.val ∈ points H c d}) (M₀ := ℝ)) x).symm
  rw [hp, geom_points_inter H a b c d hH]
  have he : sigma a b c d = max (max a c) (min b d) - max a c := by
    unfold sigma
    simpa using (max_sub_sub_right (max a c) (min b d) (max a c))
  rw [he]
  exact geom_points_card H (max a c) (max (max a c) (min b d)) hH
    (ha.trans (le_max_left a c)) (le_max_left _ _)

lemma geom_product_error (x y A B D H L M : ℝ)
    (hH : 0 ≤ H) (hL : 1 ≤ L) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hx : |x-A| ≤ D*H) (hy : |y-B| ≤ D*H)
    (hA : |A| ≤ M*H*L) (hB : |B| ≤ M*H*L) :
    |x*y-A*B| ≤ (2*M*D+D^2)*H^2*L := by
  have hL0 : 0 ≤ L := by linarith
  have he : x*y-A*B = (x-A)*(y-B) + (x-A)*B + A*(y-B) := by ring
  rw [he]
  calc
    _ ≤ |(x-A)*(y-B)| + |(x-A)*B| + |A*(y-B)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |x-A| * |y-B| + |x-A| * |B| + |A| * |y-B| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ (D*H)*(D*H) + (D*H)*(M*H*L) + (M*H*L)*(D*H) := by
      gcongr
    _ ≤ (2*M*D+D^2)*H^2*L := by
      nlinarith [mul_nonneg (sq_nonneg (D*H)) (sub_nonneg.mpr hL)]


private lemma intervalWeight_mul (H : ℝ) (hH : 0 ≤ H) (S : Finset ℕ) (a b c d : ℝ) :
    intervalWeight H S a b * intervalWeight H S c d =
      intervalWeight H S (max a c) (max (max a c) (min b d)) := by
  funext e
  have hi := geom_points_inter H a b c d hH
  change (if e.val ∈ points H a b then (1:ℝ) else 0) *
    (if e.val ∈ points H c d then (1:ℝ) else 0) = _
  dsimp only [intervalWeight]
  rw [← hi]
  simpa only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Finset.mem_inter, Pi.one_apply, Pi.mul_apply] using
    (congrFun (Set.inter_indicator_one
      (s := {x : S | x.val ∈ points H a b})
      (t := {x : S | x.val ∈ points H c d}) (M₀ := ℝ)) e).symm

lemma IsIntervalWeight.mul {M H : ℝ} {S : Finset ℕ} {f g : S → ℝ}
    (hH : 0 ≤ H) (hf : IsIntervalWeight M H S f) (hg : IsIntervalWeight M H S g) : IsIntervalWeight M H S (f*g) := by
  obtain ⟨a,b,ha,hab,hb,rfl⟩ := hf
  obtain ⟨c,d,hc,hcd,hd,rfl⟩ := hg
  exact ⟨max a c, max (max a c) (min b d), le_max_of_le_left ha,
    le_max_left _ _, max_le (max_le (hab.trans hb) (hcd.trans hd))
      ((min_le_left _ _).trans hb), intervalWeight_mul H hH S a b c d⟩

lemma interval_points_subset {M H a b : ℝ} (hH : 0 ≤ H) (hb : b ≤ M) :
    points H a b ⊆ Finset.Iic ⌊M*H⌋₊ := by
  intro d hd
  exact Finset.mem_Iic.mpr ((Finset.mem_Ioc.mp hd).2.trans
    (Nat.floor_mono (mul_le_mul_of_nonneg_right hb hH)))

lemma distinct_interval_weight_moment (SS : Finset ℕ → ℝ) (M H : ℝ) (hH : 0 ≤ H)
    {k : ℕ} (a b : Fin k → ℝ) (hab : admissible M a b) :
    formalDistinct (fun J : Finset (Finset.Iic ⌊M*H⌋₊) => SS (J.image Subtype.val))
      (fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)) = corr SS H a b := by
  classical
  unfold formalDistinct corr
  simp_rw [intervalWeight, Fintype.prod_boole, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun d _ i => (d i).val)
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hd.2,
      fun i j hij => hd.1 (Subtype.ext hij)⟩
  · intro d hd e he hde
    funext i
    exact Subtype.ext (congrFun hde i)
  · intro d hd
    obtain ⟨hd,hinj⟩ := Finset.mem_filter.mp hd
    have hd := Fintype.mem_piFinset.mp hd
    let e : Fin k → Finset.Iic ⌊M*H⌋₊ :=
      fun i => ⟨d i, interval_points_subset hH (hab i).2.2 (hd i)⟩
    refine ⟨e, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun i j hij => hinj (congrArg Subtype.val hij), hd⟩
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    have hi : (Finset.univ.image d).image Subtype.val =
        Finset.univ.image (fun i => (d i).val) := Finset.image_image
    rw [← hi]
    exact centerFinite_image SS Subtype.val Subtype.val_injective (Finset.univ.image d)

lemma interval_weight_family {M H : ℝ} {k : ℕ} {S : Finset ℕ}
    (f : Fin k → S → ℝ) (hf : ∀ i, IsIntervalWeight M H S (f i)) :
    ∃ a b : Fin k → ℝ, admissible M a b ∧ f = fun i => intervalWeight H S (a i) (b i) := by
  choose a b ha hab hb he using hf
  exact ⟨a,b,fun i => ⟨ha i,hab i,hb i⟩,funext he⟩

lemma sigma_bound {M a b c d : ℝ} (hM : 0 ≤ M)
    (ha : 0 ≤ a) (hb : b ≤ M) (_hc : 0 ≤ c) :
    0 ≤ sigma a b c d ∧ sigma a b c d ≤ M := by
  unfold sigma
  exact ⟨le_max_left _ _, max_le hM (by
    have := min_le_left b d
    have := le_max_left a c
    linarith)⟩

private lemma distinct_two_bound (SS : Finset ℕ → ℝ) (M H L C : ℝ)
    (hM : 1 ≤ M) (hH : 1 ≤ H) (hL : 1 ≤ L) (hlog : Real.log H ≤ L)
    (hC : 0 ≤ C)
    (hc : ∀ a b : Fin 2 → ℝ, admissible M a b →
      |corr SS H a b + H*Real.log H*sigma (a 0) (b 0) (a 1) (b 1)| ≤ C*H)
    (f g : Finset.Iic ⌊M*H⌋₊ → ℝ) (hf : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f)
    (hg : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g) :
    |formalDistinct (fun J => SS (J.image Subtype.val)) ![f,g]| ≤ (C+M)*H*L := by
  obtain ⟨a,b,hab,he⟩ := interval_weight_family ![f,g] (by intro i; fin_cases i <;> assumption)
  rw [he, distinct_interval_weight_moment SS M H (by linarith) a b hab]
  have hs := sigma_bound (d := b 1) (by linarith : 0 ≤ M) (hab 0).1 (hab 0).2.2 (hab 1).1
  have hh : |H*Real.log H*sigma (a 0) (b 0) (a 1) (b 1)| ≤ H*L*M := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) (Real.log_nonneg hH)) hs.1)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hlog (by linarith)) hs.2 hs.1
      (by positivity)
  have ht := abs_sub (corr SS H a b + H*Real.log H*sigma (a 0) (b 0) (a 1) (b 1))
    (H*Real.log H*sigma (a 0) (b 0) (a 1) (b 1))
  rw [add_sub_cancel_right] at ht
  have : C*H ≤ C*H*L := le_mul_of_one_le_right (by positivity) hL
  nlinarith [hc a b hab]

private lemma distinct_three_bound (SS : Finset ℕ → ℝ) (M H L E : ℝ)
    (hH : 1 ≤ H) (_hL : 0 ≤ L) (hlog : Real.log H ≤ L) (hE : 0 ≤ E)
    (hc : ∀ a b : Fin 3 → ℝ, admissible M a b →
      |corr SS H a b| ≤ E*(H*Real.log H)^(3/2 : ℝ))
    (f g h : Finset.Iic ⌊M*H⌋₊ → ℝ)
    (hf : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f)
    (hg : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g)
    (hh : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) h) :
    |formalDistinct (fun J => SS (J.image Subtype.val)) ![f,g,h]| ≤ E*(H*L)^(3/2 : ℝ) := by
  obtain ⟨a,b,hab,he⟩ := interval_weight_family ![f,g,h] (by intro i; fin_cases i <;> assumption)
  rw [he, distinct_interval_weight_moment SS M H (by linarith) a b hab]
  exact (hc a b hab).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (mul_nonneg (by linarith) (Real.log_nonneg hH))
      (mul_le_mul_of_nonneg_left hlog (by linarith)) (by norm_num)) hE)

private lemma distinct_four_bound (SS : Finset ℕ → ℝ) (M H E : ℝ) (hH : 0 ≤ H)
    (hc : ∀ a b : Fin 4 → ℝ, admissible M a b →
      |corr SS H a b - pairCorr SS H a b| ≤ E)
    (f g h q : Finset.Iic ⌊M*H⌋₊ → ℝ)
    (hf : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f)
    (hg : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g)
    (hh : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) h)
    (hq : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) q) :
    |formalDistinct (fun J => SS (J.image Subtype.val)) ![f,g,h,q] -
      perfectPairingSum (fun u v => formalDistinct (fun J => SS (J.image Subtype.val))
        ![u,v]) f g h q| ≤ E := by
  obtain ⟨a,b,hab,he⟩ := interval_weight_family ![f,g,h,q] (by intro i; fin_cases i <;> assumption)
  have hv : ∀ i, (![f,g,h,q] : Fin 4 → _) i = intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i) :=
    fun i => congrFun he i
  have hp (i j : Fin 4) : admissible M ![a i,a j] ![b i,b j] := by
    intro t; fin_cases t <;> simpa using hab _
  have htwo (i j : Fin 4) :
      formalDistinct (fun J => SS (J.image Subtype.val))
        ![intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i), intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a j) (b j)] =
      corr SS H ![a i,a j] ![b i,b j] := by
    convert distinct_interval_weight_moment SS M H hH ![a i,a j] ![b i,b j] (hp i j) using 1
    congr 1
    funext t; fin_cases t <;> rfl
  have hh4 := distinct_interval_weight_moment SS M H hH a b hab
  rw [← he] at hh4
  rw [hh4]
  have h0 : f = intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a 0) (b 0) := hv 0
  have h1 : g = intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a 1) (b 1) := hv 1
  have h2 : h = intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a 2) (b 2) := hv 2
  have h3 : q = intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a 3) (b 3) := hv 3
  simpa only [perfectPairingSum, h0,h1,h2,h3, htwo, pairCorr] using hc a b hab

lemma index_interval_weight_bound {M H : ℝ} (hH : 0 ≤ H)
    (f : Finset.Iic ⌊M*H⌋₊ → ℝ) (hf : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f) :
    |indexSum f| ≤ M*H := by
  obtain ⟨a,b,ha,hab,hb,rfl⟩ := hf
  unfold indexSum
  simp only [intervalWeight]
  rw [geom_indicator_sum _ _ (interval_points_subset hH hb), abs_of_nonneg (by positivity)]
  exact geom_points_card_le M H a b hH ha hab hb

private lemma cubic_bound (SS : Finset ℕ → ℝ) (M H L s K E : ℝ)
    (hs : s ≠ 0) (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (_hK : 0 ≤ K) (_hE : 0 ≤ E)
    (ha : |s-2| ≤ 3*L) (hb : |s-1| ≤ 3*L)
    (B : ∀ f g, IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f →
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g →
      |formalDistinct (fun J => SS (J.image Subtype.val)) ![f,g]| ≤ K*H*L)
    (T : ∀ f g h, IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f →
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g → IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) h →
      |formalDistinct (fun J => SS (J.image Subtype.val)) ![f,g,h]| ≤ E*(H*L)^(3/2:ℝ))
    (f g h : Finset.Iic ⌊M*H⌋₊ → ℝ)
    (hf : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f)
    (hg : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g)
    (hh : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) h) :
    |formalMoment (fun J => SS (J.image Subtype.val)) s ![f,g,h]| ≤
      E*(H*L)^(3/2:ℝ) + (9*K+9*M)*H*L^2 := by
  have hp : |formalDistinct (fun J => SS (J.image Subtype.val)) ![f*g,h] +
      formalDistinct (fun J => SS (J.image Subtype.val)) ![f*h,g] +
      formalDistinct (fun J => SS (J.image Subtype.val)) ![g*h,f]| ≤ 3*K*H*L := by
    grw [abs_add_le, abs_add_le, B _ _ (hf.mul hH hg) hh,
      B _ _ (hf.mul hH hh) hg, B _ _ (hg.mul hH hh) hf]
    ring_nf; rfl
  have hd := index_interval_weight_bound hH (f*g*h) ((hf.mul hH hg).mul hH hh)
  rw [formal_third_moment_eq _ s hs (by simpa using hSS) (by intro d; simpa using hSS1 d.val)]
  calc
    _ ≤ E*(H*L)^(3/2:ℝ) + (3*L)*(3*K*H*L) + (3*L)*(3*L)*(M*H) := by
      grw [abs_add_le, abs_add_le, abs_mul, abs_mul, abs_mul,
        T _ _ _ hf hg hh, ha, hb, hp, hd]
    _ = _ := by ring

private lemma cubic_scale_bound {H L : ℝ} (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hLH : L ≤ H) :
    (H*L)^(3/2 : ℝ) ≤ H^2*L := by
  have hp : 0 < H*L := by positivity
  have hs : Real.sqrt (H*L) ≤ H := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  calc
    (H*L)^(3/2 : ℝ) = (H*L) * Real.sqrt (H*L) := by
      rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hp,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    _ ≤ (H*L)*H := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

private lemma fourth_scalar_bound {H L E K J a b base rep pair triple T : ℝ}
    (hH : 1 ≤ H) (hL : 1 ≤ L) (hsq : L^2 ≤ H)
    (hE : 0 ≤ E) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (ha : |a| ≤ 3*L) (hb : |b| ≤ 3*L)
    (hbase : |base| ≤ E*H^2*L^2)
    (hrep : |rep| ≤ 6*E*(H*L)^(3/2 : ℝ))
    (hpair : |pair| ≤ 3*K*H*L)
    (htriple : |triple| ≤ 4*K*H*L)
    (hT : |T| ≤ J*H) :
    |base + a*rep + a^2*pair + (a^2-2*b)*triple + (a^2*b-2*b^2)*T| ≤
      (1000*(K+J+1))*(E*H^2*L^2 + H^2*L) := by
  have hH0 : 0 ≤ H := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hLH : L ≤ H := by nlinarith
  have hscale := cubic_scale_bound hH hL hLH
  have ha2 : |a^2| ≤ 9*L^2 := by
    rw [abs_pow]
    nlinarith [abs_nonneg a]
  have hc : |a^2-2*b| ≤ 15*L^2 := by
    calc
      _ ≤ |a^2| + |2*b| := abs_sub _ _
      _ ≤ 9*L^2 + 2*(3*L) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact add_le_add ha2 (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ ≤ _ := by nlinarith
  have hd : |a^2*b-2*b^2| ≤ 45*L^3 := by
    calc
      _ ≤ |a^2*b| + |2*b^2| := abs_sub _ _
      _ = |a^2| * |b| + 2* |b|^2 := by rw [abs_mul, abs_mul, abs_pow]; norm_num
      _ ≤ (9*L^2)*(3*L) + 2*(3*L)^2 := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL)]
  have hr : |a*rep| ≤ 18*E*H^2*L^2 := by
    calc
      _ = |a| * |rep| := abs_mul _ _
      _ ≤ (3*L)*(6*E*(H*L)^(3/2 : ℝ)) := mul_le_mul ha hrep (abs_nonneg _) (by positivity)
      _ ≤ (3*L)*(6*E*(H^2*L)) := by gcongr
      _ = _ := by ring
  have hp : |a^2*pair| ≤ 27*K*H^2*L := by
    calc
      _ = |a^2| * |pair| := abs_mul _ _
      _ ≤ (9*L^2)*(3*K*H*L) := mul_le_mul ha2 hpair (abs_nonneg _) (by positivity)
      _ = 27*K*H*L*L^2 := by ring
      _ ≤ 27*K*H*L*H := by gcongr
      _ = _ := by ring
  have ht : |(a^2-2*b)*triple| ≤ 60*K*H^2*L := by
    calc
      _ = |a^2-2*b| * |triple| := abs_mul _ _
      _ ≤ (15*L^2)*(4*K*H*L) := mul_le_mul hc htriple (abs_nonneg _) (by positivity)
      _ = 60*K*H*L*L^2 := by ring
      _ ≤ 60*K*H*L*H := by gcongr
      _ = _ := by ring
  have hlast : |(a^2*b-2*b^2)*T| ≤ 45*J*H^2*L := by
    calc
      _ = |a^2*b-2*b^2| * |T| := abs_mul _ _
      _ ≤ (45*L^3)*(J*H) := mul_le_mul hd hT (abs_nonneg _) (by positivity)
      _ = 45*J*H*L*L^2 := by ring
      _ ≤ 45*J*H*L*H := by gcongr
      _ = _ := by ring
  have ht₁ := abs_add_le base (a*rep)
  have ht₂ := abs_add_le (base+a*rep) (a^2*pair)
  have ht₃ := abs_add_le (base+a*rep+a^2*pair) ((a^2-2*b)*triple)
  have ht₄ := abs_add_le (base+a*rep+a^2*pair+(a^2-2*b)*triple) ((a^2*b-2*b^2)*T)
  have hsum : |base + a*rep + a^2*pair + (a^2-2*b)*triple + (a^2*b-2*b^2)*T| ≤
      19*(E*H^2*L^2) + (87*K+45*J)*(H^2*L) := by linarith
  have hmass : 0 ≤ E*H^2*L^2 := by positivity
  have hmass₂ : 0 ≤ H^2*L := by positivity
  calc
    _ ≤ 19*(E*H^2*L^2) + (87*K+45*J)*(H^2*L) := hsum
    _ ≤ (1000*(K+J+1))*(E*H^2*L^2) + (1000*(K+J+1))*(H^2*L) := by
      gcongr <;> linarith
    _ = _ := by ring
private theorem scalar_bounds (α β : ℝ) (hα : 0 < α) (hβ : β < 1) :
    ∀ᶠ N : ℝ in atTop, ∀ H s : ℝ, N ^ α ≤ H → H ≤ N ^ β →
      Real.log N ≤ s → s ≤ Real.log N + Real.log 2 →
      2 ≤ H ∧ 1 ≤ Real.log N ∧ Real.log H ≤ Real.log N ∧
      |s - 2| ≤ 3 * Real.log N ∧ |s - 1| ≤ 3 * Real.log N ∧
      (Real.log N)^2 ≤ H ∧ Real.log N ≤ H := by
  have hg := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hα).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hα).eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop 1, hg] with N hN hpow hL hlog H s hlo hhi hs₁ hs₂
  have hH : 2 ≤ H := hpow.trans hlo
  have hHN : H ≤ N := hhi.trans (Real.rpow_le_self_of_one_le hN hβ.le)
  have hlogH : Real.log H ≤ Real.log N := Real.log_le_log (by linarith) hHN
  have hsq : (Real.log N)^2 ≤ H := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.rpow_two] at hlog
    exact hlog.trans hlo
  have hlog2 : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  refine ⟨hH, hL, hlogH, ?_, ?_, hsq, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith
  · nlinarith
private lemma fourth_bound (SS : Finset ℕ → ℝ) (M H L s K E : ℝ)
    (hs : s ≠ 0) (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hM : 0 ≤ M) (hH : 1 ≤ H) (hL : 1 ≤ L) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hsq : L^2 ≤ H) (ha : |s-2| ≤ 3*L) (hb : |s-1| ≤ 3*L)
    (B : ∀ f g, IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f →
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g →
      |formalDistinct (fun J => SS (J.image Subtype.val)) ![f,g]| ≤ K*H*L)
    (T : ∀ f g h, IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f →
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g → IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) h →
      |formalDistinct (fun J => SS (J.image Subtype.val)) ![f,g,h]| ≤ E*(H*L)^(3/2:ℝ))
    (F : ∀ f g h q, IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f →
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g → IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) h →
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) q →
      |formalDistinct (fun J => SS (J.image Subtype.val)) ![f,g,h,q] -
        perfectPairingSum (fun u v => formalDistinct (fun J => SS (J.image Subtype.val))
          ![u,v]) f g h q| ≤ E*H^2*L^2)
    (f g h q : Finset.Iic ⌊M*H⌋₊ → ℝ)
    (hf : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f)
    (hg : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g)
    (hh : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) h)
    (hq : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) q) :
    |formalMoment (fun J => SS (J.image Subtype.val)) s ![f,g,h,q] -
      perfectPairingSum (fun u v => formalMoment (fun J => SS (J.image Subtype.val))
        s ![u,v]) f g h q| ≤ 1000*(K+M+1)*(E*H^2*L^2 + H^2*L) := by
  have hH0 : 0 ≤ H := by linarith
  have hr : |repeatedPairSum (fun u v w => formalDistinct
      (fun J => SS (J.image Subtype.val)) ![u,v,w]) f g h q| ≤ 6*E*(H*L)^(3/2:ℝ) := by
    unfold repeatedPairSum
    grw [abs_add_le,abs_add_le,abs_add_le,abs_add_le,abs_add_le,
      T _ _ _ (hf.mul hH0 hg) hh hq, T _ _ _ (hf.mul hH0 hh) hg hq,
      T _ _ _ (hf.mul hH0 hq) hg hh, T _ _ _ (hg.mul hH0 hh) hf hq,
      T _ _ _ (hg.mul hH0 hq) hf hh, T _ _ _ (hh.mul hH0 hq) hf hg]
    ring_nf; rfl
  have hp : |pairPairSum (fun u v => formalDistinct
      (fun J => SS (J.image Subtype.val)) ![u,v]) f g h q| ≤ 3*K*H*L := by
    unfold pairPairSum
    grw [abs_add_le,abs_add_le,
      B _ _ (hf.mul hH0 hg) (hh.mul hH0 hq),
      B _ _ (hf.mul hH0 hh) (hg.mul hH0 hq),
      B _ _ (hf.mul hH0 hq) (hg.mul hH0 hh)]
    ring_nf; rfl
  have ht : |tripleSingletonSum (fun u v => formalDistinct
      (fun J => SS (J.image Subtype.val)) ![u,v]) f g h q| ≤ 4*K*H*L := by
    unfold tripleSingletonSum
    grw [abs_add_le,abs_add_le,abs_add_le,
      B _ _ ((hg.mul hH0 hh).mul hH0 hq) hf,
      B _ _ ((hf.mul hH0 hh).mul hH0 hq) hg,
      B _ _ ((hf.mul hH0 hg).mul hH0 hq) hh,
      B _ _ ((hf.mul hH0 hg).mul hH0 hh) hq]
    ring_nf; rfl
  rw [formal_fourth_pairing_defect _ s hs (by simpa using hSS)
    (by intro d; simpa using hSS1 d.val)]
  exact fourth_scalar_bound hH hL hsq hE hK hM ha hb (F _ _ _ _ hf hg hh hq)
    hr hp ht (index_interval_weight_bound hH0 _ (((hf.mul hH0 hg).mul hH0 hh).mul hH0 hq))

private lemma second_approx (SS : Finset ℕ → ℝ) (M H L s C : ℝ)
    (hs : s ≠ 0) (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hM : 1 ≤ M) (hH : 1 ≤ H) (hL : 1 ≤ L) (hLH : L ≤ H)
    (hb : |s-1| ≤ 3*L)
    (hc : ∀ a b : Fin 2 → ℝ, admissible M a b →
      |corr SS H a b + H*Real.log H*sigma (a 0) (b 0) (a 1) (b 1)| ≤ C*H)
    (a b c d : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbM : b ≤ M)
    (hc0 : 0 ≤ c) (hcd : c ≤ d) (hdM : d ≤ M) :
    |formalMoment (fun J : Finset (Finset.Iic ⌊M*H⌋₊) => SS (J.image Subtype.val)) s
      ![intervalWeight H (Finset.Iic ⌊M*H⌋₊) a b, intervalWeight H (Finset.Iic ⌊M*H⌋₊) c d] -
      H*(s-Real.log H)*sigma a b c d| ≤ (C+M+6)*H := by
  have hH0 : 0 ≤ H := by linarith
  have had : admissible M ![a,c] ![b,d] := by
    intro i; fin_cases i
    · exact ⟨ha,hab,hbM⟩
    · exact ⟨hc0,hcd,hdM⟩
  have hr := distinct_interval_weight_moment SS M H hH0 ![a,c] ![b,d] had
  have he : (fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (![a,c] i) (![b,d] i)) =
      ![intervalWeight H (Finset.Iic ⌊M*H⌋₊) a b, intervalWeight H (Finset.Iic ⌊M*H⌋₊) c d] := by
    funext i; fin_cases i <;> rfl
  rw [he] at hr
  have hcount := geom_overlap_count H a b c d (Finset.Iic ⌊M*H⌋₊) hH0 ha hc0
    (fun n hn => interval_points_subset hH0 hbM (Finset.mem_inter.mp hn).1)
  change |indexSum (intervalWeight H (Finset.Iic ⌊M*H⌋₊) a b *
    intervalWeight H (Finset.Iic ⌊M*H⌋₊) c d) - H*sigma a b c d| ≤ 2 at hcount
  have hsigma := sigma_bound (d := d) (by linarith : 0 ≤ M) ha hbM hc0
  rw [formal_second_moment_eq _ s hs (by simpa using hSS)
    (by intro e; simpa using hSS1 e.val), hr]
  have heq : corr SS H ![a,c] ![b,d] + (s-1)*indexSum
      (intervalWeight H (Finset.Iic ⌊M*H⌋₊) a b * intervalWeight H (Finset.Iic ⌊M*H⌋₊) c d) -
      H*(s-Real.log H)*sigma a b c d =
      (corr SS H ![a,c] ![b,d]+H*Real.log H*sigma a b c d) +
      (s-1)*(indexSum (intervalWeight H (Finset.Iic ⌊M*H⌋₊) a b *
        intervalWeight H (Finset.Iic ⌊M*H⌋₊) c d)-H*sigma a b c d) - H*sigma a b c d := by ring
  rw [heq]
  have hc' : |corr SS H ![a,c] ![b,d]+H*Real.log H*sigma a b c d| ≤ C*H :=
    hc ![a,c] ![b,d] had
  calc
    _ ≤ C*H + (3*L)*2 + H*M := by
      grw [abs_sub, abs_add_le, abs_mul, abs_mul, hc', hb,
        hcount, abs_of_nonneg hH0, abs_of_nonneg hsigma.1, hsigma.2]
    _ ≤ _ := by nlinarith

/-- The quadratic formal value has the variance size uniformly on the length band. -/
theorem formal_interval_second_bound (SS : Finset ℕ → ℝ) (α β M : ℝ)
    (hα : 0 < α) (hβ : β < 1) (hSS : SS ∅ = 1)
    (hSS1 : ∀ d, SS {d} = 1) (hcor : IntervalCorrelations SS) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℝ in atTop,
      ∀ H s : ℝ, N ^ α ≤ H → H ≤ N ^ β →
      Real.log N ≤ s → s ≤ Real.log N + Real.log 2 →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ M →
        |Phi SS H s (fun _ : Fin 2 => a) (fun _ => b)| ≤ C * H * Real.log N := by
  obtain ⟨C, hC, hc, _⟩ := hcor M hM
  refine ⟨C + 3 * M + 6, by positivity, ?_⟩
  filter_upwards [scalar_bounds α β hα hβ] with N hN H s hlo hhi hslo hshi a b ha hab hb
  obtain ⟨hH, hL, hlogH, _, hsb, _, hLH⟩ := hN H s hlo hhi hslo hshi
  have hH1 : 1 ≤ H := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hs : s ≠ 0 := by linarith
  have hlogH0 : 0 ≤ Real.log H := Real.log_nonneg hH1
  have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hsd : |s - Real.log H| ≤ 2 * Real.log N := by
    rw [abs_le]; constructor <;> linarith
  have hsig := sigma_bound (d := b) (by linarith : 0 ≤ M) ha hb ha
  have heq : (fun i : Fin 2 => intervalWeight H (Finset.Iic ⌊M*H⌋₊) a b) =
      ![intervalWeight H (Finset.Iic ⌊M*H⌋₊) a b,
        intervalWeight H (Finset.Iic ⌊M*H⌋₊) a b] := by
    funext i; fin_cases i <;> rfl
  change (fun (_ : Fin 2) (d : Finset.Iic ⌊M*H⌋₊) =>
    if d.val ∈ points H a b then (1 : ℝ) else 0) = _ at heq
  rw [Phi_eq_formalMoment SS H s _ _ _
    (fun _ => interval_points_subset hH0 hb), heq]
  have he := second_approx SS M H (Real.log N) s C hs hSS hSS1 hM hH1 hL hLH hsb
    (hc H hH1) a b a b ha hab hb ha hab hb
  have hmain : |H * (s - Real.log H) * sigma a b a b| ≤ 2 * M * H * Real.log N := by
    rw [abs_mul, abs_mul, abs_of_nonneg hH0, abs_of_nonneg hsig.1]
    calc
      _ ≤ H * (2 * Real.log N) * M :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsd hH0) hsig.2 hsig.1 (by positivity)
      _ = _ := by ring
  have ht := abs_sub_le
    (formalMoment (fun J : Finset (Finset.Iic ⌊M*H⌋₊) => SS (J.image Subtype.val)) s
      ![intervalWeight H (Finset.Iic ⌊M*H⌋₊) a b,
        intervalWeight H (Finset.Iic ⌊M*H⌋₊) a b])
    (H * (s - Real.log H) * sigma a b a b) 0
  simp only [sub_zero] at ht
  have hrem : (C + M + 6) * H ≤ (C + M + 6) * H * Real.log N :=
    le_mul_of_one_le_right (by positivity) hL
  nlinarith

private lemma pairing_approx (SS : Finset ℕ → ℝ) (M H L s C : ℝ)
    (hs : s ≠ 0) (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1)
    (hM : 1 ≤ M) (hH : 1 ≤ H) (hL : 1 ≤ L) (hLH : L ≤ H)
    (hC : 0 ≤ C) (hlog : Real.log H ≤ L) (hslo : L ≤ s) (hshi : s ≤ L+1)
    (hb : |s-1| ≤ 3*L)
    (hc : ∀ a b : Fin 2 → ℝ, admissible M a b →
      |corr SS H a b + H*Real.log H*sigma (a 0) (b 0) (a 1) (b 1)| ≤ C*H)
    (a b : Fin 4 → ℝ) (hab : admissible M a b) :
    |perfectPairingSum (fun u v => formalMoment
        (fun J : Finset (Finset.Iic ⌊M*H⌋₊) => SS (J.image Subtype.val)) s ![u,v])
      (intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a 0) (b 0))
      (intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a 1) (b 1))
      (intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a 2) (b 2))
      (intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a 3) (b 3)) -
      H^2*(s-Real.log H)^2*W4 a b| ≤
      3*(4*M*(C+M+6)+(C+M+6)^2)*H^2*L := by
  let V (i j : Fin 4) := formalMoment
    (fun J : Finset (Finset.Iic ⌊M*H⌋₊) => SS (J.image Subtype.val)) s
    ![intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i),intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a j) (b j)]
  let A (i j : Fin 4) := H*(s-Real.log H)*sigma (a i) (b i) (a j) (b j)
  have hv (i j : Fin 4) : |V i j-A i j| ≤ (C+M+6)*H :=
    second_approx SS M H L s C hs hSS hSS1 hM hH hL hLH hb hc
      _ _ _ _ (hab i).1 (hab i).2.1 (hab i).2.2 (hab j).1 (hab j).2.1 (hab j).2.2
  have hA (i j : Fin 4) : |A i j| ≤ (2*M)*H*L := by
    have ht := sigma_bound (d := b j) (by linarith : 0 ≤ M)
      (hab i).1 (hab i).2.2 (hab j).1
    have hlH : 0 ≤ Real.log H := Real.log_nonneg hH
    dsimp only [A]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) ht.1)]
    calc
      _ ≤ H*(2*L)*M := by gcongr <;> linarith
      _ = _ := by ring
  have hp (i j k l : Fin 4) : |V i j*V k l-A i j*A k l| ≤
      (4*M*(C+M+6)+(C+M+6)^2)*H^2*L := by
    convert geom_product_error (V i j) (V k l) (A i j) (A k l) (C+M+6) H L (2*M)
      (by linarith) hL (by positivity) (by linarith) (hv i j) (hv k l) (hA i j) (hA k l)
      using 1
    ring
  have he : H^2*(s-Real.log H)^2*W4 a b = A 0 1*A 2 3+A 0 2*A 1 3+A 0 3*A 1 2 := by
    dsimp [A,W4]; ring
  rw [he]
  change |(V 0 1*V 2 3+V 0 2*V 1 3+V 0 3*V 1 2) - _| ≤ _
  rw [show (V 0 1*V 2 3+V 0 2*V 1 3+V 0 3*V 1 2) -
      (A 0 1*A 2 3+A 0 2*A 1 3+A 0 3*A 1 2) =
      (V 0 1*V 2 3-A 0 1*A 2 3)+(V 0 2*V 1 3-A 0 2*A 1 3)+
      (V 0 3*V 1 2-A 0 3*A 1 2) by ring]
  grw [abs_add_le,abs_add_le,hp 0 1 2 3,hp 0 2 1 3,hp 0 3 1 2]
  ring_nf; rfl

/-- Uniform cubic and fourth formal interval moment bounds on a polynomial length band. -/
theorem formal_interval_moment_bounds (SS : Finset ℕ → ℝ) (α β : ℝ)
    (hα : 0 < α) (_hαβ : α < β) (hβ : β < 1)
    (hSS : SS ∅ = 1) (hSS1 : ∀ d, SS {d} = 1) (hcor : IntervalCorrelations SS)
    (M : ℝ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ η : ℝ → ℝ,
      (∀ H, 0 ≤ η H) ∧ AntitoneOn η (Ici 2) ∧ Tendsto η atTop (nhds 0) ∧
      ∀ᶠ N : ℝ in atTop, ∀ H s : ℝ, N^α ≤ H → H ≤ N^β →
        Real.log N ≤ s → s ≤ Real.log N+Real.log 2 →
        (∀ a b : Fin 3 → ℝ, admissible M a b →
          |Phi SS H s a b| ≤ C*(η H*(H*Real.log N)^(3/2:ℝ)+H*(Real.log N)^2)) ∧
        (∀ a b : Fin 4 → ℝ, admissible M a b →
          |Phi SS H s a b-H^2*(s-Real.log H)^2*W4 a b| ≤
            C*(η H*H^2*(Real.log N)^2+H^2*Real.log N)) := by
  obtain ⟨C,hC,hc2,η,hη,hmono,hlim,hc3,hc4,_⟩ := hcor M hM
  let K := C+M
  let P := 3*(4*M*(C+M+6)+(C+M+6)^2)
  let Q := 1000*(K+M+1)+P+9*K+9*M+1
  have hM0 : 0 ≤ M := by linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨Q,hQ,η,hη,hmono,hlim,?_⟩
  filter_upwards [scalar_bounds α β hα hβ] with N hN H s hlo hhi hslo hshi
  obtain ⟨hH2,hL,hlog,ha,hb,hsq,hLH⟩ := hN H s hlo hhi hslo hshi
  have hH : 1 ≤ H := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hL0 : 0 ≤ Real.log N := by linarith
  have hlH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hs : s ≠ 0 := by linarith
  have hηH := hη H
  have B := distinct_two_bound SS M H (Real.log N) C hM hH hL hlog hC
    (hc2 H hH)
  have T := distinct_three_bound SS M H (Real.log N) (η H) hH hL0 hlog (hη H)
    (hc3 H hH2)
  have F := distinct_four_bound SS M H (η H*H^2*(Real.log N)^2) hH0 (by
    intro a b hab
    exact (hc4 H hH2 a b hab).trans (by gcongr))
  constructor
  · intro a b hab
    let f := fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)
    have hf (i) : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) (f i) :=
      ⟨a i,b i,(hab i).1,(hab i).2.1,(hab i).2.2,rfl⟩
    have he : (fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)) = ![f 0,f 1,f 2] := by
      funext i; fin_cases i <;> rfl
    change (fun i (d : Finset.Iic ⌊M*H⌋₊) =>
      if d.val ∈ points H (a i) (b i) then (1:ℝ) else 0) = _ at he
    rw [Phi_eq_formalMoment SS H s a b _ (fun i => interval_points_subset hH0 (hab i).2.2),he]
    have ht := cubic_bound SS M H (Real.log N) s K (η H) hs hSS hSS1
      hH0 hL0 hK (hη H) ha hb B T _ _ _ (hf 0) (hf 1) (hf 2)
    refine ht.trans ?_
    have hA : 0 ≤ η H*(H*Real.log N)^(3/2:ℝ) := by positivity
    have hD : 0 ≤ H*(Real.log N)^2 := by positivity
    dsimp only [Q]
    nlinarith [mul_nonneg hP hD, mul_nonneg hK hD, mul_nonneg hM0 hD,
      mul_nonneg hP hA, mul_nonneg hK hA, mul_nonneg hM0 hA]
  · intro a b hab
    let f := fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)
    have hf (i) : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) (f i) :=
      ⟨a i,b i,(hab i).1,(hab i).2.1,(hab i).2.2,rfl⟩
    have he : (fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)) = ![f 0,f 1,f 2,f 3] := by
      funext i; fin_cases i <;> rfl
    change (fun i (d : Finset.Iic ⌊M*H⌋₊) =>
      if d.val ∈ points H (a i) (b i) then (1:ℝ) else 0) = _ at he
    rw [Phi_eq_formalMoment SS H s a b _ (fun i => interval_points_subset hH0 (hab i).2.2),he]
    have ht := fourth_bound SS M H (Real.log N) s K (η H) hs hSS hSS1 hM0
      hH hL hK (hη H) hsq ha hb B T F _ _ _ _ (hf 0) (hf 1) (hf 2) (hf 3)
    have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
    have hp := pairing_approx SS M H (Real.log N) s C hs hSS hSS1 hM hH hL hLH
      hC hlog hslo (by linarith) hb (hc2 H hH) a b hab
    have hsplt := abs_sub_le
      (formalMoment (fun J : Finset (Finset.Iic ⌊M*H⌋₊) => SS (J.image Subtype.val)) s ![f 0,f 1,f 2,f 3])
      (perfectPairingSum (fun u v => formalMoment (fun J => SS (J.image Subtype.val)) s ![u,v])
        (f 0) (f 1) (f 2) (f 3))
      (H^2*(s-Real.log H)^2*W4 a b)
    have hA : 0 ≤ η H*H^2*(Real.log N)^2 := by positivity
    have hD : 0 ≤ H^2*Real.log N := by positivity
    have hp' : |perfectPairingSum (fun u v => formalMoment
        (fun J : Finset (Finset.Iic ⌊M*H⌋₊) => SS (J.image Subtype.val)) s ![u,v])
        (f 0) (f 1) (f 2) (f 3)-H^2*(s-Real.log H)^2*W4 a b| ≤ P*H^2*Real.log N := hp
    dsimp only [Q]
    nlinarith [mul_nonneg hP hA, mul_nonneg hK hD, mul_nonneg hM0 hD,
      mul_nonneg hK hA, mul_nonneg hM0 hA]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
