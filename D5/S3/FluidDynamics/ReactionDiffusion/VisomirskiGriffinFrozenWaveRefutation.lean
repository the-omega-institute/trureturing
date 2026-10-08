/- GID: D5/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/ReactionDiffusion/VisomirskiGriffinFrozenWaveRefutation
   mirror-E: none(waiver:analytic-evolution)
   anchors: []
   utility: none
   digest: Diffusion erases the parity niches of the biased spatial replicator. -/

/-
result: proof_shape: content; escape_witness: solution_pair; consumer: settling result.
admission_basis: open-problem-resolution (#14205; Refuted)
Direct frozen dependencies: none on the baseline. PeriodicAllenCahnDecay is a same-delivery prerequisite.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay

noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter MeasureTheory
open D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay
namespace D5.S3.FluidDynamics.ReactionDiffusion.VisomirskiGriffinFrozenWaveRefutation

variable {ι : Type*} [Fintype ι]

def biasedMatrix (n : ℕ) (a : ℝ) : Matrix (Fin (2*n)) (Fin (2*n)) ℝ :=
  fun i j => if j = (i - (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) then 1+a else if j = (i + (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) then -1 else 0

def reaction (n : ℕ) (a : ℝ) (z : Fin (2*n) → ℝ) (i : Fin (2*n)) : ℝ :=
  z i * ((biasedMatrix n a).mulVec z i - dotProduct z ((biasedMatrix n a).mulVec z))


def initialData (n : ℕ) (i : Fin (2*n)) (x : ℝ) : ℝ :=
  if i.val % 2 = 0 then (1+Real.sin x)/(2*(n:ℝ)) else (1-Real.sin x)/(2*(n:ℝ))

def equilibrium (n : ℕ) : ℝ := 1/(2*(n:ℝ))

structure ClassicalSolution (n : ℕ) (a D : ℝ) (u : Fin (2*n) → ℝ → ℝ → ℝ) : Prop where
  continuous : ∀ i, ContinuousOn (fun z : ℝ × ℝ => u i z.1 z.2) (Ici 0 ×ˢ univ)
  periodic : ∀ i t, 0 ≤ t → Function.Periodic (u i t) (2*Real.pi)
  time_deriv : ∀ i t x, 0 < t → HasDerivAt (fun s => u i s x) ((deriv (fun s => u i s x) t)) t
  space_deriv : ∀ i t x, 0 < t → HasDerivAt (u i t) ((deriv (u i t) x)) x
  space_deriv2 : ∀ i t x, 0 < t → HasDerivAt ((deriv (u i t))) ((deriv (deriv (u i t)) x)) x
  continuous_dt : ∀ i, ContinuousOn (fun z : ℝ × ℝ => (deriv (fun s => u i s z.2) z.1)) (Ioi 0 ×ˢ univ)
  continuous_dx : ∀ i, ContinuousOn (fun z : ℝ × ℝ => (deriv (u i z.1) z.2)) (Ioi 0 ×ˢ univ)
  continuous_dxx : ∀ i, ContinuousOn (fun z : ℝ × ℝ => (deriv (deriv (u i z.1)) z.2)) (Ioi 0 ×ˢ univ)
  equation : ∀ i t x, 0 < t → (deriv (fun s => u i s x) t) = reaction n a (fun j => u j t x) i + D*(deriv (deriv (u i t)) x)
  initial : ∀ i x, u i 0 x = initialData n i x

def distanceSq (f g : ℝ → ℝ) : ℝ := energy (fun _ x => f x-g x) 0

def Homogenizes (n : ℕ) (u : Fin (2*n) → ℝ → ℝ → ℝ) : Prop :=
  ∀ i, Tendsto (fun t => distanceSq (u i t) (fun _ => equilibrium n)) atTop (𝓝 0)

def FrozenWaveLimit (n : ℕ) (u : Fin (2*n) → ℝ → ℝ → ℝ)
    (v : Fin (2*n) → ℝ → ℝ) : Prop :=
  (∀ i, Continuous (v i)) ∧
  (∀ i, Function.Periodic (v i) (2*Real.pi)) ∧
  (∃ i x, v i x ≠ equilibrium n) ∧
  (∀ i, Tendsto (fun t => distanceSq (u i t) (v i)) atTop (𝓝 0))

def claim : Prop := ∀ (n : ℕ), 2 ≤ n → ∃ u v,
  ClassicalSolution n (-(1:ℝ)/2) ((1:ℝ)/100) u ∧ FrozenWaveLimit n u v

private lemma periodic_representative {f : ℝ → ℝ} (hp : Function.Periodic f (2*Real.pi)) (x : ℝ) :
    ∃ y ∈ Icc (-Real.pi) Real.pi, f y = f x := by
  have hP : 0 < 2*Real.pi := by positivity
  let y := toIocMod hP (-Real.pi) x
  have hy := toIocMod_mem_Ioc hP (-Real.pi) x
  have heq : -Real.pi+2*Real.pi = Real.pi := by ring
  rw [heq] at hy
  refine ⟨y,⟨hy.1.le,hy.2⟩,?_⟩
  dsimp [y]
  rw [←self_sub_toIocDiv_zsmul hP (-Real.pi) x]
  exact hp.sub_zsmul_eq _

private lemma distanceSq_pos_of_ne {f : ℝ → ℝ} {c : ℝ} (hc : Continuous f)
    (hp : Function.Periodic f (2*Real.pi)) (hne : ∃ x, f x ≠ c) :
    0 < distanceSq f (fun _ => c) := by
  rcases hne with ⟨x,hx⟩
  rcases periodic_representative hp x with ⟨y,hy,heq⟩
  apply intervalIntegral.integral_pos (by linarith [Real.pi_pos])
    ((hc.sub continuous_const).pow 2).continuousOn
  · intro y _; exact sq_nonneg (f y-c)
  · exact ⟨y,hy,sq_pos_of_ne_zero (sub_ne_zero.mpr (heq.symm ▸ hx))⟩

private lemma distanceSq_triangle {f g h : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) :
    distanceSq f h ≤ 2*distanceSq f g+2*distanceSq g h := by
  have H : ∀ x : ℝ, (f x-h x)^2 ≤ 2*(f x-g x)^2+2*(g x-h x)^2 := by
    intro x
    nlinarith [sq_nonneg ((f x-g x)-(g x-h x))]
  have hfg : IntervalIntegrable (fun x => (f x-g x)^2) volume (-Real.pi) Real.pi := ((hf.sub hg).pow 2).intervalIntegrable _ _
  have hgh : IntervalIntegrable (fun x => (g x-h x)^2) volume (-Real.pi) Real.pi := ((hg.sub hh).pow 2).intervalIntegrable _ _
  unfold distanceSq energy
  calc
    _ ≤ ∫ x in -Real.pi..Real.pi, 2*(f x-g x)^2+2*(g x-h x)^2 :=
      intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
        (((hf.sub hh).pow 2).intervalIntegrable _ _)
        ((hfg.const_mul 2).add (hgh.const_mul 2)) (fun x _ => H x)
    _ = _ := by rw [intervalIntegral.integral_add (hfg.const_mul 2) (hgh.const_mul 2),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

private lemma distanceSq_symm (f g : ℝ → ℝ) : distanceSq f g = distanceSq g f := by
  unfold distanceSq
  apply intervalIntegral.integral_congr
  intro x _
  ring

private lemma homogenizes_excludes_frozen {n : ℕ} {a D : ℝ} {u}
    (hu : ClassicalSolution n a D u) (hh : Homogenizes n u) :
    ¬ ∃ v, FrozenWaveLimit n u v := by
  rintro ⟨v,hvc,hvp,⟨i,x,hx⟩,hlim⟩
  have hiu : ∀ t, 0 ≤ t → Continuous (u i t) := by
    intro t ht
    exact continuousOn_univ.mp (slice_continuousOn (hu.continuous i) ht)
  have hbound : ∀ᶠ t in atTop,
      distanceSq (v i) (fun _ => equilibrium n) ≤
        2*distanceSq (u i t) (v i)+2*distanceSq (u i t) (fun _ => equilibrium n) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    have H := distanceSq_triangle (h := fun _ => equilibrium n) (hvc i) (hiu t ht) continuous_const
    rw [distanceSq_symm (v i) (u i t)] at H
    exact H
  have htend : Tendsto (fun t => 2*distanceSq (u i t) (v i)+
      2*distanceSq (u i t) (fun _ => equilibrium n)) atTop (𝓝 0) := by
    convert! ((hlim i).const_mul 2).add ((hh i).const_mul 2) using 1 <;> norm_num
  have hle : distanceSq (v i) (fun _ => equilibrium n) ≤ 0 := ge_of_tendsto htend hbound
  have hpos := distanceSq_pos_of_ne (hvc i) (hvp i) ⟨x,hx⟩
  linarith


private theorem family_implies_not_claim (hfamily : ∀ (n : ℕ) (a D : ℝ), 2 ≤ n → -1 < a → a ≤ 0 →
  0 < D → 0 ≤ 2*(n:ℝ)*D+a → ∀ u, ClassicalSolution n a D u → Homogenizes n u) : ¬ claim := by
  intro hc
  rcases hc 25 (by norm_num) with ⟨u,v,hu,hv⟩
  have hh := hfamily 25 (-1/2) (1/100) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) u hu
  exact homogenizes_excludes_frozen hu hh ⟨v,hv⟩

private def vectorEnergy (w : ι → ℝ → ℝ → ℝ) (t : ℝ) := ∑ i, energy (w i) t

private lemma component_regular {n a D u} (h : ClassicalSolution n a D u) (i : Fin (2*n)) :
    ScalarRegular (u i) := by
  exact ⟨h.continuous i,h.periodic i,h.time_deriv i,h.space_deriv i,h.space_deriv2 i,
    h.continuous_dt i,h.continuous_dx i,h.continuous_dxx i⟩

private lemma vectorEnergy_continuous {w : ι → ℝ → ℝ → ℝ} (hr : ∀ i, ScalarRegular (w i)) :
    ContinuousOn (vectorEnergy w) (Ici 0) := by
  classical
  exact continuousOn_finsetSum _ (fun i _ => (hr i).energy_continuous)

private lemma vectorEnergy_nonnegative (w : ι → ℝ → ℝ → ℝ) (t : ℝ) : 0 ≤ vectorEnergy w t :=
  Finset.sum_nonneg (fun i _ => energy_nonnegative (w i) t)

private lemma vectorEnergy_eq_integral {w : ι → ℝ → ℝ → ℝ} (hr : ∀ i, ScalarRegular (w i))
    {t : ℝ} (ht : 0 ≤ t) : vectorEnergy w t = ∫ x in -Real.pi..Real.pi, ∑ i, (w i t x)^2 := by
  classical
  symm
  apply intervalIntegral.integral_finsetSum
  intro i _
  exact ((hr i).slice_continuous ht).pow 2 |>.intervalIntegrable _ _

private lemma vectorEnergy_deriv {w Q : ι → ℝ → ℝ → ℝ} (hr : ∀ i, ScalarRegular (w i))
    {t D : ℝ} (ht : 0 < t) (hQ : ∀ i, Continuous (Q i t))
    (he : ∀ i x, (deriv (fun s => (w i) s x) t) = D*(deriv (deriv ((w i) t)) x)+Q i t x) :
    HasDerivAt (vectorEnergy w)
      (∑ i, (2*(∫ x in -Real.pi..Real.pi, w i t x*Q i t x)-
        2*D*(∫ x in -Real.pi..Real.pi, ((deriv ((w i) t) x))^2))) t := by
  classical
  exact HasDerivAt.fun_sum (fun i _ => pde_energy_deriv (hr i) ht (Q i t) (hQ i) (he i))

private lemma vector_energy_bound {w Q : ι → ℝ → ℝ → ℝ} (hr : ∀ i, ScalarRegular (w i))
    {t D K : ℝ} (ht : 0 < t) (hD : 0 ≤ D) (hQ : ∀ i, Continuous (Q i t))
    (hb : ∀ x ∈ Icc (-Real.pi) Real.pi, (∑ i, w i t x*Q i t x) ≤ K*(∑ i, (w i t x)^2)) :
    (∑ i, (2*(∫ x in -Real.pi..Real.pi, w i t x*Q i t x)-
      2*D*(∫ x in -Real.pi..Real.pi, ((deriv ((w i) t) x))^2))) ≤ 2*K*vectorEnergy w t := by
  classical
  have hprod : ∀ i, IntervalIntegrable (fun x => w i t x*Q i t x) volume (-Real.pi) Real.pi := by
    intro i
    exact (((hr i).slice_continuous ht.le).mul (hQ i)).intervalIntegrable _ _
  have hsq : ∀ i, IntervalIntegrable (fun x => (w i t x)^2) volume (-Real.pi) Real.pi := by
    intro i
    exact (((hr i).slice_continuous ht.le).pow 2).intervalIntegrable _ _
  have H : (∑ i, ∫ x in -Real.pi..Real.pi, w i t x*Q i t x) ≤ K*vectorEnergy w t := by
    rw [← intervalIntegral.integral_finsetSum (fun i _ => hprod i),vectorEnergy_eq_integral hr ht.le,
      ← intervalIntegral.integral_const_mul]
    have hpi : IntervalIntegrable (fun x => ∑ i, w i t x*Q i t x) volume (-Real.pi) Real.pi := by
      convert! IntervalIntegrable.sum Finset.univ (fun i _ => hprod i) using 1
      funext x
      simp
    have hsi : IntervalIntegrable (fun x => ∑ i, (w i t x)^2) volume (-Real.pi) Real.pi := by
      convert! IntervalIntegrable.sum Finset.univ (fun i _ => hsq i) using 1
      funext x
      simp
    exact intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hpi (hsi.const_mul K) hb
  have hneg : 0 ≤ ∑ i, (∫ x in -Real.pi..Real.pi, ((deriv ((w i) t) x))^2) := by
    apply Finset.sum_nonneg
    intro i _
    exact intervalIntegral.integral_nonneg_of_forall (by linarith [Real.pi_pos]) (fun _ => sq_nonneg _)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]
  nlinarith

private lemma vector_energy_zero_implies_zero {w : ι → ℝ → ℝ → ℝ} (hr : ∀ i, ScalarRegular (w i))
    {t : ℝ} (ht : 0 ≤ t) (hz : vectorEnergy w t = 0) : ∀ i x, w i t x = 0 := by
  classical
  intro i x
  have hei : energy (w i) t = 0 := by
    have H := Finset.single_le_sum (fun j _ => energy_nonnegative (w j) t) (Finset.mem_univ i)
    change energy (w i) t ≤ vectorEnergy w t at H
    rw [hz] at H
    exact le_antisymm H (energy_nonnegative _ _)
  by_contra hne
  have hpos := distanceSq_pos_of_ne ((hr i).slice_continuous ht) ((hr i).periodic t ht) ⟨x,hne⟩
  have heq : distanceSq (w i t) (fun _ => 0) = energy (w i) t := by simp [distanceSq, energy]
  rw [heq,hei] at hpos
  linarith

private lemma matrix_reaction_equivariant {n : ℕ} {a : ℝ} (e : Fin (2*n) ≃ Fin (2*n))
    (hA : ∀ i j, biasedMatrix n a (e i) (e j) = biasedMatrix n a i j)
    (z : Fin (2*n) → ℝ) (i : Fin (2*n)) :
    reaction n a (fun j => z (e j)) i = reaction n a z (e i) := by
  have hmul : ∀ i, (biasedMatrix n a).mulVec (fun j => z (e j)) i =
      (biasedMatrix n a).mulVec z (e i) := by
    intro i
    unfold Matrix.mulVec dotProduct
    exact Fintype.sum_equiv e _ _ (fun j => by change biasedMatrix n a i j * z (e j) = biasedMatrix n a (e i) (e j) * z (e j); exact congrArg (fun r : ℝ => r*z (e j)) (hA i j).symm)
  have hdot : dotProduct (fun j => z (e j)) ((biasedMatrix n a).mulVec (fun j => z (e j))) =
      dotProduct z ((biasedMatrix n a).mulVec z) := by
    unfold dotProduct
    exact Fintype.sum_equiv e _ _ (fun j => by rw [hmul j])
  unfold reaction
  rw [hmul i,hdot]

private lemma prev_eq_sub {n : ℕ} (hn : 2 ≤ n) (i : Fin (2*n)) :
    letI : NeZero (2*n) := ⟨by omega⟩
    (i - (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) = i-1 := by
  letI : NeZero (2*n) := ⟨by omega⟩
  rfl

private lemma next_eq_add {n : ℕ} (hn : 2 ≤ n) (i : Fin (2*n)) :
    letI : NeZero (2*n) := ⟨by omega⟩
    (i + (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) = i+1 := by
  letI : NeZero (2*n) := ⟨by omega⟩
  rfl

private lemma cycle_matrix_equivariant {n : ℕ} (hn : 2 ≤ n) (a : ℝ) (k : Fin (2*n)) :
    ∀ i j, biasedMatrix n a (finCycle k i) (finCycle k j) = biasedMatrix n a i j := by
  letI : NeZero (2*n) := ⟨by omega⟩
  intro i j
  unfold biasedMatrix
  simp only [finCycle_apply, prev_eq_sub hn, next_eq_add hn]
  have hprev : (i+k)-1 = (i-1)+k := by abel
  simp only [hprev, add_right_comm i k 1, add_right_cancel_iff]

private lemma cycle_val_parity {n : ℕ} (hn : 2 ≤ n) (i k : Fin (2*n)) :
    (finCycle k i).val % 2 = (i.val+k.val)%2 := by
  simp only [finCycle_apply, Fin.val_add]
  exact Nat.mod_mod_of_dvd _ (by use n)

private lemma initial_cycle_two {n : ℕ} (hn : 2 ≤ n) (i : Fin (2*n)) (x : ℝ) :
    initialData n (finCycle ⟨2,by omega⟩ i) x = initialData n i x := by
  unfold initialData
  rw [cycle_val_parity hn]
  simp

private lemma contDiff_reaction (n : ℕ) (a : ℝ) :
    ContDiff ℝ 1 (fun z : Fin (2*n) → ℝ => reaction n a z) := by
  apply contDiff_pi.mpr
  intro i
  unfold reaction Matrix.mulVec dotProduct
  fun_prop

private lemma pi_norm_sq_le_sum_sq {ι : Type*} [Fintype ι] (z : ι → ℝ) :
    ‖z‖^2 ≤ ∑ i, (z i)^2 := by
  classical
  have hsum : 0 ≤ ∑ i, (z i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : ‖z‖ ≤ Real.sqrt (∑ i, (z i)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    have hi : (z i)^2 ≤ ∑ j, (z j)^2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    exact (Real.le_sqrt (abs_nonneg _) hsum).mpr (by simpa only [sq_abs] using hi)
  have H := pow_le_pow_left₀ (norm_nonneg z) hn 2
  rwa [Real.sq_sqrt hsum] at H

private lemma lipschitz_reaction_energy {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ι → ℝ}
    {s : Set (ι → ℝ)} {L : ℝ≥0} (hL : LipschitzOnWith L F s)
    {z v : ι → ℝ} (hz : z ∈ s) (hv : v ∈ s) :
    (∑ i, (z i-v i)*(F z i-F v i)) ≤
      (Fintype.card ι:ℝ)*L*(∑ i, (z i-v i)^2) := by
  classical
  have hdiff : ‖F z-F v‖ ≤ L*‖z-v‖ := by
    simpa only [dist_eq_norm] using hL.dist_le_mul z hz v hv
  have hterm : ∀ i, (z i-v i)*(F z i-F v i) ≤ (L:ℝ)*‖z-v‖^2 := by
    intro i
    have hi : |z i-v i| ≤ ‖z-v‖ := by simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (z-v) i
    have hri : |F z i-F v i| ≤ L*‖z-v‖ := by
      have H : |F z i-F v i| ≤ ‖F z-F v‖ := by
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (F z-F v) i
      exact H.trans hdiff
    calc
      (z i-v i)*(F z i-F v i) ≤ |(z i-v i)*(F z i-F v i)| := le_abs_self _
      _ = |z i-v i| *|F z i-F v i| := abs_mul _ _
      _ ≤ ‖z-v‖*((L:ℝ)*‖z-v‖) := mul_le_mul hi hri (abs_nonneg _) (norm_nonneg _)
      _ = (L:ℝ)*‖z-v‖^2 := by ring
  calc
    (∑ i, (z i-v i)*(F z i-F v i)) ≤ ∑ _i : ι, (L:ℝ)*‖z-v‖^2 :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Fintype.card ι:ℝ)*L*‖z-v‖^2 := by simp; ring
    _ ≤ (Fintype.card ι:ℝ)*L*(∑ i, (z i-v i)^2) := by
      exact mul_le_mul_of_nonneg_left (pi_norm_sq_le_sum_sq (z-v)) (by positivity)

private lemma reaction_lipschitz_ball (n : ℕ) (a M : ℝ) : ∃ L : ℝ≥0,
    LipschitzOnWith L (fun z : Fin (2*n) → ℝ => reaction n a z) (Metric.closedBall 0 M) := by
  exact (contDiff_reaction n a).contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : Fin (2*n) → ℝ) M) (isCompact_closedBall _ _)

private lemma classical_bounded_on_strip {n a D u} (hu : ClassicalSolution n a D u) {T : ℝ}
    (hT : 0 ≤ T) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ∀ x ∈ Icc (-Real.pi) Real.pi,
      ‖(fun i => u i t x)‖ ≤ M := by
  have hc : ContinuousOn (fun z : ℝ × ℝ => fun i => u i z.1 z.2)
      (Icc 0 T ×ˢ Icc (-Real.pi) Real.pi) := by
    apply continuousOn_pi.mpr
    intro i
    exact (hu.continuous i).mono (fun z hz => ⟨hz.1.1,mem_univ _⟩)
  rcases (isCompact_Icc.prod isCompact_Icc).bddAbove_image hc.norm with ⟨M,hM⟩
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro t ht x hx
  exact (hM ⟨(t,x),⟨ht,hx⟩,rfl⟩).trans (le_max_left _ _)

private lemma difference_equation {n a D u v} (hu : ClassicalSolution n a D u)
    (hv : ClassicalSolution n a D v) (i : Fin (2*n)) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (deriv (fun s => (fun t x => u i t x-v i t x) s x) t) =
      D*(deriv (deriv ((fun t x => u i t x-v i t x) t)) x)+
        (reaction n a (fun j => u j t x) i-reaction n a (fun j => v j t x) i) := by
  have eT : (deriv (fun s => (fun t x => u i t x-v i t x) s x) t) = (deriv (fun s => u i s x) t)-(deriv (fun s => v i s x) t) := by
    exact ((hu.time_deriv i t x ht).sub (hv.time_deriv i t x ht)).deriv
  have eX : (deriv ((fun t x => u i t x-v i t x) t)) = fun x => (deriv (u i t) x)-(deriv (v i t) x) := by
    funext x
    exact ((hu.space_deriv i t x ht).sub (hv.space_deriv i t x ht)).deriv
  have eXX : (deriv (deriv ((fun t x => u i t x-v i t x) t)) x) = (deriv (deriv (u i t)) x)-(deriv (deriv (v i t)) x) := by
    rw [eX]
    exact ((hu.space_deriv2 i t x ht).sub (hv.space_deriv2 i t x ht)).deriv
  rw [eT,eXX,hu.equation i t x ht,hv.equation i t x ht]
  ring

/-- Uniqueness uses only finite-time bounds and nonnegative diffusion. -/

private theorem classical_unique {n a D u v} (hD : 0 ≤ D) (hu : ClassicalSolution n a D u)
    (hv : ClassicalSolution n a D v) : ∀ i t x, 0 ≤ t → u i t x = v i t x := by
  classical
  intro i T x hT
  let w := fun i t x => u i t x-v i t x
  let Q := fun i t x => reaction n a (fun j => u j t x) i-reaction n a (fun j => v j t x) i
  have hr : ∀ i, ScalarRegular (w i) := fun i => (component_regular hu i).sub (component_regular hv i)
  have hQc : ∀ t, 0 < t → ∀ i, Continuous (Q i t) := by
    intro t ht i
    have hcU : Continuous (fun x => fun j => u j t x) := continuous_pi (fun j => (component_regular hu j).slice_continuous ht.le)
    have hcV : Continuous (fun x => fun j => v j t x) := continuous_pi (fun j => (component_regular hv j).slice_continuous ht.le)
    exact ((continuous_apply i).comp ((contDiff_reaction n a).continuous.comp hcU)).sub
      ((continuous_apply i).comp ((contDiff_reaction n a).continuous.comp hcV))
  rcases classical_bounded_on_strip hu hT with ⟨Mu,hMu,hbu⟩
  rcases classical_bounded_on_strip hv hT with ⟨Mv,hMv,hbv⟩
  rcases reaction_lipschitz_ball n a (max Mu Mv) with ⟨L,hL⟩
  let K : ℝ := (Fintype.card (Fin (2*n)):ℝ)*L
  let E' := fun t => ∑ j, (2*(∫ x in -Real.pi..Real.pi, w j t x*Q j t x)-
    2*D*(∫ x in -Real.pi..Real.pi, ((deriv ((w j) t) x))^2))
  have hder : ∀ t ∈ Ioo 0 T, HasDerivAt (vectorEnergy w) (E' t) t := by
    intro t ht
    exact vectorEnergy_deriv hr ht.1 (hQc t ht.1) (fun j x => difference_equation hu hv j ht.1 x)
  have hbound : ∀ t ∈ Ioo 0 T, E' t ≤ (2*K)*vectorEnergy w t := by
    intro t ht
    apply vector_energy_bound hr ht.1 hD (hQc t ht.1)
    intro x hx
    have hzu : (fun j => u j t x) ∈ Metric.closedBall 0 (max Mu Mv) := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using (hbu t ⟨ht.1.le,ht.2.le⟩ x hx).trans (le_max_left Mu Mv)
    have hzv : (fun j => v j t x) ∈ Metric.closedBall 0 (max Mu Mv) := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using (hbv t ⟨ht.1.le,ht.2.le⟩ x hx).trans (le_max_right Mu Mv)
    exact lipschitz_reaction_energy hL hzu hzv
  have h0 : vectorEnergy w 0 = 0 := by
    unfold vectorEnergy energy
    have hw0 : ∀ j x, w j 0 x = 0 := by
      intro j x; dsimp [w]; rw [hu.initial j x,hv.initial j x]; ring
    simp only [hw0, zero_pow (by decide : 2 ≠ 0), intervalIntegral.integral_zero, Finset.sum_const_zero]
  have hEzero := energy_zero_of_gronwall
    ((vectorEnergy_continuous hr).mono (fun t ht => ht.1)) hder hbound h0
    (fun t _ => vectorEnergy_nonnegative w t) T ⟨hT,le_rfl⟩
  have H := vector_energy_zero_implies_zero hr hT hEzero i x
  exact sub_eq_zero.mp H

private lemma solution_permute {n a D u} (hu : ClassicalSolution n a D u)
    (e : Fin (2*n) ≃ Fin (2*n))
    (hA : ∀ i j, biasedMatrix n a (e i) (e j) = biasedMatrix n a i j)
    (hinit : ∀ i x, initialData n (e i) x = initialData n i x) :
    ClassicalSolution n a D (fun i t x => u (e i) t x) := by
  refine ⟨(fun i => hu.continuous (e i)),(fun i => hu.periodic (e i)),
    (fun i => hu.time_deriv (e i)),(fun i => hu.space_deriv (e i)),
    (fun i => hu.space_deriv2 (e i)),(fun i => hu.continuous_dt (e i)),
    (fun i => hu.continuous_dx (e i)),(fun i => hu.continuous_dxx (e i)),?_,?_⟩
  · intro i t x ht
    change (deriv (fun s => u (e i) s x) t) = reaction n a (fun j => u (e j) t x) i+D*(deriv (deriv (u (e i) t)) x)
    rw [matrix_reaction_equivariant e hA (fun j => u j t x) i]
    exact hu.equation (e i) t x ht
  · intro i x
    rw [hu.initial,hinit]

private lemma initial_cycle_one_reflect {n : ℕ} (hn : 2 ≤ n) (i : Fin (2*n)) (x : ℝ) :
    initialData n (finCycle ⟨1,by omega⟩ i) (-x) = initialData n i x := by
  unfold initialData
  rw [cycle_val_parity hn]
  simp only [Fin.val_mk, Real.sin_neg]
  have hmod := Nat.mod_lt i.val (by decide : 0 < 2)
  have hm : (i.val+1)%2 = (i.val%2+1)%2 := by omega
  rw [hm]
  interval_cases h : i.val%2 <;> simp [h, sub_eq_add_neg]

private lemma solution_reflect_permute {n a D u} (hu : ClassicalSolution n a D u)
    (e : Fin (2*n) ≃ Fin (2*n))
    (hA : ∀ i j, biasedMatrix n a (e i) (e j) = biasedMatrix n a i j)
    (hinit : ∀ i x, initialData n (e i) (-x) = initialData n i x) :
    ClassicalSolution n a D (fun i t x => u (e i) t (-x)) := by
  let v := fun i t x => u (e i) t (-x)
  have hr : ∀ i, ScalarRegular (v i) := fun i => (component_regular hu (e i)).reflect
  refine ⟨(fun i => (hr i).continuous),(fun i => (hr i).periodic),
    (fun i => (hr i).time_deriv),(fun i => (hr i).space_deriv),
    (fun i => (hr i).space_deriv2),(fun i => (hr i).continuous_dt),
    (fun i => (hr i).continuous_dx),(fun i => (hr i).continuous_dxx),?_,?_⟩
  · intro i t x ht
    have hT : (deriv (fun s => v i s x) t) = (deriv (fun s => u (e i) s (-x)) t) := (hu.time_deriv (e i) t (-x) ht).deriv
    have hX : (deriv (v i t)) = fun x => -(deriv (u (e i) t) (-x)) := by
      funext x
      have H : HasDerivAt (v i t) (-(deriv (u (e i) t) (-x))) x := by
        convert! (hu.space_deriv (e i) t (-x) ht).comp x (hasDerivAt_neg x) using 1 <;> simp
      exact H.deriv
    have hXX : (deriv (deriv (v i t)) x) = (deriv (deriv (u (e i) t)) (-x)) := by
      rw [hX]
      have H : HasDerivAt (fun x => -(deriv (u (e i) t) (-x))) ((deriv (deriv (u (e i) t)) (-x))) x := by
        convert! ((hu.space_deriv2 (e i) t (-x) ht).comp x (hasDerivAt_neg x)).neg using 1 <;> simp
      exact H.deriv
    change (deriv (fun s => v i s x) t) = reaction n a (fun j => v j t x) i+D*(deriv (deriv (v i t)) x)
    rw [hT,hXX]
    dsimp [v]
    rw [matrix_reaction_equivariant e hA (fun j => u j t (-x)) i]
    exact hu.equation (e i) t (-x) ht
  · intro i x
    rw [hu.initial,hinit]

private lemma shift_two_invariant {n a D u} (hn : 2 ≤ n) (hD : 0 ≤ D) (hu : ClassicalSolution n a D u) :
    ∀ i t x, 0 ≤ t → u (finCycle ⟨2,by omega⟩ i) t x = u i t x := by
  have hv := solution_permute hu (finCycle ⟨2,by omega⟩) (cycle_matrix_equivariant hn a _)
    (initial_cycle_two hn)
  exact classical_unique hD hv hu

private lemma reflection_invariant {n a D u} (hn : 2 ≤ n) (hD : 0 ≤ D) (hu : ClassicalSolution n a D u) :
    ∀ i t x, 0 ≤ t → u (finCycle ⟨1,by omega⟩ i) t (-x) = u i t x := by
  have hv := solution_reflect_permute hu (finCycle ⟨1,by omega⟩) (cycle_matrix_equivariant hn a _)
    (initial_cycle_one_reflect hn)
  exact classical_unique hD hv hu

private lemma parity_of_shift_two {n : ℕ} (hn : 2 ≤ n) (z : Fin (2*n) → ℝ)
    (hs : ∀ i, z (finCycle ⟨2,by omega⟩ i) = z i) (i : Fin (2*n)) :
    z i = if i.val%2 = 0 then z ⟨0,by omega⟩ else z ⟨1,by omega⟩ := by
  have h : ∀ m, ∀ hm : m < 2*n,
      z ⟨m,hm⟩ = if m%2=0 then z ⟨0,by omega⟩ else z ⟨1,by omega⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases hm0 : m=0
      · subst m; simp
      by_cases hm1 : m=1
      · subst m; simp
      have hm2 : 2 ≤ m := by omega
      let j : Fin (2*n) := ⟨m-2,by omega⟩
      have heq : finCycle ⟨2,by omega⟩ j = (⟨m,hm⟩ : Fin (2*n)) := by
        apply Fin.ext
        simp only [finCycle_apply, Fin.val_add, Fin.val_mk, j]
        rw [Nat.sub_add_cancel hm2,Nat.mod_eq_of_lt hm]
      have hp : (m-2)%2 = m%2 := by omega
      rw [←heq,hs j,ih (m-2) (by omega) (by omega),hp]
  exact h i.val i.isLt

private lemma neighbor_parity {n : ℕ} (hn : 2 ≤ n) (i : Fin (2*n)) :
    ((i - (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n)))).val%2 = (i.val+1)%2 ∧ ((i + (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n)))).val%2 = (i.val+1)%2 := by
  have hpos : 0 < 2*n := by omega
  have hprev : (i.val+2*n-1)%2 = (i.val+1)%2 := by omega
  constructor
  · simp only [Fin.val_sub, Fin.val_mk]
    rw [Nat.mod_eq_of_lt (show 1 < 2*n by omega)]
    rw [Nat.mod_mod_of_dvd _ (by use n)]
    omega
  · simp only [Fin.val_add, Fin.val_mk]
    rw [Nat.mod_eq_of_lt (show 1 < 2*n by omega)]
    exact Nat.mod_mod_of_dvd _ (by use n)

private lemma prev_ne_next {n : ℕ} (hn : 2 ≤ n) (i : Fin (2*n)) : (i - (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) ≠ (i + (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) := by
  letI : NeZero (2*n) := ⟨by omega⟩
  rw [prev_eq_sub hn,next_eq_add hn]
  intro h
  have H := congrArg (fun j => j-i+1) h
  have Ha : i-1-i+1 = 0 := by abel
  have Hb : i+1-i+1 = (1 : Fin (2*n))+1 := by abel
  rw [Ha,Hb] at H
  have hv1 : (1 : Fin (2*n)).val = 1 := by
    simp [Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2*n by omega)]
  have Hv := congrArg Fin.val H
  change 0 = ((1 : Fin (2*n)).val+(1 : Fin (2*n)).val) % (2*n) at Hv
  rw [hv1,Nat.mod_eq_of_lt (show 1+1 < 2*n by omega)] at Hv
  omega

private lemma mulVec_biased {n : ℕ} (hn : 2 ≤ n) (a : ℝ) (z : Fin (2*n) → ℝ) (i : Fin (2*n)) :
    (biasedMatrix n a).mulVec z i = (1+a)*z ((i - (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))))-z ((i + (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n)))) := by
  have hne := prev_ne_next hn i
  unfold Matrix.mulVec dotProduct biasedMatrix
  have heq : (fun j => (if j=(i - (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) then 1+a else if j=(i + (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) then -1 else 0)*z j) =
      fun j => (if j=(i - (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) then (1+a)*z ((i - (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n)))) else 0)+
        (if j=(i + (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) then -z ((i + (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n)))) else 0) := by
    funext j
    split_ifs <;> simp_all
  change (∑ j, (if j=(i - (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) then 1+a else if j=(i + (⟨1 % (2*n), Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (2*n))) then -1 else 0)*z j) = _
  rw [heq,Finset.sum_add_distrib]
  simp [sub_eq_add_neg]

private lemma parity_reaction {n : ℕ} (hn : 2 ≤ n) (a p q : ℝ) (i : Fin (2*n)) :
    reaction n a (fun j => if j.val%2=0 then p else q) i =
      if i.val%2=0 then a*p*q*(1-2*(n:ℝ)*p) else a*p*q*(1-2*(n:ℝ)*q) := by
  let z : Fin (2*n) → ℝ := fun j => if j.val%2=0 then p else q
  have hvec : ∀ j, (biasedMatrix n a).mulVec z j = if j.val%2=0 then a*q else a*p := by
    intro j
    rw [mulVec_biased hn]
    dsimp [z]
    rw [(neighbor_parity hn j).1,(neighbor_parity hn j).2]
    have hmod := Nat.mod_lt j.val (by decide : 0 < 2)
    have hm : (j.val+1)%2 = (j.val%2+1)%2 := by omega
    rw [hm]
    interval_cases h : j.val%2 <;> simp [h] <;> ring
  have hdot : dotProduct z ((biasedMatrix n a).mulVec z) = 2*(n:ℝ)*a*p*q := by
    unfold dotProduct
    have hterm : ∀ j, z j*((biasedMatrix n a).mulVec z j) = a*p*q := by
      intro j
      rw [hvec j]
      dsimp [z]
      split_ifs <;> ring
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    ring
  change z i*((biasedMatrix n a).mulVec z i-dotProduct z ((biasedMatrix n a).mulVec z)) = _
  rw [hvec i,hdot]
  dsimp [z]
  split_ifs <;> ring

private theorem scalar_linear_zero {w B : ℝ → ℝ → ℝ} {D : ℝ} (hr : ScalarRegular w) (hD : 0 ≤ D)
    (hB : ContinuousOn B.uncurry (Ici 0 ×ˢ univ))
    (he : ∀ t x, 0 < t → (deriv (fun s => w s x) t) = D*(deriv (deriv (w t)) x)+B t x*w t x)
    (h0 : ∀ x, w 0 x=0) : ∀ t x, 0 ≤ t → w t x=0 := by
  intro T x hT
  have hBc : ∀ t, 0 ≤ t → Continuous (B t) := by
    intro t ht
    exact continuousOn_univ.mp (slice_continuousOn hB ht)
  have hc : ContinuousOn B.uncurry (Icc 0 T ×ˢ Icc (-Real.pi) Real.pi) :=
    hB.mono (fun z hz => ⟨hz.1.1,mem_univ _⟩)
  rcases (isCompact_Icc.prod isCompact_Icc).bddAbove_image hc with ⟨K,hK⟩
  let E' := fun t => 2*(∫ x in -Real.pi..Real.pi, w t x*(B t x*w t x))-
    2*D*(∫ x in -Real.pi..Real.pi, ((deriv (w t) x))^2)
  have hder : ∀ t ∈ Ioo 0 T, HasDerivAt (energy w) (E' t) t := by
    intro t ht
    exact pde_energy_deriv hr ht.1 (fun x => B t x*w t x)
      ((hBc t ht.1.le).mul (hr.slice_continuous ht.1.le)) (he t · ht.1)
  have hb : ∀ t ∈ Ioo 0 T, E' t ≤ (2*K)*energy w t := by
    intro t ht
    have H := vector_energy_bound (ι := Unit) (w := fun _ => w) (Q := fun _ t x => B t x*w t x)
      (fun _ => hr) ht.1 hD
      (fun _ => (hBc t ht.1.le).mul (hr.slice_continuous ht.1.le))
      (K := K) (by
        intro x hx
        have H : B t x ≤ K := hK ⟨(t,x),⟨⟨ht.1.le,ht.2.le⟩,hx⟩,rfl⟩
        simp only [Fintype.sum_unique]
        nlinarith [mul_nonneg (sub_nonneg.mpr H) (sq_nonneg (w t x))])
    simpa only [Fintype.sum_unique,vectorEnergy] using H
  have hinit : energy w 0 = 0 := by simp [energy, h0]
  have hzero := energy_zero_of_gronwall (hr.energy_continuous.mono (fun t ht => ht.1))
    hder hb hinit (fun t _ => energy_nonnegative _ _) T ⟨hT,le_rfl⟩
  by_contra hne
  have hpos := distanceSq_pos_of_ne (hr.slice_continuous hT) (hr.periodic T hT) ⟨x,hne⟩
  have heq : distanceSq (w T) (fun _ => 0) = energy w T := by simp [distanceSq, energy]
  rw [heq,hzero] at hpos
  linarith

private lemma scalar_pair_algebra {n : ℝ} (hn : n ≠ 0) (a p q : ℝ) (hs : p+q=1/n) :
    n*(a*p*q*(1-2*n*p)-a*p*q*(1-2*n*q)) =
      (-a/(2*n))*(n*(p-q)-(n*(p-q))^3) := by
  have H : n*(p+q)=1 := by rw [hs]; field_simp
  have H2 := congrArg (fun r : ℝ => r^2) H
  have H4 : 4*n^2*p*q = 1-(n*(p-q))^2 := by nlinarith [H2]
  calc
    _ = (-a/2)*(p-q)*(4*n^2*p*q) := by ring
    _ = (-a/2)*(p-q)*(1-(n*(p-q))^2) := by rw [H4]
    _ = _ := by field_simp [hn] <;> ring

private lemma pair_components_algebra {n : ℝ} (hn : n ≠ 0) (p q : ℝ) (hs : p+q=1/n) :
    p-1/(2*n) = (n*(p-q))/(2*n) ∧ q-1/(2*n) = -(n*(p-q))/(2*n) := by
  have H : n*(p+q)=1 := by rw [hs]; field_simp
  constructor <;> field_simp <;> linarith

private lemma homogenizes_of_parity_scalar {n : ℕ} (hn : 2 ≤ n)
    (u : Fin (2*n) → ℝ → ℝ → ℝ) (p q : ℝ → ℝ → ℝ)
    (hpair : ∀ t x, 0 ≤ t → p t x+q t x=1/(n:ℝ))
    (hcomp : ∀ i t x, 0 ≤ t → u i t x=if i.val%2=0 then p t x else q t x)
    (hdecay : Tendsto (energy (fun t x => (n:ℝ)*(p t x-q t x))) atTop (𝓝 0)) :
    Homogenizes n u := by
  have hnr : (n:ℝ) ≠ 0 := by positivity
  intro i
  have hlim := hdecay.const_mul ((1/(2*(n:ℝ)))^2)
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  unfold distanceSq equilibrium energy
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [hcomp i t x ht]
  have H := pair_components_algebra hnr (p t x) (q t x) (hpair t x ht)
  split_ifs
  · rw [H.1]; ring
  · rw [H.2]; ring

private theorem solution_pair {n : ℕ} {a D : ℝ} {u} (hn : 2 ≤ n) (hD : 0 ≤ D)
    (hu : ClassicalSolution n a D u) :
    ∃ p q : ℝ → ℝ → ℝ, ScalarRegular p ∧ ScalarRegular q ∧
      (∀ i t x, 0 ≤ t → u i t x = if i.val%2=0 then p t x else q t x) ∧
      (∀ t x, 0 ≤ t → p t x+q t x=1/(n:ℝ)) ∧
      (∀ t x, 0 < t → (deriv (fun s => p s x) t) = D*(deriv (deriv (p t)) x)+a*p t x*q t x*(1-2*(n:ℝ)*p t x)) ∧
      (∀ t x, 0 < t → (deriv (fun s => q s x) t) = D*(deriv (deriv (q t)) x)+a*p t x*q t x*(1-2*(n:ℝ)*q t x)) ∧
      (∀ t x, 0 ≤ t → p t (-x)=q t x) ∧
      (∀ t x, 0 ≤ t → q t (-x)=p t x) := by
  let i0 : Fin (2*n) := ⟨0,by omega⟩
  let i1 : Fin (2*n) := ⟨1,by omega⟩
  let p := u i0
  let q := u i1
  have hrp : ScalarRegular p := component_regular hu i0
  have hrq : ScalarRegular q := component_regular hu i1
  have hcomp : ∀ i t x, 0 ≤ t → u i t x=if i.val%2=0 then p t x else q t x := by
    intro i t x ht
    exact parity_of_shift_two hn (fun j => u j t x)
      (fun j => shift_two_invariant hn hD hu j t x ht) i
  have hfun : ∀ t x, 0 ≤ t → (fun i => u i t x) =
      fun i => if i.val%2=0 then p t x else q t x := by
    intro t x ht; funext i; exact hcomp i t x ht
  have hp : ∀ t x, 0 < t → (deriv (fun s => p s x) t) = D*(deriv (deriv (p t)) x)+a*p t x*q t x*(1-2*(n:ℝ)*p t x) := by
    intro t x ht
    have H := hu.equation i0 t x ht
    rw [hfun t x ht.le,parity_reaction hn] at H
    change (deriv (fun s => p s x) t) = (if i0.val%2=0 then a*p t x*q t x*(1-2*(n:ℝ)*p t x)
      else a*p t x*q t x*(1-2*(n:ℝ)*q t x))+D*(deriv (deriv (p t)) x) at H
    norm_num [i0] at H
    linarith
  have hq : ∀ t x, 0 < t → (deriv (fun s => q s x) t) = D*(deriv (deriv (q t)) x)+a*p t x*q t x*(1-2*(n:ℝ)*q t x) := by
    intro t x ht
    have H := hu.equation i1 t x ht
    rw [hfun t x ht.le,parity_reaction hn] at H
    change (deriv (fun s => q s x) t) = (if i1.val%2=0 then a*p t x*q t x*(1-2*(n:ℝ)*p t x)
      else a*p t x*q t x*(1-2*(n:ℝ)*q t x))+D*(deriv (deriv (q t)) x) at H
    norm_num [i1] at H
    linarith
  have hnr : (n:ℝ) ≠ 0 := by positivity
  let s := fun t x => 1*p t x+1*q t x+(-(1/(n:ℝ)))
  let B := fun t x => -2*(n:ℝ)*a*p t x*q t x
  have hrs : ScalarRegular s := hrp.affine hrq 1 1 (-(1/(n:ℝ)))
  have hBc : ContinuousOn B.uncurry (Ici 0 ×ˢ univ) :=
    (hrp.continuous.const_mul (-2*(n:ℝ)*a)).mul hrq.continuous
  have hsE : ∀ t x, 0 < t → (deriv (fun r => s r x) t) = D*(deriv (deriv (s t)) x)+B t x*s t x := by
    intro t x ht
    have H := affine_derivatives hrp hrq 1 1 (-(1/(n:ℝ))) ht x
    change (deriv (fun r => s r x) t) = _ ∧ (deriv (deriv (s t)) x) = _ at H
    rw [H.1,H.2,hp t x ht,hq t x ht]
    dsimp [s,B]
    field_simp
    ring
  have hs0 : ∀ x, s 0 x=0 := by
    intro x
    dsimp [s,p,q]
    rw [hu.initial,hu.initial]
    simp only [initialData, i0, i1, Fin.val_mk]
    norm_num
    field_simp [hnr] <;> ring
  have hzero := scalar_linear_zero hrs hD hBc hsE hs0
  have hpair : ∀ t x, 0 ≤ t → p t x+q t x=1/(n:ℝ) := by
    intro t x ht
    have H := hzero t x ht
    dsimp [s] at H
    linarith
  have hc : finCycle (⟨1,by omega⟩ : Fin (2*n)) i0 = i1 := by
    apply Fin.ext
    simp [finCycle_apply, Fin.val_add, i0, i1, Nat.mod_eq_of_lt (show 1 < 2*n by omega)]
  have hqp : ∀ t x, 0 ≤ t → q t (-x)=p t x := by
    intro t x ht
    have H := reflection_invariant hn hD hu i0 t x ht
    rw [hc] at H
    exact H
  have hpq : ∀ t x, 0 ≤ t → p t (-x)=q t x := by
    intro t x ht
    simpa only [neg_neg] using (hqp t (-x) ht).symm
  exact ⟨p,q,hrp,hrq,hcomp,hpair,hp,hq,hpq,hqp⟩

private theorem vg_family : ∀ (n : ℕ) (a D : ℝ), 2 ≤ n → -1 < a → a ≤ 0 →
  0 < D → 0 ≤ 2*(n:ℝ)*D+a → ∀ u, ClassicalSolution n a D u → Homogenizes n u := by
  intro n a D hn ha hapos hD hthreshold u hu
  rcases solution_pair hn hD.le hu with ⟨p,q,hrp,hrq,hcomp,hpair,hp,hq,hpq,hqp⟩
  have hnr : (n:ℝ) ≠ 0 := by positivity
  let w := fun t x => (n:ℝ)*(p t x-q t x)
  let μ : ℝ := -a/(2*(n:ℝ))
  have hrw : ScalarRegular w := by
    convert! hrp.affine hrq (n:ℝ) (-(n:ℝ)) 0 using 1
    funext t x; dsimp [w]; ring
  have hwD : ∀ t x, 0 < t → (deriv (fun s => w s x) t) = D*(deriv (deriv (w t)) x)+μ*(w t x-(w t x)^3) := by
    intro t x ht
    have H := affine_derivatives hrp hrq (n:ℝ) (-(n:ℝ)) 0 ht x
    have heq : (fun t x => (n:ℝ)*p t x+(-(n:ℝ))*q t x+0) = w := by
      funext t x; dsimp [w]; ring
    rw [heq] at H
    rw [H.1,H.2,hp t x ht,hq t x ht]
    have HA := scalar_pair_algebra hnr a (p t x) (q t x) (hpair t x ht.le)
    dsimp [μ,w]
    linear_combination HA
  have hodd : ∀ t, 0 < t → ∀ x, w t (-x) = -w t x := by
    intro t ht x
    dsimp [w]
    rw [hpq t x ht.le,hqp t x ht.le]
    ring
  have hμ : 0 ≤ μ := div_nonneg (neg_nonneg.mpr hapos) (by positivity)
  have hμD : μ ≤ D := by
    apply (div_le_iff₀ (show 0 < 2*(n:ℝ) by positivity)).mpr
    linarith
  exact homogenizes_of_parity_scalar hn u p q hpair hcomp
    (odd_allen_cahn_decay hrw hD hμ hμD hwD hodd)

theorem result : ¬ claim := family_implies_not_claim vg_family


end D5.S3.FluidDynamics.ReactionDiffusion.VisomirskiGriffinFrozenWaveRefutation
