/- GID: D5/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/OptimalLaw/RationalPrice
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The optimal full-real slope is a positive rational number and the unique real zero of the triangular root value. -/

import D5.S3.Arith.FibonacciAtomic.OptimalLawStrictSlope
import D5.S3.Arith.FibonacciAtomic.TriangularFirstSplitRecurrence
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Fintype.Pigeonhole
import D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding
import D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic
open TriangularPathNormalization TriangularFirstSplitRecurrence

namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice

private theorem triangular_lower (m : ℕ) (hm : 2 ≤ m) (γ : RootPath m) :
    OptimalLawStrictSlope.alpha m * anchorMass γ ≤ pathCost γ := by
  classical
  obtain ⟨hnonneg, hsum, _, hmin, hcost, hpositive⟩ :=
    TriangularPathNormalization.result m hm γ
  by_cases ht : 0 < anchorMass γ
  · obtain ⟨hn, hminimum⟩ := hmin
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' hn (probability γ)
    have heq' : probability γ i = anchorMass γ := heq.symm.trans hminimum
    have hlow : ∀ j, probability γ i ≤ probability γ j := by
      intro j
      rw [← heq]
      exact Finset.inf'_le _ (Finset.mem_univ j)
    have H := OptimalLawStrictSlope.alpha_le m (probability γ)
      (hpositive ht) hsum i hlow
    rw [heq'] at H
    rw [hcost]
    exact (le_div_iff₀ ht).mp H
  · have ha : 0 ≤ anchorMass γ := tsum_nonneg (fun d => by positivity)
    have hz : anchorMass γ = 0 := by linarith
    rw [hz, mul_zero]
    exact tsum_nonneg (fun d => by positivity)

private def root_path (m : ℕ) (γ : TriangularFirstSplitRecurrence.Path m 1) : RootPath m where
  state := γ.state
  action := γ.action
  root := γ.start
  legal := γ.legal
  step := γ.step

private theorem below_alpha_nonnegative (m : ℕ) (hm : 2 ≤ m) (x : ℝ)
    (hx : x ≤ OptimalLawStrictSlope.alpha m) :
    0 ≤ TriangularFirstSplitRecurrence.W x m 1 := by
  apply le_csInf
  · exact ⟨_, ⟨TriangularFirstSplitRecurrence.noSplit m 1 (by omega), rfl⟩⟩
  · rintro y ⟨γ, rfl⟩
    have H := triangular_lower m hm (root_path m γ)
    have ht : 0 ≤ anchorMass (root_path m γ) := tsum_nonneg (fun d => by positivity)
    have HM := mul_le_mul_of_nonneg_right hx ht
    change 0 ≤ pathCost (root_path m γ) - x * anchorMass (root_path m γ)
    linarith

private theorem zero_if_optimum_embeds (m : ℕ) (hm : 2 ≤ m)
    (γ : RootPath m)
    (h : pathCost γ = OptimalLawStrictSlope.alpha m * anchorMass γ) :
    TriangularFirstSplitRecurrence.W (OptimalLawStrictSlope.alpha m) m 1 = 0 := by
  have low := below_alpha_nonnegative m hm _ le_rfl
  let δ : TriangularFirstSplitRecurrence.Path m 1 :=
    ⟨γ.state, γ.action, γ.root, γ.legal, γ.step⟩
  have hd : TriangularFirstSplitRecurrence.pathValue (OptimalLawStrictSlope.alpha m) δ = 0 := by
    change pathCost γ - OptimalLawStrictSlope.alpha m * anchorMass γ = 0
    linarith
  have H : TriangularFirstSplitRecurrence.W (OptimalLawStrictSlope.alpha m) m 1 ≤
      TriangularFirstSplitRecurrence.pathValue (OptimalLawStrictSlope.alpha m) δ := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨η, rfl⟩
      have HH := triangular_lower m hm (root_path m η)
      change 0 ≤ pathCost (root_path m η) -
        OptimalLawStrictSlope.alpha m * anchorMass (root_path m η)
      linarith
    · exact ⟨δ, rfl⟩
  linarith


private lemma anchor_bounds (m : ℕ) (γ : RootPath m) : 0≤anchorMass γ ∧ anchorMass γ≤1 := by
  have eq : anchorMass γ = Real.ofDigits (fun d => anchorDigit (γ.action d)) := by
    simp [anchorMass,Real.ofDigits,Real.ofDigitsTerm,div_eq_mul_inv]
  rw [eq]
  exact ⟨Real.ofDigits_nonneg _,Real.ofDigits_le_one _⟩

private lemma root_cost (m : ℕ) (hm : 2≤m) (γ : RootPath m) : 1≤pathCost γ := by
  have summableR : Summable (fun d => ((γ.state d).r:ℝ)/(2:ℝ)^d) := by
    apply Summable.of_nonneg_of_le (f := fun d => (m:ℝ)*(1/2:ℝ)^d)
      (fun d => by positivity)
    · intro d
      have H : ((γ.state d).r:ℝ)≤m := by
        exact_mod_cast (Nat.le_trans (γ.legal d).2.1.le (γ.legal d).2.2.1)
      rw [div_pow,one_pow,mul_one_div]
      exact div_le_div_of_nonneg_right H (by positivity)
    · exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)).mul_left (m:ℝ)
  have H := summableR.sum_le_tsum ({0}:Finset ℕ) (fun d _ => by positivity)
  simpa [pathCost,γ.root] using H

private theorem at_alpha_zero (m : ℕ) (hm : 2≤m) : W (OptimalLawStrictSlope.alpha m) m 1=0 := by
  obtain ⟨p,k,hp,hs,hk,ho⟩ := OptimalLawStrictSlope.attained m hm
  obtain ⟨σ,γ,heq,hat,hcost⟩ := D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.result m hm p k hp hs hk ho
  apply zero_if_optimum_embeds m hm γ
  rw [hcost,hat]
  have H := (div_eq_iff (hp k).ne').mp ho
  simpa [mul_comm] using H

private lemma root_bdd_below (m : ℕ) (hm : 2≤m) (x : ℝ) :
    BddBelow (Set.range (fun γ : TriangularFirstSplitRecurrence.Path m 1 => pathValue x γ)) := by
  refine ⟨-(|x|),?_⟩
  rintro y ⟨γ,rfl⟩
  let δ := root_path m γ
  have hc := root_cost m hm δ
  have ht := anchor_bounds m δ
  have hprod : x*anchorMass δ≤|x| := by
    calc
      _ ≤ |x| * anchorMass δ := mul_le_mul_of_nonneg_right (le_abs_self x) ht.1
      _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg x)
      _ = _ := mul_one _
  change -|x| ≤pathCost δ-x*anchorMass δ
  linarith

/-- The triangular root value vanishes at exactly the full-real optimum. -/
theorem zero_iff_alpha (m : ℕ) (hm : 2≤m) (x : ℝ) :
    W x m 1=0 ↔ x=OptimalLawStrictSlope.alpha m := by
  constructor
  · intro hz
    rcases lt_trichotomy x (OptimalLawStrictSlope.alpha m) with hlt|heq|hgt
    · obtain ⟨γ,hγ⟩ := (TriangularFirstSplitRecurrence.result m hm x m ⟨by omega,le_rfl⟩ 1 (by omega)).2.2
      let δ := root_path m γ
      have hc := root_cost m hm δ
      have ht := (anchor_bounds m δ).1
      have lower := triangular_lower m hm δ
      have he : pathCost δ-x*anchorMass δ=0 := by
        change pathValue x γ=0
        rw [hγ,hz]
      by_cases hp : 0<anchorMass δ
      · have H := mul_lt_mul_of_pos_right hlt hp
        linarith
      · have H : anchorMass δ=0 := by linarith
        rw [H,mul_zero,sub_zero] at he
        linarith
    · exact heq
    · obtain ⟨p,k,hp,hs,hk,ho⟩ := OptimalLawStrictSlope.attained m hm
      obtain ⟨σ,γ,heq,hat,hcost⟩ := D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.result m hm p k hp hs hk ho
      let δ : TriangularFirstSplitRecurrence.Path m 1 := ⟨γ.state,γ.action,γ.root,γ.legal,γ.step⟩
      have hv : pathValue x δ<0 := by
        change pathCost γ-x*anchorMass γ<0
        rw [hat,hcost]
        have HC := (div_eq_iff (hp k).ne').mp ho
        have H := mul_lt_mul_of_pos_right hgt (hp k)
        nlinarith only [HC,H]
      have HW : W x m 1 ≤ pathValue x δ :=
        csInf_le (root_bdd_below m hm x) ⟨δ,rfl⟩
      rw [hz] at HW
      linarith
  · intro H
    rw [H]
    exact at_alpha_zero m hm


end D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice

open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic
open DyadicSupportLines OptimalLawStrictSlope
namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice
set_option maxHeartbeats 800000

private lemma rational_of_dyadic (x : ℝ) (h : ∃ D : ℕ, ∃ z : ℤ, (2 : ℝ)^D*x=z) :
    ∃ q : ℚ, (q : ℝ)=x := by
  obtain ⟨D,z,hz⟩ := h
  refine ⟨(z:ℚ)/(2:ℚ)^D,?_⟩
  push_cast
  apply (div_eq_iff (by positivity : (2:ℝ)^D≠0)).mpr
  simpa [mul_comm] using hz.symm

private lemma normalized_rational_minimum (m : ℕ) (p : Fin m → ℝ) (k : Fin m)
    (hs : ∑ i, p i=1) (hk : ∀ i, p k≤p i)
    (hr : ∀ i, p k<p i → ∃ q:ℚ, (q:ℝ)=p i) :
    ∀ i, ∃ q:ℚ, (q:ℝ)=p i := by
  classical
  let S := Finset.univ.filter (fun i => p i=p k)
  have hS : S.Nonempty := ⟨k, by simp [S]⟩
  have hc : (S.card:ℝ)≠0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  let q : Fin m → ℚ := fun i => if hi : p k<p i then (hr i hi).choose else 0
  have qeq (i : Fin m) : (q i:ℝ)=if p k<p i then p i else 0 := by
    dsimp only [q]
    split_ifs with hi
    · exact (hr i hi).choose_spec
    · norm_num
  have sumS : (∑ i : Fin m, if p i=p k then p k else 0)=(S.card:ℝ)*p k := by
    rw [← Finset.sum_filter]
    simp [S]
  have sumEq : (S.card:ℝ)*p k+(∑ i, q i:ℚ)=1 := by
    rw [← sumS, Rat.cast_sum, ← Finset.sum_add_distrib, ← hs]
    apply Finset.sum_congr rfl
    intro i _
    rw [qeq]
    by_cases hi : p i=p k
    · simp [hi]
    · have hlt : p k<p i := lt_of_le_of_ne (hk i) (Ne.symm hi)
      simp [hi,hlt]
  let t : ℚ := (1-∑ i,q i)/(S.card:ℚ)
  have ht : (t:ℝ)=p k := by
    dsimp only [t]
    push_cast
    apply (div_eq_iff hc).mpr
    push_cast at sumEq
    nlinarith only [sumEq]
  intro i
  by_cases hi : p k<p i
  · exact hr i hi
  · have he : p i=p k := le_antisymm (le_of_not_gt hi) (hk i)
    exact ⟨t,ht.trans he.symm⟩

private theorem optimizer_rational (m : ℕ) (hm : 2≤m) (p : Fin m → ℝ) (k : Fin m)
    (hp : ∀ i,0<p i) (hs : ∑ i,p i=1) (hk : ∀ i,p k≤p i)
    (ho : cost p /p k=alpha m) : ∀ i, ∃ q:ℚ, (q:ℝ)=p i := by
  apply normalized_rational_minimum m p k hs hk
  intro i hi
  obtain ⟨D,hD,hz,_,_⟩ := D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding.result m hm p k hp hs hk ho i hi
  exact rational_of_dyadic (p i) ⟨D,hz⟩

end D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice

open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic
open TriangularFirstSplitRecurrence DyadicSupportLines
namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice
set_option maxHeartbeats 800000

private lemma rational_of_equal_tails (f : ℕ → ℚ)
    (sm : Summable (fun d => (f d:ℝ)/(2:ℝ)^d))
    (a b : ℕ) (hab : a<b) (tails : ∀ n, f (n+a)=f (n+b)) :
    ∃ q:ℚ, (q:ℝ)=∑' d, (f d:ℝ)/(2:ℝ)^d := by
  let qa : ℚ := ∑ j∈Finset.range a, f j/(2:ℚ)^j
  let qb : ℚ := ∑ j∈Finset.range b, f j/(2:ℚ)^j
  have head (c : ℕ) : (∑ j∈Finset.range c, (f j:ℝ)/(2:ℝ)^j)+
      ((2:ℝ)^c)⁻¹*(∑' n, (f (n+c):ℝ)/(2:ℝ)^n)=
      ∑' d, (f d:ℝ)/(2:ℝ)^d := by
    rw [← sm.sum_add_tsum_nat_add c]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_add]
    ring
  have hA := head a
  have hB := head b
  have castA : (qa:ℝ)=∑ j∈Finset.range a, (f j:ℝ)/(2:ℝ)^j := by
    dsimp only [qa]; push_cast; rfl
  have castB : (qb:ℝ)=∑ j∈Finset.range b, (f j:ℝ)/(2:ℝ)^j := by
    dsimp only [qb]; push_cast; rfl
  rw [← castA] at hA
  rw [← castB] at hB
  simp_rw [tails] at hA
  have denom : ((2:ℝ)^a)⁻¹-((2:ℝ)^b)⁻¹≠0 := by
    apply sub_ne_zero.mpr
    intro H
    exact (pow_lt_pow_right₀ (by norm_num : (1:ℝ)<2) hab).ne (inv_injective H)
  refine ⟨(((2:ℚ)^a)⁻¹*qb-((2:ℚ)^b)⁻¹*qa)/
    (((2:ℚ)^a)⁻¹-((2:ℚ)^b)⁻¹),?_⟩
  push_cast
  apply (div_eq_iff denom).mpr
  nlinarith [congrArg (fun y => ((2:ℝ)^b)⁻¹*y) hA,
    congrArg (fun y => ((2:ℝ)^a)⁻¹*y) hB]

private theorem rational_no_split (e r : ℕ) (hr : r<e) : ∃ q:ℚ, (q:ℝ)=U e r := by
  have bound (d : ℕ) : rho e r d<e := (noSplit e r hr).legal d |>.2.1
  have sm : Summable (fun d => (rho e r d:ℝ)/(2:ℝ)^d) := by
    apply Summable.of_nonneg_of_le (f := fun d => (e:ℝ)*(1/2:ℝ)^d)
      (fun d => by positivity)
    · intro d
      rw [div_pow, one_pow, mul_one_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast (bound d).le) (by positivity)
    · exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)).mul_left (e:ℝ)
  obtain ⟨a,b,hne,he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun d : ℕ => (⟨rho e r d,bound d⟩ : Fin e))
  have eq : rho e r a=rho e r b := congrArg Fin.val he
  rcases lt_or_gt_of_ne hne with hab|hba
  · apply rational_of_equal_tails (fun d => (rho e r d:ℚ)) (by simpa using sm) a b hab
    intro n
    exact_mod_cast (show rho e r (n+a)=rho e r (n+b) from by
      simp only [rho, Function.iterate_add_apply]
      change (fun x:ℕ => 2*x%e)^[n] (rho e r a)=
        (fun x:ℕ => 2*x%e)^[n] (rho e r b)
      rw [eq])
  · apply rational_of_equal_tails (fun d => (rho e r d:ℚ)) (by simpa using sm) b a hba
    intro n
    exact_mod_cast (show rho e r (n+b)=rho e r (n+a) from by
      simp only [rho, Function.iterate_add_apply]
      change (fun x:ℕ => 2*x%e)^[n] (rho e r b)=
        (fun x:ℕ => 2*x%e)^[n] (rho e r a)
      rw [eq])

private lemma orbit_mod (e n d : ℕ) : rho e (n%e) d=(2^d*n)%e := by
  induction d with
  | zero => simp [rho]
  | succ d ih =>
    rw [rho, Function.iterate_succ_apply']
    change (2*rho e (n%e) d)%e=(2^(d+1)*n)%e
    rw [ih, pow_succ]
    rw [Nat.mul_mod_mod]
    congr 1
    ring

private lemma rational_fraction_cost (q : ℚ) (hq : 0≤q) :
    ∃ v:ℚ, (v:ℝ)=∑' d:ℕ, Int.fract ((2:ℝ)^d*(q:ℝ))/(2:ℝ)^d := by
  let n := q.num.natAbs
  let e := q.den
  have he : 0<e := Rat.pos q
  have qeq : (q:ℝ)=(n:ℝ)/(e:ℝ) := by
    have hn : (n:ℤ)=q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
    rw [Rat.cast_def]
    dsimp only [e]
    rw [← hn, Int.cast_natCast]
  have frac (d : ℕ) : Int.fract ((2:ℝ)^d*(q:ℝ))=(rho e (n%e) d:ℝ)/(e:ℝ) := by
    rw [qeq, ← mul_div_assoc]
    have heq : (2:ℝ)^d*(n:ℝ)=(2^d*n:ℕ) := by push_cast; rfl
    rw [heq, Int.fract_div_natCast_eq_div_natCast_mod, orbit_mod]
  obtain ⟨v,hv⟩ := rational_no_split e (n%e) (Nat.mod_lt _ he)
  refine ⟨v/(e:ℚ),?_⟩
  push_cast
  rw [hv,U,← tsum_div_const]
  apply tsum_congr
  intro d
  rw [frac]
  ring

/-- Every nonnegative normalized law with rational coordinates has rational dyadic cost. -/
theorem rational_law_cost (m : ℕ) (p : Fin m → ℝ)
    (hp : ∀ i,0≤p i) (hs : ∑ i,p i=1)
    (hr : ∀ i,∃ q:ℚ,(q:ℝ)=p i) : ∃ v:ℚ,(v:ℝ)=cost p := by
  classical
  choose q hq using hr
  have qp (i : Fin m) : 0≤q i := by exact_mod_cast (hq i).symm ▸ hp i
  choose v hv using (fun i => rational_fraction_cost (q i) (qp i))
  refine ⟨∑ i,v i,?_⟩
  rw [Rat.cast_sum]
  simp_rw [hv,hq]
  unfold cost
  rw [← Summable.tsum_finsetSum]
  · apply tsum_congr
    intro d
    simp only [Int.fract, sub_div, ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hs,mul_one,DyadicSupportLines.residual,Int.cast_sum]
  · intro i _
    apply Summable.of_nonneg_of_le (f := fun d => (1/2:ℝ)^d)
      (fun d => div_nonneg (Int.fract_nonneg _) (by positivity))
    · intro d
      rw [div_pow,one_pow]
      exact div_le_div_of_nonneg_right (Int.fract_lt_one _).le (by positivity)
    · exact summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)

end D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice

open scoped BigOperators
open D5.S3.Arith.FibonacciAtomic
open DyadicSupportLines OptimalLawStrictSlope
namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice

/-- The full-real optimum has a positive rational representative. -/
theorem rational_alpha (m : ℕ) (hm : 2≤m) : ∃ A:ℚ, 0<A ∧ (A:ℝ)=alpha m := by
  obtain ⟨p,k,hp,hs,hk,ho⟩ := attained m hm
  have hr := D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.optimizer_rational m hm p k hp hs hk ho
  obtain ⟨q,hq⟩ := hr k
  obtain ⟨v,hv⟩ := D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_law_cost m p (fun i => (hp i).le) hs hr
  have he : ((v/q:ℚ):ℝ)=alpha m := by
    push_cast
    rw [hv,hq,ho]
  refine ⟨v/q,?_,he⟩
  have ha : (0:ℝ)<alpha m := lt_of_lt_of_le
    (by exact_mod_cast (show 0<m by omega)) (alpha_ge_labels m hm)
  exact_mod_cast he.symm ▸ ha

end D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice

open D5.S3.Arith.FibonacciAtomic
namespace D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice

/-- One positive rational equals the full-real optimum and is the unique real root price. -/
theorem result (m : ℕ) (hm : 2≤m) : ∃ A:ℚ,
    0<A ∧ (A:ℝ)=OptimalLawStrictSlope.alpha m ∧
    ∀ x:ℝ, TriangularFirstSplitRecurrence.W x m 1=0 ↔ x=(A:ℝ) := by
  obtain ⟨A,hA,he⟩ := D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.rational_alpha m hm
  refine ⟨A,hA,he,?_⟩
  intro x
  rw [he]
  exact D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice.zero_iff_alpha m hm x

end D5.S3.Arith.FibonacciAtomic.OptimalLaw.RationalPrice
