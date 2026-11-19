/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCollisionRemoval
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveCollisionRemoval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coincident indices contribute negligible errors to finite sieve interval correlations. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FormalIntervalMomentBounds
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.NormalizationAlgebra
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.FiniteSieveDefs

open scoped BigOperators Topology
open Set Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private lemma collision_coefficient_bounds {L B a b : ℝ}
    (hL : 1 ≤ L) (hB : 1 ≤ B) (ha : |a| ≤ B*L) (hb : |b| ≤ B*L) :
    |a^2| ≤ B^2*L^2 ∧ |a^2-2*b| ≤ 3*B^2*L^2 ∧
      |a^2*b-2*b^2| ≤ 3*B^3*L^3 := by
  have hL0 : 0 ≤ L := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hBL : 1 ≤ B*L := one_le_mul_of_one_le_of_one_le hB hL
  have ha2 : |a^2| ≤ (B*L)^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hBL0 : 0 ≤ B*L := by positivity
  have hBL2 : B*L ≤ (B*L)^2 := le_self_pow₀ hBL (by norm_num)
  have hBL3 : (B*L)^2 ≤ (B*L)^3 := pow_le_pow_right₀ hBL (by norm_num)
  refine ⟨by simpa only [mul_pow] using ha2, ?_, ?_⟩
  · calc
      _ ≤ |a^2| + |2*b| := abs_sub _ _
      _ ≤ (B*L)^2 + 2*(B*L) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
      _ ≤ 3*(B*L)^2 := by linarith
      _ = _ := by ring
  · calc
      _ ≤ |a^2*b| + |2*b^2| := abs_sub _ _
      _ = |a^2| * |b| + 2*|b|^2 := by rw [abs_mul, abs_mul, abs_pow]; norm_num
      _ ≤ (B*L)^2*(B*L) + 2*(B*L)^2 := by gcongr
      _ ≤ 3*(B*L)^3 := by nlinarith
      _ = _ := by ring

private lemma cubic_collision_error {H L B K J a b S T : ℝ}
    (hL : 0 ≤ L) (hB : 0 ≤ B)
    (ha : |a| ≤ B*L) (hb : |b| ≤ B*L)
    (hS : |S| ≤ 3*K*H*L) (hT : |T| ≤ J*H) :
    |a*S+a*b*T| ≤ (3*B*K+B^2*J)*H*L^2 := by
  calc
    _ ≤ |a*S| + |a*b*T| := abs_add_le _ _
    _ = |a| * |S| + |a| * |b| * |T| := by simp only [abs_mul]
    _ ≤ (B*L)*(3*K*H*L) + (B*L)*(B*L)*(J*H) := by gcongr
    _ = _ := by ring

private lemma fourth_collision_error {H L B K J a b rep pair triple T : ℝ}
    (hL : 1 ≤ L) (hB : 1 ≤ B) (ha : |a| ≤ B*L) (hb : |b| ≤ B*L)
    (hpair : |pair| ≤ 3*K*H*L) (htriple : |triple| ≤ 4*K*H*L)
    (hT : |T| ≤ J*H) :
    |a*rep+a^2*pair+(a^2-2*b)*triple+(a^2*b-2*b^2)*T| ≤
      B*L * |rep| + (15*B^2*K+3*B^3*J)*H*L^3 := by
  have hL0 : 0 ≤ L := by linarith
  have hB0 : 0 ≤ B := by linarith
  obtain ⟨ha2,hc,hd⟩ := collision_coefficient_bounds hL hB ha hb
  calc
    _ ≤ |a*rep| + |a^2*pair| + |(a^2-2*b)*triple| + |(a^2*b-2*b^2)*T| := by
      grw [abs_add_le, abs_add_le, abs_add_le]
    _ = |a| * |rep| + |a^2| * |pair| + |a^2-2*b| * |triple| + |a^2*b-2*b^2| * |T| := by
      simp only [abs_mul]
    _ ≤ (B*L) * |rep| + (B^2*L^2)*(3*K*H*L)+(3*B^2*L^2)*(4*K*H*L)+
        (3*B^3*L^3)*(J*H) := by gcongr
    _ = _ := by ring

private lemma sieve_indicator_moment (Q : ℕ+) (M H : ℝ) (hH : 0 ≤ H)
    {k : ℕ} (a b : Fin k → ℝ) (hab : admissible M a b) :
    quadraticFamilyMoment (sieveFunctional Q)
      (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable Q d.val)
      (fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)) = sieveIntervalMoment Q H a b := by
  unfold quadraticFamilyMoment sieveIntervalMoment
  change sieveExpectation Q _ = sieveExpectation Q _
  congr 1
  funext x
  simp only [Finset.prod_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [intervalWeight, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_coe_sort (Finset.Iic ⌊M*H⌋₊)
    (fun n : ℕ => if n ∈ points H (a i) (b i) then sieveVariable Q n x else 0)]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_of_subset (interval_points_subset hH (hab i).2.2)]
  rfl

/-- The cubic distinct-index interval moment differs from its uniform moment by at most
the two-point and diagonal collision contributions. -/
private theorem sieve_cubic_collision_bound (Q : ℕ+) (M H L B K : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (ha : |sieveDensity Q-2| ≤ B*L) (hb : |sieveDensity Q-1| ≤ B*L)
    (h₂ : ∀ f g : Finset.Iic ⌊M*H⌋₊ → ℝ,
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f → IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g →
      |distinctIndexMoment (sieveFunctional Q) (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable Q d.val) ![f,g]| ≤
        K*H*L)
    (a b : Fin 3 → ℝ) (hab : admissible M a b) :
    |distinctIndexMoment (sieveFunctional Q) (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable Q d.val)
      (fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i))| ≤
      |sieveIntervalMoment Q H a b| + (3*B*K+B^2*M)*H*L^2 := by
  let Z : Finset.Iic ⌊M*H⌋₊ → ZMod (Q : ℕ) → ℝ := fun d => sieveVariable Q d.val
  let f := fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)
  have hf (i : Fin 3) : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) (f i) :=
    ⟨a i,b i,(hab i).1,(hab i).2.1,(hab i).2.2,rfl⟩
  have he : (fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)) =
      ![f 0,f 1,f 2] := by
    funext i; fin_cases i <;> rfl
  have hV := sieve_indicator_moment Q M H hH a b hab
  rw [he] at hV ⊢
  change quadraticFamilyMoment (sieveFunctional Q) Z ![f 0,f 1,f 2] = sieveIntervalMoment Q H a b at hV
  have h1 : sieveFunctional Q 1 = 1 := by
    change (∑ _ : ZMod (Q : ℕ), (1 : ℝ)) / (Q : ℝ) = 1
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast Q.ne_zero)
  have h0 (d : Finset.Iic ⌊M*H⌋₊) : sieveFunctional Q (Z d) = 0 := sieve_mean_zero Q d.val
  have hq (d : Finset.Iic ⌊M*H⌋₊) :
      Z d ^ 2 = (sieveDensity Q-2) • Z d + algebraMap ℝ (ZMod (Q : ℕ) → ℝ) (sieveDensity Q-1) := by
    ext x
    exact sieve_quadratic Q d.val x
  have hid := quadratic_third_moment_eq (sieveFunctional Q) Z (sieveDensity Q-2) (sieveDensity Q-1) h1 h0 hq
    (f 0) (f 1) (f 2)
  have hp : |distinctIndexMoment (sieveFunctional Q) Z ![f 0*f 1,f 2] +
      distinctIndexMoment (sieveFunctional Q) Z ![f 0*f 2,f 1] +
      distinctIndexMoment (sieveFunctional Q) Z ![f 1*f 2,f 0]| ≤ 3*K*H*L := by
    grw [abs_add_le, abs_add_le, h₂ _ _ ((hf 0).mul hH (hf 1)) (hf 2),
      h₂ _ _ ((hf 0).mul hH (hf 2)) (hf 1),
      h₂ _ _ ((hf 1).mul hH (hf 2)) (hf 0)]
    ring_nf; rfl
  have hT := index_interval_weight_bound hH (f 0*f 1*f 2) (((hf 0).mul hH (hf 1)).mul hH (hf 2))
  have herr : |quadraticFamilyMoment (sieveFunctional Q) Z ![f 0,f 1,f 2] -
      distinctIndexMoment (sieveFunctional Q) Z ![f 0,f 1,f 2]| ≤
      (3*B*K+B^2*M)*H*L^2 := by
    calc
      _ = |(sieveDensity Q-2)*(distinctIndexMoment (sieveFunctional Q) Z ![f 0*f 1,f 2] +
          distinctIndexMoment (sieveFunctional Q) Z ![f 0*f 2,f 1] +
          distinctIndexMoment (sieveFunctional Q) Z ![f 1*f 2,f 0]) +
          (sieveDensity Q-2)*(sieveDensity Q-1)*indexSum (f 0*f 1*f 2)| := by
        congr 1
        rw [hid]
        ring
      _ ≤ _ := cubic_collision_error hL hB ha hb hp hT
  calc
    _ = |quadraticFamilyMoment (sieveFunctional Q) Z ![f 0,f 1,f 2] -
        (quadraticFamilyMoment (sieveFunctional Q) Z ![f 0,f 1,f 2] -
          distinctIndexMoment (sieveFunctional Q) Z ![f 0,f 1,f 2])| := by congr 1; ring
    _ ≤ |quadraticFamilyMoment (sieveFunctional Q) Z ![f 0,f 1,f 2]| +
        |quadraticFamilyMoment (sieveFunctional Q) Z ![f 0,f 1,f 2] -
          distinctIndexMoment (sieveFunctional Q) Z ![f 0,f 1,f 2]| := abs_sub _ _
    _ ≤ |sieveIntervalMoment Q H a b| + (3*B*K+B^2*M)*H*L^2 := by
      rw [← hV]
      exact add_le_add le_rfl herr

/-- The fourth distinct-index pairing defect is controlled by the uniform pairing defect,
the repeated-pair cubic terms, and the quadratic and diagonal collisions. -/
private theorem sieve_fourth_collision_bound (Q : ℕ+) (M H L B K U : ℝ)
    (hH : 0 ≤ H) (hL : 1 ≤ L) (hB : 1 ≤ B)
    (ha : |sieveDensity Q-2| ≤ B*L) (hb : |sieveDensity Q-1| ≤ B*L)
    (h₂ : ∀ f g : Finset.Iic ⌊M*H⌋₊ → ℝ,
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f → IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g →
      |distinctIndexMoment (sieveFunctional Q) (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable Q d.val) ![f,g]| ≤
        K*H*L)
    (h₃ : ∀ f g h : Finset.Iic ⌊M*H⌋₊ → ℝ,
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f → IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g →
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) h →
      |distinctIndexMoment (sieveFunctional Q) (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable Q d.val) ![f,g,h]| ≤
        U*(H*L)^(3/2 : ℝ))
    (a b : Fin 4 → ℝ) (hab : admissible M a b) :
    let f := fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)
    |distinctIndexMoment (sieveFunctional Q) (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable Q d.val) f -
      perfectPairingSum (fun u v => distinctIndexMoment (sieveFunctional Q)
        (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable Q d.val) ![u,v]) (f 0) (f 1) (f 2) (f 3)| ≤
      |sieveIntervalWickDefect Q H a b| + (6*B*U*L*(H*L)^(3/2 : ℝ)+(15*B^2*K+3*B^3*M)*H*L^3) := by
  let Z : Finset.Iic ⌊M*H⌋₊ → ZMod (Q : ℕ) → ℝ := fun d => sieveVariable Q d.val
  let f := fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)
  have hf (i : Fin 4) : IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) (f i) :=
    ⟨a i,b i,(hab i).1,(hab i).2.1,(hab i).2.2,rfl⟩
  have he : f = ![f 0,f 1,f 2,f 3] := by
    funext i; fin_cases i <;> rfl
  change |distinctIndexMoment (sieveFunctional Q) Z f - perfectPairingSum
    (fun u v => distinctIndexMoment (sieveFunctional Q) Z ![u,v]) (f 0) (f 1) (f 2) (f 3)| ≤ _
  rw [he]
  have hV4 := sieve_indicator_moment Q M H hH a b hab
  change quadraticFamilyMoment (sieveFunctional Q) Z f = sieveIntervalMoment Q H a b at hV4
  rw [he] at hV4
  have hV2 (i j : Fin 4) : quadraticFamilyMoment (sieveFunctional Q) Z ![f i,f j] =
      sieveIntervalMoment Q H ![a i,a j] ![b i,b j] := by
    have had : admissible M ![a i,a j] ![b i,b j] := by
      intro t; fin_cases t <;> simpa using hab _
    have ht := sieve_indicator_moment Q M H hH ![a i,a j] ![b i,b j] had
    have he2 : (fun t : Fin 2 => intervalWeight H (Finset.Iic ⌊M*H⌋₊)
        (![a i,a j] t) (![b i,b j] t)) = ![f i,f j] := by
      funext t; fin_cases t <;> rfl
    rw [he2] at ht
    exact ht
  let v := quadraticFamilyMoment (sieveFunctional Q) Z ![f 0,f 1,f 2,f 3] -
    perfectPairingSum (fun u v => quadraticFamilyMoment (sieveFunctional Q) Z ![u,v])
      (f 0) (f 1) (f 2) (f 3)
  let r := distinctIndexMoment (sieveFunctional Q) Z ![f 0,f 1,f 2,f 3] -
    perfectPairingSum (fun u v => distinctIndexMoment (sieveFunctional Q) Z ![u,v])
      (f 0) (f 1) (f 2) (f 3)
  change |r| ≤ _
  have hdef : v = sieveIntervalWickDefect Q H a b := by
    dsimp only [v]
    simp only [perfectPairingSum, hV4, hV2, sieveIntervalWickDefect, sieveIntervalPairing]
  have h1 : sieveFunctional Q 1 = 1 := by
    change (∑ _ : ZMod (Q : ℕ), (1 : ℝ)) / (Q : ℝ) = 1
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast Q.ne_zero)
  have h0 (d : Finset.Iic ⌊M*H⌋₊) : sieveFunctional Q (Z d) = 0 := sieve_mean_zero Q d.val
  have hq (d : Finset.Iic ⌊M*H⌋₊) :
      Z d ^ 2 = (sieveDensity Q-2) • Z d + algebraMap ℝ (ZMod (Q : ℕ) → ℝ) (sieveDensity Q-1) := by
    ext x
    exact sieve_quadratic Q d.val x
  have hid := quadratic_fourth_pairing_defect (sieveFunctional Q) Z (sieveDensity Q-2) (sieveDensity Q-1)
    h1 h0 hq (f 0) (f 1) (f 2) (f 3)
  let rep := repeatedPairSum (fun u v w => distinctIndexMoment (sieveFunctional Q) Z ![u,v,w])
    (f 0) (f 1) (f 2) (f 3)
  let pair := pairPairSum (fun u v => distinctIndexMoment (sieveFunctional Q) Z ![u,v])
    (f 0) (f 1) (f 2) (f 3)
  let triple := tripleSingletonSum (fun u v => distinctIndexMoment (sieveFunctional Q) Z ![u,v])
    (f 0) (f 1) (f 2) (f 3)
  change v = r+(sieveDensity Q-2)*rep+(sieveDensity Q-2)^2*pair+((sieveDensity Q-2)^2-2*(sieveDensity Q-1))*triple+
    ((sieveDensity Q-2)^2*(sieveDensity Q-1)-2*(sieveDensity Q-1)^2)*indexSum (f 0*f 1*f 2*f 3) at hid
  have hr : |rep| ≤ 6*U*(H*L)^(3/2 : ℝ) := by
    dsimp only [rep, repeatedPairSum]
    grw [abs_add_le, abs_add_le, abs_add_le, abs_add_le, abs_add_le,
      h₃ _ _ _ ((hf 0).mul hH (hf 1)) (hf 2) (hf 3),
      h₃ _ _ _ ((hf 0).mul hH (hf 2)) (hf 1) (hf 3),
      h₃ _ _ _ ((hf 0).mul hH (hf 3)) (hf 1) (hf 2),
      h₃ _ _ _ ((hf 1).mul hH (hf 2)) (hf 0) (hf 3),
      h₃ _ _ _ ((hf 1).mul hH (hf 3)) (hf 0) (hf 2),
      h₃ _ _ _ ((hf 2).mul hH (hf 3)) (hf 0) (hf 1)]
    ring_nf; rfl
  have hp : |pair| ≤ 3*K*H*L := by
    dsimp only [pair, pairPairSum]
    grw [abs_add_le, abs_add_le,
      h₂ _ _ ((hf 0).mul hH (hf 1)) ((hf 2).mul hH (hf 3)),
      h₂ _ _ ((hf 0).mul hH (hf 2)) ((hf 1).mul hH (hf 3)),
      h₂ _ _ ((hf 0).mul hH (hf 3)) ((hf 1).mul hH (hf 2))]
    ring_nf; rfl
  have ht : |triple| ≤ 4*K*H*L := by
    dsimp only [triple, tripleSingletonSum]
    grw [abs_add_le, abs_add_le, abs_add_le,
      h₂ _ _ (((hf 1).mul hH (hf 2)).mul hH (hf 3)) (hf 0),
      h₂ _ _ (((hf 0).mul hH (hf 2)).mul hH (hf 3)) (hf 1),
      h₂ _ _ (((hf 0).mul hH (hf 1)).mul hH (hf 3)) (hf 2),
      h₂ _ _ (((hf 0).mul hH (hf 1)).mul hH (hf 2)) (hf 3)]
    ring_nf; rfl
  have hT := index_interval_weight_bound hH (f 0*f 1*f 2*f 3)
    ((((hf 0).mul hH (hf 1)).mul hH (hf 2)).mul hH (hf 3))
  have hL0 : 0 ≤ L := by linarith
  have hB0 : 0 ≤ B := by linarith
  have herr : |v-r| ≤
      6*B*U*L*(H*L)^(3/2 : ℝ)+(15*B^2*K+3*B^3*M)*H*L^3 := by
    calc
      _ = |(sieveDensity Q-2)*rep+(sieveDensity Q-2)^2*pair+((sieveDensity Q-2)^2-2*(sieveDensity Q-1))*triple+
          ((sieveDensity Q-2)^2*(sieveDensity Q-1)-2*(sieveDensity Q-1)^2)*indexSum (f 0*f 1*f 2*f 3)| := by
        congr 1
        rw [hid]
        ring
      _ ≤ B*L * |rep| + (15*B^2*K+3*B^3*M)*H*L^3 :=
        fourth_collision_error hL hB ha hb hp ht hT
      _ ≤ B*L*(6*U*(H*L)^(3/2 : ℝ))+(15*B^2*K+3*B^3*M)*H*L^3 := by
        gcongr
      _ = _ := by ring
  calc
    _ = |v-(v-r)| := by congr 1; ring
    _ ≤ |v| + |v-r| := abs_sub _ _
    _ ≤ |sieveIntervalWickDefect Q H a b| +
        (6*B*U*L*(H*L)^(3/2 : ℝ)+(15*B^2*K+3*B^3*M)*H*L^3) := by
      rw [← hdef]
      exact add_le_add le_rfl herr

private lemma repeated_pair_ratio (H L : ℝ) (hH : 0 < H) (hL : 0 < L) :
    L*(H*L)^(3/2 : ℝ)/(H*L)^2 = Real.sqrt (L/H) := by
  have hHL : 0 < H*L := mul_pos hH hL
  have hpow : ((H*L)^(3/2 : ℝ))^2 = (H*L)^3 := by
    rw [← Real.rpow_natCast ((H*L)^(3/2 : ℝ)) 2,
      ← Real.rpow_mul hHL.le]
    norm_num
  have hratio := cubic_formal_ratio H L 0 hH hL
  simp only [zero_mul, zero_add] at hratio
  rw [← hratio]
  apply (div_eq_div_iff (pow_ne_zero _ hHL.ne')
    (Real.rpow_pos_of_pos hHL (3/2 : ℝ)).ne').mpr
  calc
    _ = L*((H*L)^(3/2 : ℝ))^2 := by ring
    _ = L*(H*L)^3 := by rw [hpow]
    _ = _ := by ring

private theorem uniform_cubic_collision_removal
    (hS : FiniteSieveIntervals) (M B K : ℝ)
    (hM : 1 ≤ M) (hB : 1 ≤ B)
    (hQ : ∀ᶠ H : ℝ in atTop, sieveDensity (primorialSieveModulus M H) ≤ B*Real.log H)
    (h₂ : ∀ᶠ H : ℝ in atTop, ∀ f g : Finset.Iic ⌊M*H⌋₊ → ℝ,
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f → IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g →
      |distinctIndexMoment (sieveFunctional (primorialSieveModulus M H)) (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable (primorialSieveModulus M H) d.val)
        ![f,g]| ≤ K*H*Real.log H) :
    UniformIntervalSmall 3 (fun H a b => distinctIndexMoment (sieveFunctional (primorialSieveModulus M H))
      (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable (primorialSieveModulus M H) d.val)
      (fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i))) M := by
  intro ε hε
  let C := 3*(B+2)*K+(B+2)^2*M
  have ht : Tendsto (fun H : ℝ => Real.log H/H) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hlim : Tendsto (fun H : ℝ => C*Real.sqrt (Real.log H/H)) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using ht.sqrt.const_mul C
  filter_upwards [hS.1 M hM (ε/2) (half_pos hε), hQ, h₂,
    eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    hlim.eventually_le_const (half_pos hε)] with H hV hmod htwo hH hL hsmall a b hab
  have hH0 : 0 ≤ H := by linarith
  have hHpos : 0 < H := by linarith
  have hL0 : 0 ≤ Real.log H := by linarith
  have hLpos : 0 < Real.log H := by linarith
  have hBp : 0 ≤ B+2 := by linarith
  have hP0 : 0 ≤ sieveDensity (primorialSieveModulus M H) := by unfold sieveDensity; positivity
  have ha : |sieveDensity (primorialSieveModulus M H)-2| ≤ (B+2)*Real.log H := by
    rw [abs_le]
    constructor <;> nlinarith [hmod]
  have hb : |sieveDensity (primorialSieveModulus M H)-1| ≤ (B+2)*Real.log H := by
    rw [abs_le]
    constructor <;> nlinarith [hmod]
  have hbd := sieve_cubic_collision_bound (primorialSieveModulus M H) M H (Real.log H) (B+2) K
    hH0 hL0 hBp ha hb htwo a b hab
  have hIV := hV a b hab
  have hs : 0 < momentScale 3 H := by
    unfold momentScale
    exact Real.rpow_pos_of_pos (mul_pos hHpos hLpos) _
  have hratio := cubic_formal_ratio H (Real.log H) 0 hHpos hLpos
  simp only [zero_mul, zero_add] at hratio
  have hratio' : H*(Real.log H)^2 = Real.sqrt (Real.log H/H)*momentScale 3 H := by
    apply (div_eq_iff hs.ne').mp
    simpa only [momentScale, Nat.cast_ofNat] using hratio
  have he : C*H*(Real.log H)^2 = (C*Real.sqrt (Real.log H/H))*momentScale 3 H := by
    calc
      _ = C*(H*(Real.log H)^2) := by ring
      _ = _ := by rw [hratio']; ring
  have herror : C*H*(Real.log H)^2 ≤ (ε/2)*momentScale 3 H := by
    rw [he]
    exact mul_le_mul_of_nonneg_right hsmall hs.le
  calc
    _ ≤ |sieveIntervalMoment (primorialSieveModulus M H) H a b| + C*H*(Real.log H)^2 := hbd
    _ ≤ (ε/2)*momentScale 3 H+(ε/2)*momentScale 3 H := add_le_add hIV herror
    _ = ε*momentScale 3 H := by ring

/-- Uniform finite-sieve interval moment estimates imply uniform distinct-index estimates
for primorial moduli with logarithmic density and bounded two-point sums. -/
theorem sieve_collision_removal
    (hS : FiniteSieveIntervals) (M B K : ℝ)
    (hM : 1 ≤ M) (hB : 1 ≤ B)
    (hQ : ∀ᶠ H : ℝ in atTop, sieveDensity (primorialSieveModulus M H) ≤ B*Real.log H)
    (h₂ : ∀ᶠ H : ℝ in atTop, ∀ f g : Finset.Iic ⌊M*H⌋₊ → ℝ,
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f → IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g →
      |distinctIndexMoment (sieveFunctional (primorialSieveModulus M H)) (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable (primorialSieveModulus M H) d.val)
        ![f,g]| ≤ K*H*Real.log H) :
    UniformIntervalSmall 3 (fun H a b => distinctIndexMoment (sieveFunctional (primorialSieveModulus M H))
      (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable (primorialSieveModulus M H) d.val)
      (fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i))) M ∧
    UniformIntervalSmall 4 (fun H a b =>
      let f := fun i => intervalWeight H (Finset.Iic ⌊M*H⌋₊) (a i) (b i)
      distinctIndexMoment (sieveFunctional (primorialSieveModulus M H)) (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable (primorialSieveModulus M H) d.val) f -
        perfectPairingSum (fun u v => distinctIndexMoment (sieveFunctional (primorialSieveModulus M H))
          (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable (primorialSieveModulus M H) d.val) ![u,v])
          (f 0) (f 1) (f 2) (f 3)) M := by
  have hthird := uniform_cubic_collision_removal hS M B K hM hB hQ h₂
  refine ⟨hthird, ?_⟩
  intro ε hε
  let C := 15*(B+2)^2*K+3*(B+2)^3*M
  have ht : Tendsto (fun H : ℝ => Real.log H/H) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hlim : Tendsto (fun H : ℝ =>
      6*(B+2)*Real.sqrt (Real.log H/H)+C*(Real.log H/H)) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero, mul_zero, zero_add] using
      (ht.sqrt.const_mul (6*(B+2))).add (ht.const_mul C)
  filter_upwards [hS.2 M hM (ε/2) (half_pos hε), hthird 1 (by norm_num),
    hQ, h₂, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    hlim.eventually_le_const (half_pos hε)] with H hV hthirdH hmod htwo hH hL hsmall a b hab
  have hH0 : 0 ≤ H := by linarith
  have hHpos : 0 < H := by linarith
  have hLpos : 0 < Real.log H := by linarith
  have hHL : 0 < H*Real.log H := mul_pos hHpos hLpos
  have hBp : 1 ≤ B+2 := by linarith
  have hP0 : 0 ≤ sieveDensity (primorialSieveModulus M H) := by unfold sieveDensity; positivity
  have ha : |sieveDensity (primorialSieveModulus M H)-2| ≤ (B+2)*Real.log H := by
    rw [abs_le]
    constructor <;> nlinarith [hmod]
  have hb : |sieveDensity (primorialSieveModulus M H)-1| ≤ (B+2)*Real.log H := by
    rw [abs_le]
    constructor <;> nlinarith [hmod]
  have hthree : ∀ f g h : Finset.Iic ⌊M*H⌋₊ → ℝ,
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) f → IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) g →
      IsIntervalWeight M H (Finset.Iic ⌊M*H⌋₊) h →
      |distinctIndexMoment (sieveFunctional (primorialSieveModulus M H)) (fun d : Finset.Iic ⌊M*H⌋₊ => sieveVariable (primorialSieveModulus M H) d.val)
        ![f,g,h]| ≤ 1*(H*Real.log H)^(3/2 : ℝ) := by
    intro f g h hf hg hh
    obtain ⟨c,d,hcd,he⟩ := interval_weight_family ![f,g,h]
      (by intro i; fin_cases i <;> assumption)
    have hc := hthirdH c d hcd
    rw [← he] at hc
    simpa only [one_mul, momentScale, Nat.cast_ofNat] using hc
  have hbd := sieve_fourth_collision_bound (primorialSieveModulus M H) M H (Real.log H) (B+2) K 1
    hH0 hL hBp ha hb htwo hthree a b hab
  have hIV : |sieveIntervalWickDefect (primorialSieveModulus M H) H a b| ≤ (ε/2)*(H*Real.log H)^2 := by
    have hh := hV a b hab
    norm_num [momentScale] at hh
    exact hh
  have hrep := (div_eq_iff (pow_ne_zero 2 hHL.ne')).mp
    (repeated_pair_ratio H (Real.log H) hHpos hLpos)
  have hdiag : H*(Real.log H)^3 = (Real.log H/H)*(H*Real.log H)^2 := by
    field_simp [hHpos.ne']
  have he : 6*(B+2)*1*Real.log H*(H*Real.log H)^(3/2 : ℝ)+C*H*(Real.log H)^3 =
      (6*(B+2)*Real.sqrt (Real.log H/H)+C*(Real.log H/H))*(H*Real.log H)^2 := by
    calc
      _ = 6*(B+2)*(Real.log H*(H*Real.log H)^(3/2 : ℝ))+
          C*(H*(Real.log H)^3) := by ring
      _ = 6*(B+2)*(Real.sqrt (Real.log H/H)*(H*Real.log H)^2)+
          C*((Real.log H/H)*(H*Real.log H)^2) := by rw [hrep, hdiag]
      _ = _ := by ring
  dsimp only at hbd ⊢
  calc
    _ ≤ |sieveIntervalWickDefect (primorialSieveModulus M H) H a b| +
        (6*(B+2)*1*Real.log H*(H*Real.log H)^(3/2 : ℝ)+C*H*(Real.log H)^3) := hbd
    _ = |sieveIntervalWickDefect (primorialSieveModulus M H) H a b| +
        (6*(B+2)*Real.sqrt (Real.log H/H)+C*(Real.log H/H))*(H*Real.log H)^2 := by rw [he]
    _ ≤ (ε/2)*(H*Real.log H)^2+(ε/2)*(H*Real.log H)^2 :=
      add_le_add hIV (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _))
    _ = ε*(H*Real.log H)^2 := by ring
    _ = ε*momentScale 4 H := by norm_num [momentScale]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
