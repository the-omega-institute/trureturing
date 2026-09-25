/- GID: D5/S3/Quantum/Information/ActualPureQubitCostInfimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ActualPureQubitCostInfimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib]
   utility: none
   digest: Full finite affine-readout pure-qubit spectral-information cost infimum. -/

import D5.S3.Quantum.Information.ActualPureQubitUpperFamily
import D5.S3.Quantum.Information.ActualPureQubitFisherRank
open scoped InnerProductSpace ComplexOrder Matrix.Norms.Elementwise Topology
open Matrix Set Filter Finset
open D5.S3.Quantum.Foundation.FiniteStateChannel
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Information.ActualPureQubitCostInfimum

theorem result {m : ℕ} (p v : Fin m → ℝ)
    (hp : ∀ j,0<p j) (hp1 : ∑ j,p j=1) (hv0 : ∑ j,v j=0) (hv : v≠0)
    (hthree : ∃ i j k,v i/p i≠v j/p j ∧ v i/p i≠v k/p k ∧ v j/p j≠v k/p k) :
    let B := ∑ j,p j*(v j/p j)^2
    let V := (∑ j,p j*(v j/p j)^4)-B^2-(∑ j,p j*(v j/p j)^3)^2/B
    0<V ∧
    (∀ᶠ R in 𝓝[>] 0,(costs p v R).Nonempty ∧ BddBelow (costs p v R) ∧
      IsGLB (costs p v R) (C2 p v R)) ∧
    Tendsto (fun R => (C2 p v R-B)/R^2) (𝓝[>] 0) (𝓝 (V/4)) := by
  classical
  revert m

  have upper_result : ∀ {m : ℕ}
        (p v : Fin m → ℝ) (hp : ∀ j, 0<p j) (hp1 : ∑ j, p j=1)
        (hv0 : ∑ j, v j=0) (hv : ∃ j, v j ≠ 0),
        let B := ∑ j, v j^2/p j
        let V := (∑ j, v j^4/(p j)^3)-B^2-(∑ j, v j^3/(p j)^2)^2/B
        ∃ (N : ℝ → Fin m → Matrix (Fin 2) (Fin 2) ℂ)
          (rho : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (I : ℝ → Set ℝ) (Q : ℝ → ℝ),
          Tendsto (fun R => (Q R-B)/R^2) (𝓝[>] 0) (𝓝 (V/4)) ∧
          (∀ᶠ R in 𝓝[>] 0, IsProgram p v R (N R) (rho R) (I R) (Q R)) := by
    intro m p v hp hp1 hv0 hv
    dsimp only
    let B := ∑ j, v j^2/p j
    have hB : 0<B := by
      obtain ⟨j,hj⟩ := hv
      exact Finset.sum_pos' (fun i _ => div_nonneg (sq_nonneg _) (hp i).le)
        ⟨j,Finset.mem_univ _, div_pos (sq_pos_of_ne_zero hj) (hp j)⟩
    let d := fun j => v j/Real.sqrt B
    have hs : Real.sqrt B ≠ 0 := (Real.sqrt_pos.mpr hB).ne'
    have hd0 : ∑ j, d j=0 := by dsimp [d]; rw [← Finset.sum_div, hv0, zero_div]
    have hmoment (k l : ℕ) : (∑ j, d j^k/(p j)^l) =
        (∑ j, v j^k/(p j)^l)/(Real.sqrt B)^k := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [d]
      rw [div_pow]
      ring
    have hd : ∑ j, d j^2/p j=1 := by
      calc
        (∑ j, d j^2/p j) = B/B := by
          simpa only [pow_one, Real.sq_sqrt hB.le] using hmoment 2 1
        _ = 1 := div_self hB.ne'
    obtain ⟨N,rho,I,Q,hlim,hprog⟩ := actual_upper_family p d hp hp1 hd0 hd B hB
    have hvd : (fun j => Real.sqrt B*d j)=v := by
      funext j
      dsimp [d]
      field_simp
    have hpower (k : ℕ) : (Real.sqrt B)^(2*k)=B^k := by
      rw [pow_mul, Real.sq_sqrt hB.le]
    have hc : B^2/4*((∑ j, d j^4/(p j)^3)-1-(∑ j, d j^3/(p j)^2)^2) =
        ((∑ j, v j^4/(p j)^3)-B^2-(∑ j, v j^3/(p j)^2)^2/B)/4 := by
      rw [hmoment 3 2,hmoment 4 3,hpower 2,div_pow,←pow_mul]
      norm_num only [Nat.reduceMul]
      rw [hpower 3]
      field_simp
    rw [hc] at hlim
    rw [hvd] at hprog
    exact ⟨N,rho,I,Q,hlim,hprog⟩

  have coefficient_inequality (p v b A q e c x : ℝ)
      (hp : 0 < p) (hc : 0 < c) (he : e < 1)
      (hb : b = v/c) (hAf : A = (p-b*x-e*q)/(1-e)) (hpsd : b^2 ≤ A*q) :
      e*(q/p)^2-(1-(x/c)*(v/p))*(q/p)+(1-e)*(1/c^2)*(v/p)^2 ≤ 0 := by
    clear * - p v b A q e c x hp hc he hb hAf hpsd
    have ha : 0 < 1-e := sub_pos.mpr he
    have hap := (eq_div_iff ha.ne').mp hAf
    have hh := mul_le_mul_of_nonneg_left hpsd ha.le
    have hid : (e*(q/p)^2-(1-(x/c)*(v/p))*(q/p)+(1-e)*(1/c^2)*(v/p)^2)*p^2 =
        (1-e)*b^2-(p-b*x-e*q)*q := by
      rw [hb]
      field_simp [hp.ne', hc.ne']
      ring
    have hh' : (1-e)*b^2-(p-b*x-e*q)*q ≤ 0 := by
      nlinarith only [hh, congrArg (fun r : ℝ => r*q) hap]
    rw [← hid] at hh'
    exact nonpos_of_mul_nonpos_left hh' (sq_pos_of_pos hp)

  have coefficient_degeneration {ι : Type} [Fintype ι]
      (p v : ι → ℝ) (B : ℝ)
      (hp : ∀ j, 0 < p j) (hpsum : ∑ j, p j = 1)
      (hv : v ≠ 0) (hvsum : ∑ j, v j = 0)
      (hB : B = ∑ j, p j*(v j/p j)^2)
      (hthree : ∃ i j k, v i/p i ≠ v j/p j ∧ v i/p i ≠ v k/p k ∧ v j/p j ≠ v k/p k)
      (e c x Q : ℕ → ℝ) (q A b : ℕ → ι → ℝ)
      (he : ∀ n, 0 < e n ∧ e n ≤ 1/2) (hc : ∀ n, 0 < c n)
      (hq : ∀ n j, 0 ≤ q n j) (hA : ∀ n j, 0 ≤ A n j)
      (hqsum : ∀ n, ∑ j, q n j = 1)
      (hb : ∀ n j, b n j=v j/c n)
      (hAf : ∀ n j, A n j=(p j-b n j*x n-e n*q n j)/(1-e n))
      (hpsd : ∀ n j, b n j^2 ≤ A n j*q n j)
      (hinside : ∀ n, x n^2 < 4*e n*(1-e n))
      (hQf : ∀ n, Q n=c n^2*(4*e n*(1-e n))/(4*e n*(1-e n)-x n^2))
      (hQ : Tendsto Q atTop (𝓝 B)) :
      Tendsto e atTop (𝓝 0) ∧ Tendsto (fun n => c n^2) atTop (𝓝 B) ∧
      ∀ j, Tendsto (fun n => q n j) atTop (𝓝 (v j^2/(B*p j))) := by
    clear * - p v B hp hpsum hv hvsum hB hthree e c x Q q A b he hc hq hA hqsum hb hAf hpsd hinside hQf hQ coefficient_inequality
    have equality_obstruction
        (p s t : ι → ℝ) (B e u z : ℝ)
        (hp : ∀ j, 0 < p j) (hpsum : ∑ j, p j = 1)
        (hsum : ∑ j, p j * s j = 0) (hB : ∑ j, p j * s j ^ 2 = B)
        (ht : ∑ j, p j * t j = 1) (hBp : 0 < B)
        (he : 0 < e) (heh : e ≤ 1/2)
        (hcost : B * ((1-e)*z-e*u^2) = 1-e)
        (hF : ∀ j, e*t j^2-(1-2*e*u*s j)*t j+(1-e)*z*s j^2 ≤ 0)
        (hthree : ∃ i j k, s i ≠ s j ∧ s i ≠ s k ∧ s j ≠ s k) : False := by
      clear * - p s t B e u z hp hpsum hsum hB ht hBp he heh hcost hF hthree
      classical
      let L := (1-e)*z-e*u^2
      let r := fun j => t j-1+u*s j
      let F := fun j => e*t j^2-(1-2*e*u*s j)*t j+(1-e)*z*s j^2
      have hL : 0 < L := by dsimp [L]; nlinarith only [hcost,hBp,heh]
      have hid (j : ι) : F j = e*(r j)^2 + L*s j^2 + (2*e-1)*t j + 2*e*u*s j-e := by
        dsimp [F,r,L]; ring
      have hsumF : (∑ j, p j * F j) = e * ∑ j, p j * (r j)^2 := by
        simp_rw [hid]
        simp_rw [mul_sub, mul_add]
        simp only [sum_sub_distrib, sum_add_distrib]
        simp_rw [show ∀ j, p j * (e*r j^2) = e*(p j*r j^2) by intro; ring,
          show ∀ j, p j * (L*s j^2) = L*(p j*s j^2) by intro; ring,
          show ∀ j, p j * ((2*e-1)*t j) = (2*e-1)*(p j*t j) by intro; ring,
          show ∀ j, p j * (2*e*u*s j) = (2*e*u)*(p j*s j) by intro; ring]
        simp only [← mul_sum, ← sum_mul, hB, ht, hsum, hpsum]
        dsimp [L]
        linear_combination hcost
      have hnonpos : (∑ j, p j * F j) ≤ 0 :=
        sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hp j)) (hF j)
      have hrnonneg : ∀ j, 0 ≤ p j * (r j)^2 := fun j => mul_nonneg (hp j).le (sq_nonneg _)
      have hrzero : (∑ j, p j * (r j)^2) = 0 := by
        rw [hsumF] at hnonpos
        nlinarith only [he,hnonpos,sum_nonneg (s := univ) (fun j _ => hrnonneg j)]
      have hr (j : ι) : r j = 0 := by
        have hh := (sum_eq_zero_iff_of_nonneg (fun j _ => hrnonneg j)).mp hrzero j (mem_univ j)
        have : (r j)^2 = 0 := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hp j))
        exact sq_eq_zero_iff.mp this
      have hFzero : (∑ j, p j * F j) = 0 := by rw [hsumF,hrzero,mul_zero]
      have hroot (j : ι) : L * s j^2 + u*s j -(1-e) = 0 := by
        have hh := (sum_eq_zero_iff_of_nonpos (fun j _ =>
          mul_nonpos_of_nonneg_of_nonpos (hp j).le (hF j))).mp hFzero j (mem_univ j)
        have hh' : F j = 0 := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hp j))
        have htj : t j = 1-u*s j := by have := hr j; dsimp [r] at this; linarith only [this]
        rw [hid,hr,htj] at hh'
        linear_combination hh'
      obtain ⟨i,j,k,hij,hik,hjk⟩ := hthree
      have hd (a b : ι) (hab : s a ≠ s b) : L*(s a+s b)+u=0 := by
        have hh : (s a-s b)*(L*(s a+s b)+u)=0 := by
          linear_combination hroot a - hroot b
        exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hab)
      have hh : L*(s j-s k)=0 := by linear_combination hd i j hij - hd i k hik
      exact hjk (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt hL)))

    have normalized_convergence
        (p s : ι → ℝ) (B M : ℝ)
        (hp : ∀ j, 0 < p j) (hpsum : ∑ j, p j = 1)
        (hsum : ∑ j, p j * s j = 0) (hB : ∑ j, p j * s j^2 = B)
        (hBp : 0 < B)
        (hthree : ∃ i j k, s i ≠ s j ∧ s i ≠ s k ∧ s j ≠ s k)
        (e z k Q : ℕ → ℝ) (t : ℕ → ι → ℝ)
        (he : ∀ n, 0 < e n ∧ e n ≤ 1/2)
        (hz : ∀ n, 0 < z n ∧ z n ≤ M)
        (hk : ∀ n, -M ≤ k n ∧ k n ≤ M)
        (ht : ∀ n j, 0 ≤ t n j ∧ t n j ≤ 1 / p j)
        (htsum : ∀ n, ∑ j, p j*t n j = 1)
        (hF : ∀ n j, e n*t n j^2-(1-k n*s j)*t n j+(1-e n)*z n*s j^2 ≤ 0)
        (hinside : ∀ n, k n^2 ≤ 4*e n*(1-e n)*z n)
        (hcost : ∀ n, Q n*(4*e n*(1-e n)*z n-k n^2)=4*e n*(1-e n))
        (hlower : ∀ n, 1 ≤ Q n*z n)
        (hQ : Tendsto Q atTop (𝓝 B)) :
        Tendsto e atTop (𝓝 0) ∧ Tendsto z atTop (𝓝 (1/B)) ∧
          Tendsto k atTop (𝓝 0) ∧ ∀ j, Tendsto (fun n => t n j) atTop (𝓝 (s j^2/B)) := by
      clear * - p s B M hp hpsum hsum hB hBp hthree e z k Q t he hz hk ht htsum hF hinside hcost hlower hQ equality_obstruction
      classical
      let f : ℕ → ℝ × ℝ × ℝ × (ι → ℝ) := fun n => (e n,z n,k n,t n)
      let K : Set (ℝ × ℝ × ℝ × (ι → ℝ)) :=
        Set.Icc 0 (1/2) ×ˢ Set.Icc 0 M ×ˢ Set.Icc (-M) M ×ˢ Set.pi Set.univ (fun j => Set.Icc 0 (1/p j))
      have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod
        (isCompact_Icc.prod (isCompact_univ_pi fun j => isCompact_Icc)))
      have hfK : ∀ n, f n ∈ K := by
        intro n
        exact ⟨⟨(he n).1.le,(he n).2⟩,⟨(hz n).1.le,(hz n).2⟩,hk n,fun j _ => ht n j⟩
      have hconv : Tendsto f atTop (𝓝 (0,1/B,0,fun j => s j^2/B)) := by
        apply hK.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hfK)
        rintro ⟨E,Z,W,T⟩ hmem hcl
        obtain ⟨φ,hφ,hlim⟩ := hcl.tendsto_subseq
        have heL : Tendsto (e ∘ φ) atTop (𝓝 E) := hlim.fst_nhds
        have hzL : Tendsto (z ∘ φ) atTop (𝓝 Z) := hlim.snd_nhds.fst_nhds
        have hkL : Tendsto (k ∘ φ) atTop (𝓝 W) := hlim.snd_nhds.snd_nhds.fst_nhds
        have htL (j : ι) : Tendsto (fun n => t (φ n) j) atTop (𝓝 (T j)) :=
          (tendsto_pi_nhds.mp hlim.snd_nhds.snd_nhds.snd_nhds) j
        have hQL := hQ.comp hφ.tendsto_atTop
        have hEL : 0 ≤ E ∧ E ≤ 1/2 := hmem.1
        have hZL : 0 ≤ Z := hmem.2.1.1
        have hsumL : ∑ j, p j*T j = 1 := by
          have hh := tendsto_finsetSum Finset.univ (fun j _ => (htL j).const_mul (p j))
          exact tendsto_nhds_unique hh (by simpa only [htsum] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)))
        have hFL (j : ι) : E*T j^2-(1-W*s j)*T j+(1-E)*Z*s j^2 ≤ 0 := by
          apply le_of_tendsto' (((heL.mul ((htL j).pow 2)).sub
            ((tendsto_const_nhds.sub (hkL.mul_const (s j))).mul (htL j))).add
            (((tendsto_const_nhds.sub heL).mul hzL).mul_const (s j^2)))
          intro n; exact hF (φ n) j
        have hinsideL : W^2 ≤ 4*E*(1-E)*Z :=
          le_of_tendsto_of_tendsto (hkL.pow 2)
            (((heL.const_mul 4).mul (tendsto_const_nhds.sub heL)).mul hzL)
            (Eventually.of_forall fun n => hinside (φ n))
        have hcostL : B*(4*E*(1-E)*Z-W^2)=4*E*(1-E) := by
          apply tendsto_nhds_unique
            (hQL.mul ((((heL.const_mul 4).mul (tendsto_const_nhds.sub heL)).mul hzL).sub (hkL.pow 2)))
          exact (((heL.const_mul 4).mul (tendsto_const_nhds.sub heL))).congr' (Eventually.of_forall fun n => (hcost (φ n)).symm)
        have hlowL : 1 ≤ B*Z := ge_of_tendsto' (hQL.mul hzL) (fun n => hlower (φ n))
        have hE0 : E=0 := by
          by_contra hne
          have hep : 0 < E := lt_of_le_of_ne hEL.1 (Ne.symm hne)
          let u := W/(2*E)
          have hu : 2*E*u=W := by dsimp [u]; field_simp
          have hc : B*((1-E)*Z-E*u^2)=1-E := by
            have hh : 4*E*(B*((1-E)*Z-E*u^2)-(1-E))=0 := by
              linear_combination hcostL - congrArg (fun x : ℝ => B*x^2) hu
            have : B*((1-E)*Z-E*u^2)-(1-E)=0 :=
              (mul_eq_zero.mp hh).resolve_left (by positivity)
            linarith only [this]
          exact equality_obstruction p s T B E u Z hp hpsum hsum hB hsumL hBp hep hEL.2 hc
            (fun j => by rw [hu]; exact hFL j) hthree
        have hW0 : W=0 := by rw [hE0] at hinsideL; nlinarith only [hinsideL,sq_nonneg W]
        have hbound (j : ι) : Z*s j^2 ≤ T j := by
          have hh := hFL j; rw [hE0,hW0] at hh; nlinarith only [hh]
        have hZB : Z*B ≤ 1 := by
          have hh := sum_le_sum (fun j (_ : j ∈ (univ : Finset ι)) =>
            mul_le_mul_of_nonneg_left (hbound j) (hp j).le)
          simp_rw [show ∀ j, p j*(Z*s j^2)=Z*(p j*s j^2) by intro; ring] at hh
          rw [← mul_sum,hB,hsumL] at hh
          exact hh
        have hZe : Z=1/B := by apply (eq_div_iff (ne_of_gt hBp)).mpr; nlinarith only [hZB,hlowL]
        have hT (j : ι) : T j=s j^2/B := by
          have hgap : ∀ j, 0 ≤ p j*(T j-Z*s j^2) := fun j =>
            mul_nonneg (hp j).le (sub_nonneg.mpr (hbound j))
          have hsz : (∑ j, p j*(T j-Z*s j^2))=0 := by
            simp_rw [mul_sub,show ∀ j, p j*(Z*s j^2)=Z*(p j*s j^2) by intro; ring]
            rw [sum_sub_distrib,← mul_sum,hsumL,hB]
            nlinarith only [hZB,hlowL]
          have hh := (sum_eq_zero_iff_of_nonneg (fun j _ => hgap j)).mp hsz j (mem_univ j)
          have heq := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hp j))
          rw [hZe] at heq
          exact (sub_eq_zero.mp heq).trans (by ring)
        simp only [hE0,hZe,hW0,show T=(fun j => s j^2/B) from funext hT]
      exact ⟨hconv.fst_nhds,hconv.snd_nhds.fst_nhds,hconv.snd_nhds.snd_nhds.fst_nhds,
        fun j => (tendsto_pi_nhds.mp hconv.snd_nhds.snd_nhds.snd_nhds) j⟩
    classical
    let s := fun j => v j/p j
    let t := fun n j => q n j/p j
    let z := fun n => 1/(c n^2)
    let k := fun n => x n/c n
    obtain ⟨j₀,hvj⟩ := Function.ne_iff.mp hv
    change v j₀ ≠ 0 at hvj
    have hBp : 0 < B := by
      rw [hB]
      exact sum_pos' (fun j _ => mul_nonneg (hp j).le (sq_nonneg _))
        ⟨j₀,mem_univ _,mul_pos (hp _) (sq_pos_of_ne_zero (div_ne_zero hvj (ne_of_gt (hp _))))⟩
    have hsumS : (∑ j, p j*s j)=0 := by
      have hid (j : ι) : p j*s j=v j := by dsimp [s]; field_simp [ne_of_gt (hp j)]
      simpa only [hid] using hvsum
    have htSum (n : ℕ) : (∑ j, p j*t n j)=1 := by
      have hid (j : ι) : p j*t n j=q n j := by dsimp [t]; field_simp [ne_of_gt (hp j)]
      simpa only [hid] using hqsum n
    have hq1 (n : ℕ) (j : ι) : q n j ≤ 1 := by
      rw [← hqsum n]; exact single_le_sum (fun j _ => hq n j) (mem_univ _)
    have hbSum (n : ℕ) : (∑ j, b n j)=0 := by
      simp_rw [hb]; rw [← sum_div,hvsum,zero_div]
    have hASum (n : ℕ) : (∑ j, A n j)=1 := by
      have haNE : 1-e n ≠ 0 := by have := (he n).2; linarith only [this]
      simp_rw [hAf]; rw [← sum_div]
      simp_rw [sum_sub_distrib,← sum_mul,← mul_sum]
      rw [hpsum,hbSum,hqsum]
      field_simp [haNE]; ring
    have hA1 (n : ℕ) (j : ι) : A n j ≤ 1 := by
      rw [← hASum n]; exact single_le_sum (fun j _ => hA n j) (mem_univ _)
    have hzbound (n : ℕ) : z n ≤ 1/(v j₀^2) := by
      have hb1 : b n j₀^2 ≤ 1 := (hpsd n j₀).trans
        ((mul_le_mul (hA1 n j₀) (hq1 n j₀) (hq n j₀) (by norm_num)).trans (by norm_num))
      rw [hb,div_pow] at hb1
      have hc2 : 0 < c n^2 := sq_pos_of_pos (hc n)
      have hv2 : 0 < v j₀^2 := sq_pos_of_ne_zero hvj
      have hvle : v j₀^2 ≤ c n^2 := (div_le_one hc2).mp hb1
      exact one_div_le_one_div_of_le hv2 hvle
    let M := 1+1/(v j₀^2)
    have hM1 : 1 ≤ M := by
      have hh : 0 ≤ 1/(v j₀^2) := by positivity
      dsimp [M]; linarith
    have hk2 (n : ℕ) : k n^2 ≤ z n := by
      have hH : 4*e n*(1-e n) ≤ 1 := by nlinarith only [sq_nonneg (2*e n-1)]
      dsimp [k,z]; rw [div_pow]
      exact div_le_div_of_nonneg_right ((hinside n).le.trans hH) (sq_nonneg _)
    have hkn (n : ℕ) : -M ≤ k n ∧ k n ≤ M := by
      have hzM : z n ≤ M := le_trans (hzbound n) (by dsimp [M]; linarith)
      have hh := hk2 n
      constructor <;> nlinarith only [hzM,hh,hM1,sq_nonneg (k n+M),sq_nonneg (k n-M)]
    have hzn (n : ℕ) : 0 < z n ∧ z n ≤ M :=
      ⟨one_div_pos.mpr (sq_pos_of_pos (hc n)),(hzbound n).trans (by dsimp [M]; linarith)⟩
    have htn (n : ℕ) (j : ι) : 0 ≤ t n j ∧ t n j ≤ 1/p j :=
      ⟨div_nonneg (hq n j) (hp j).le,div_le_div_of_nonneg_right (hq1 n j) (hp j).le⟩
    have hfn (n : ℕ) (j : ι) :
        e n*t n j^2-(1-k n*s j)*t n j+(1-e n)*z n*s j^2 ≤ 0 := by
      exact coefficient_inequality (p j) (v j) (b n j) (A n j) (q n j) (e n) (c n) (x n)
        (hp j) (hc n) (lt_of_le_of_lt (he n).2 (by norm_num)) (hb n j) (hAf n j) (hpsd n j)

    have hIn (n : ℕ) : k n^2 ≤ 4*e n*(1-e n)*z n := by
      dsimp [k,z]; rw [div_pow]
      simpa only [div_eq_mul_inv,one_mul,mul_assoc] using
        div_le_div_of_nonneg_right (hinside n).le (sq_nonneg (c n))
    have hCost (n : ℕ) : Q n*(4*e n*(1-e n)*z n-k n^2)=4*e n*(1-e n) := by
      have hh := (eq_div_iff (ne_of_gt (sub_pos.mpr (hinside n)))).mp (hQf n)
      dsimp only [z,k]
      rw [div_pow, mul_one_div, ← sub_div, ← mul_div_assoc]
      exact (div_eq_iff (ne_of_gt (sq_pos_of_pos (hc n)))).mpr (by nlinarith only [hh])
    have hlow (n : ℕ) : 1 ≤ Q n*z n := by
      have hepos := (he n).1
      have hale : 0 < 1-e n := by have := (he n).2; linarith only [this]
      have hQpos : 0 < Q n := by
        rw [hQf]
        exact div_pos (mul_pos (sq_pos_of_pos (hc n)) (mul_pos (mul_pos (by norm_num) hepos) hale))
          (sub_pos.mpr (hinside n))
      have hh := hCost n
      have hnn := mul_nonneg hQpos.le (sq_nonneg (k n))
      have hH : 0 < 4*e n*(1-e n) := by positivity
      nlinarith only [hh,hnn,hH]
    obtain ⟨he0,hz0,hk0,ht0⟩ := normalized_convergence p s B M hp hpsum hsumS hB.symm hBp
      hthree e z k Q t he hzn hkn htn htSum hfn hIn hCost hlow hQ
    have hc0 : Tendsto (fun n => c n^2) atTop (𝓝 B) := by
      have hh := hz0.inv₀ (by positivity : (1/B : ℝ) ≠ 0)
      simpa [z] using hh
    refine ⟨he0,hc0,fun j => ?_⟩
    have hh := (ht0 j).const_mul (p j)
    convert hh using 1
    · ext n; dsimp [t]; field_simp [ne_of_gt (hp j)]
    · dsimp [s]; field_simp [ne_of_gt (hp j)]

  have coefficient_matching_lower {ι : Type} [Fintype ι]
      (p v : ι → ℝ) (B : ℝ)
      (hp : ∀ j, 0 < p j) (hpsum : ∑ j, p j = 1)
      (hv : v ≠ 0) (hvsum : ∑ j, v j = 0)
      (hB : B = ∑ j, p j*(v j/p j)^2)
      (hthree : ∃ i j k, v i/p i ≠ v j/p j ∧ v i/p i ≠ v k/p k ∧ v j/p j ≠ v k/p k)
      (e c x Q : ℕ → ℝ) (q A b : ℕ → ι → ℝ)
      (he : ∀ n, 0 < e n ∧ e n ≤ 1/2) (hc : ∀ n, 0 < c n)
      (hq : ∀ n j, 0 ≤ q n j) (hA : ∀ n j, 0 ≤ A n j)
      (hqsum : ∀ n, ∑ j, q n j = 1)
      (hb : ∀ n j, b n j=v j/c n)
      (hAf : ∀ n j, A n j=(p j-b n j*x n-e n*q n j)/(1-e n))
      (hpsd : ∀ n j, b n j^2 ≤ A n j*q n j)
      (hinside : ∀ n, x n^2 < 4*e n*(1-e n))
      (hQf : ∀ n, Q n=c n^2*(4*e n*(1-e n))/(4*e n*(1-e n)-x n^2))
      (hQ : Tendsto Q atTop (𝓝 B))
      (R : ℕ → ℝ) (hR : ∀ n,0 < R n)
      (hRadius : ∀ n,c n^2*R n^2 ≤ 4*e n*(1-e n)) :
      let V := (∑ j,p j*(v j/p j)^4)-B^2-(∑ j,p j*(v j/p j)^3)^2/B
      ∀ d : ℝ,d < V/4 → ∀ᶠ n in atTop,d ≤ (Q n-B)/R n^2 := by
    have finite_matching_gap
        (p s t : ι → ℝ) (B e z k Q c R C D : ℝ)
        (hp : ∀ j, 0 ≤ p j) (hs : ∑ j,p j*s j=0)
        (hp1 : ∑ j,p j=1) (ht1 : ∑ j,p j*t j=1)
        (hB : ∑ j,p j*s j^2=B) (hBp : 0 < B)
        (hC : C=∑ j,p j*s j*(t j-1)) (hD : D=∑ j,p j*(t j-1)^2)
        (he : 0 < e) (hea : e < 1) (hQ : 0 < Q) (hR : 0 < R)
        (hF : ∀ j,e*t j^2-(1-k*s j)*t j+(1-e)*z*s j^2 ≤ 0)
        (hcost : Q*(4*e*(1-e)*z-k^2)=4*e*(1-e))
        (hradius : c^2*R^2 ≤ 4*e*(1-e)) :
        Q*c^2*(B*D-C^2)/(4*(1-e)^2*B) ≤ (Q-B)/R^2 := by
      clear * - p s t B e z k Q c R C D hp hs hp1 ht1 hB hBp hC hD he hea hQ hR hF hcost hradius
      classical
      let F := fun j => e*t j^2-(1-k*s j)*t j+(1-e)*z*s j^2
      have hsumF : (∑ j,p j*F j)=e*D+k*C+(1-e)*z*B-(1-e) := by
        have hid (j : ι) : p j*F j = e*(p j*(t j-1)^2) + k*(p j*s j*(t j-1)) +
            ((1-e)*z)*(p j*s j^2) + (2*e-1)*(p j*t j)+k*(p j*s j)-e*p j := by dsimp [F]; ring
        simp_rw [hid]
        simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,← hC,← hD,hB,ht1,hs,hp1]
        ring
      have hFnonpos : e*D+k*C+(1-e)*z*B-(1-e) ≤ 0 := by
        rw [← hsumF]
        exact sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hp j) (hF j)
      have hres : 0 ≤ B*D-C^2 := by
        have hid (j : ι) : p j*(B*(t j-1)-C*s j)^2 =
            B^2*(p j*(t j-1)^2)-2*B*C*(p j*s j*(t j-1))+C^2*(p j*s j^2) := by ring
        have hnn : 0 ≤ ∑ j,p j*(B*(t j-1)-C*s j)^2 := sum_nonneg fun j _ => mul_nonneg (hp j) (sq_nonneg _)
        simp_rw [hid] at hnn
        simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,← hD,← hC,hB] at hnn
        have hh : 0 ≤ B*(B*D-C^2) := by nlinarith only [hnn]
        exact nonneg_of_mul_nonneg_right hh hBp
      have hgap : Q*e*(B*D-C^2) ≤ (Q-B)*(1-e)*B := by
        have hid : 4*e*((Q-B)*(1-e)*B-Q*e*(B*D-C^2)) =
            Q*(2*e*C+B*k)^2-4*e*Q*B*(e*D+k*C+(1-e)*z*B-(1-e)) := by
          linear_combination congrArg (fun x : ℝ => B^2*x) hcost
        have hnn := mul_nonneg hQ.le (sq_nonneg (2*e*C+B*k))
        have hnp := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4*e*Q*B by positivity) hFnonpos
        nlinarith only [hid,hnn,hnp,he]
      have ha : 0 < 1-e := sub_pos.mpr hea
      have h1 := mul_le_mul_of_nonneg_left hradius (mul_nonneg hQ.le hres)
      have h2 := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 4*(1-e) by positivity)
      apply (div_le_div_iff₀ (by positivity : 0 < 4*(1-e)^2*B) (sq_pos_of_pos hR)).mpr
      nlinarith only [h1,h2]

    have matching_lower_of_limits
        (p s : ι → ℝ) (B : ℝ) (hp : ∀ j,0 ≤ p j)
        (hp1 : ∑ j,p j=1) (hs : ∑ j,p j*s j=0)
        (hB : ∑ j,p j*s j^2=B) (hBp : 0 < B)
        (e z k Q c R : ℕ → ℝ) (t : ℕ → ι → ℝ)
        (he : ∀ n,0 < e n ∧ e n < 1) (hQp : ∀ n,0 < Q n) (hR : ∀ n,0 < R n)
        (ht1 : ∀ n,∑ j,p j*t n j=1)
        (hF : ∀ n j,e n*t n j^2-(1-k n*s j)*t n j+(1-e n)*z n*s j^2 ≤ 0)
        (hcost : ∀ n,Q n*(4*e n*(1-e n)*z n-k n^2)=4*e n*(1-e n))
        (hradius : ∀ n,c n^2*R n^2 ≤ 4*e n*(1-e n))
        (he0 : Tendsto e atTop (𝓝 0)) (hQ0 : Tendsto Q atTop (𝓝 B))
        (hc0 : Tendsto (fun n => c n^2) atTop (𝓝 B))
        (ht0 : ∀ j,Tendsto (fun n => t n j) atTop (𝓝 (s j^2/B))) :
        let V := (∑ j,p j*s j^4)-B^2-(∑ j,p j*s j^3)^2/B
        ∀ d : ℝ,d < V/4 → ∀ᶠ n in atTop,d ≤ (Q n-B)/R n^2 := by
      clear * - p s B hp hp1 hs hB hBp e z k Q c R t he hQp hR ht1 hF hcost hradius he0 hQ0 hc0 ht0 finite_matching_gap
      classical
      let C := fun n => ∑ j,p j*s j*(t n j-1)
      let D := fun n => ∑ j,p j*(t n j-1)^2
      let C₀ := ∑ j,p j*s j*(s j^2/B-1)
      let D₀ := ∑ j,p j*(s j^2/B-1)^2
      have hC0 : Tendsto C atTop (𝓝 C₀) :=
        tendsto_finsetSum _ (fun j _ => ((ht0 j).sub tendsto_const_nhds).const_mul (p j*s j))
      have hD0 : Tendsto D atTop (𝓝 D₀) :=
        tendsto_finsetSum _ (fun j _ => (((ht0 j).sub tendsto_const_nhds).pow 2).const_mul (p j))
      let L := fun n => Q n*c n^2*(B*D n-C n^2)/(4*(1-e n)^2*B)
      have hL0 : Tendsto L atTop (𝓝 (B*(B*D₀-C₀^2)/4)) := by
        have hh := ((hQ0.mul hc0).mul ((hD0.const_mul B).sub (hC0.pow 2))).div
          ((((tendsto_const_nhds.sub he0).pow 2).const_mul 4).mul_const B)
          (show 4*(1-(0:ℝ))^2*B ≠ 0 by positivity)
        have hval : B*B*(B*D₀-C₀^2)/(4*(1-(0:ℝ))^2*B) = B*(B*D₀-C₀^2)/4 := by
          field_simp
          norm_num
        rw [hval] at hh
        exact hh
      have hCeq : C₀ = (∑ j,p j*s j^3)/B := by
        have hid (j : ι) : p j*s j*(s j^2/B-1)=(p j*s j^3)/B-p j*s j := by ring
        dsimp [C₀]; simp_rw [hid]; rw [sum_sub_distrib,← sum_div,hs,sub_zero]
      have hDeq : D₀ = (∑ j,p j*s j^4)/B^2-1 := by
        have hid (j : ι) : p j*(s j^2/B-1)^2=(p j*s j^4)/B^2-2*(p j*s j^2)/B+p j := by ring
        dsimp [D₀]; simp_rw [hid]
        simp only [sum_add_distrib,sum_sub_distrib,← sum_div,← mul_sum,hB,hp1]
        field_simp
        ring
      have hcoef : B*(B*D₀-C₀^2)/4 = ((∑ j,p j*s j^4)-B^2-(∑ j,p j*s j^3)^2/B)/4 := by
        rw [hCeq,hDeq]; field_simp
      have hle (n : ℕ) : L n ≤ (Q n-B)/R n^2 :=
        finite_matching_gap p s (t n) B (e n) (z n) (k n) (Q n) (c n) (R n) (C n) (D n)
          hp hs hp1 (ht1 n) hB hBp rfl rfl (he n).1 (he n).2 (hQp n) (hR n)
          (hF n) (hcost n) (hradius n)
      dsimp only
      intro d hd
      rw [hcoef] at hL0
      exact (hL0.eventually_const_lt hd).mono (fun n hn => hn.le.trans (hle n))
    classical
    let s := fun j => v j/p j
    let t := fun n j => q n j/p j
    let z := fun n => 1/(c n^2)
    let k := fun n => x n/c n
    obtain ⟨j₀,hvj⟩ := Function.ne_iff.mp hv
    change v j₀ ≠ 0 at hvj
    have hBp : 0 < B := by
      rw [hB]
      exact sum_pos' (fun j _ => mul_nonneg (hp j).le (sq_nonneg _))
        ⟨j₀,mem_univ _,mul_pos (hp _) (sq_pos_of_ne_zero (div_ne_zero hvj (ne_of_gt (hp _))))⟩
    have hsumS : (∑ j, p j*s j)=0 := by
      have hid (j : ι) : p j*s j=v j := by dsimp [s]; field_simp [ne_of_gt (hp j)]
      simpa only [hid] using hvsum
    have htSum (n : ℕ) : (∑ j, p j*t n j)=1 := by
      have hid (j : ι) : p j*t n j=q n j := by dsimp [t]; field_simp [ne_of_gt (hp j)]
      simpa only [hid] using hqsum n
    have hfn (n : ℕ) (j : ι) :
        e n*t n j^2-(1-k n*s j)*t n j+(1-e n)*z n*s j^2 ≤ 0 := by
      exact coefficient_inequality (p j) (v j) (b n j) (A n j) (q n j) (e n) (c n) (x n)
        (hp j) (hc n) (lt_of_le_of_lt (he n).2 (by norm_num)) (hb n j) (hAf n j) (hpsd n j)

    have hCost (n : ℕ) : Q n*(4*e n*(1-e n)*z n-k n^2)=4*e n*(1-e n) := by
      have hh := (eq_div_iff (ne_of_gt (sub_pos.mpr (hinside n)))).mp (hQf n)
      dsimp only [z,k]
      rw [div_pow, mul_one_div, ← sub_div, ← mul_div_assoc]
      exact (div_eq_iff (ne_of_gt (sq_pos_of_pos (hc n)))).mpr (by nlinarith only [hh])

    obtain ⟨he0,hc0,hq0⟩ := coefficient_degeneration p v B hp hpsum hv hvsum hB hthree
      e c x Q q A b he hc hq hA hqsum hb hAf hpsd hinside hQf hQ
    have ht0 (j : ι) : Tendsto (fun n => t n j) atTop (𝓝 (s j^2/B)) := by
      dsimp only [t]
      convert (hq0 j).div_const (p j) using 1
      dsimp [s]
      field_simp [ne_of_gt (hp j),ne_of_gt hBp]
    have hQp (n : ℕ) : 0 < Q n := by
      have ha : 0 < 1-e n := by have := (he n).2; linarith only [this]
      rw [hQf]
      exact div_pos (mul_pos (sq_pos_of_pos (hc n))
        (mul_pos (mul_pos (by norm_num) (he n).1) ha)) (sub_pos.mpr (hinside n))
    exact matching_lower_of_limits p s B (fun j => (hp j).le) hpsum hsumS hB.symm hBp
      e z k Q c R t (fun n => ⟨(he n).1,lt_of_le_of_lt (he n).2 (by norm_num)⟩)
      hQp hR htSum hfn hCost hRadius he0 hQ hc0 ht0

  have actual_rank_two_lower {m : ℕ}
      (p v : Fin m → ℝ) (B : ℝ)
      (hp : ∀ j, 0 < p j) (hpsum : ∑ j, p j = 1)
      (hv : v ≠ 0) (hvsum : ∑ j, v j = 0)
      (hB : B = ∑ j, p j*(v j/p j)^2)
      (hthree : ∃ i j k, v i/p i ≠ v j/p j ∧ v i/p i ≠ v k/p k ∧ v j/p j ≠ v k/p k)
      (N : ℕ → Fin m → Matrix (Fin 2) (Fin 2) ℂ)
      (rho : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
      (I : ℕ → Set ℝ) (R : ℕ → ℝ)
      (hI : ∀ n, IsOpen (I n)) (hconn : ∀ n, IsPreconnected (I n))
      (h0 : ∀ n, 0 ∈ I n) (hR : ∀ n, 0 < R n)
      (hRI : ∀ n, Set.Icc (-R n) (R n) ⊆ I n)
      (hN : ∀ n j, (N n j).PosSemidef) (hnorm : ∀ n, ∑ j, N n j = 1)
      (hc : ∀ n, ContDiffOn ℝ 1 (rho n) (I n))
      (hrho : ∀ n u, u ∈ I n → (rho n u).PosSemidef ∧
        Matrix.trace (rho n u) = 1 ∧ rho n u * rho n u = rho n u)
      (hread : ∀ n u, u ∈ I n → ∀ j, (Matrix.trace (N n j * rho n u)).re = p j+u*v j)
      (hrank : ∀ n, Module.finrank ℝ (effectReadout (N n)).range = 2)
      (hQ : Tendsto (fun n => spectralQFI (rho n 0)
        (deriv (rho n) 0) (hrho n 0 (h0 n)).1) atTop (𝓝 B)) :
      let V := (∑ j,p j*(v j/p j)^4)-B^2-(∑ j,p j*(v j/p j)^3)^2/B
      ∀ d : ℝ, d < V/4 → ∀ᶠ n in atTop,
        d ≤ (spectralQFI (rho n 0) (deriv (rho n) 0)
          (hrho n 0 (h0 n)).1-B)/R n^2 := by
    have htransfer : ∀
      (rho : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (I : Set ℝ)
      (hI : IsOpen I) (h0 : 0 ∈ I) (hc : ContDiffOn ℝ 1 rho I)
      (hrho : ∀ u ∈ I, (rho u).PosSemidef ∧ Matrix.trace (rho u) = 1 ∧ rho u * rho u = rho u)
      (O : (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3))) (x c ε s : ℝ) (hs : s=1 ∨ s= -1)
      (hinside : x^2 < 4*ε*(1-ε))
      (hcoord : ∀ u ∈ I, reframe O (rho u) = blochMatrix 1 (WithLp.toLp 2
        ![x+c*u,s*Real.sqrt (4*ε*(1-ε)-(x+c*u)^2),1-2*ε])),
      spectralQFI (rho 0) (deriv rho 0) (hrho 0 h0).1 =
        c^2*(4*ε*(1-ε))/(4*ε*(1-ε)-x^2) := by
      clear * - coefficient_matching_lower
      classical
      have matrix_energy (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) :
          2*(Matrix.trace (M*M)).re=(Matrix.trace M).re^2+‖bloch M‖^2 := by
        have hre (i j : Fin 2) : (M i j).re = (M j i).re := by
          simpa using congrArg Complex.re (hM.apply j i)
        have him (i j : Fin 2) : -(M i j).im = (M j i).im := by
          simpa using congrArg Complex.im (hM.apply j i)
        have h00 : (M 0 0).im = 0 := by linarith [him 0 0]
        have h11 : (M 1 1).im = 0 := by linarith [him 1 1]
        simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, bloch,
          EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h00, h11, hre 1 0, ← him 0 1]
        ring
      have bloch_energy (a : ℝ) (r : EuclideanSpace ℝ (Fin 3)) :
          2*(Matrix.trace (blochMatrix a r * blochMatrix a r)).re=a^2+‖r‖^2 := by
        simp [Matrix.trace, Matrix.mul_apply, blochMatrix, Fin.sum_univ_two,
          EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
        ring
      have reframe_energy (O : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
          (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.IsHermitian) :
          2*(Matrix.trace (reframe O M*reframe O M)).re=2*(Matrix.trace (M*M)).re := by
        rw [reframe, bloch_energy, matrix_energy M hM, O.norm_map]

      have pure_energy {n : Type} [Fintype n] [DecidableEq n] (rho B : Matrix n n ℂ)
          (hp : rho.PosSemidef) (hB : B.IsHermitian) (htan : B*rho+rho*B=B) :
          spectralQFI rho B hp = 2*(Matrix.trace (B*B)).re := by
        classical
        let U := hp.isHermitian.eigenvectorUnitary
        let d : n → ℂ := fun i => (hp.isHermitian.eigenvalues i : ℂ)
        let M := star (U : Matrix n n ℂ) * B * U
        have hM : M.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul _ hB
        have hu : star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 := U.property.1
        have hu' : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := U.property.2
        have hdiag : star (U : Matrix n n ℂ) * rho * (U : Matrix n n ℂ) = diagonal d := by
          conv_lhs => rw [hp.isHermitian.spectral_theorem]
          simp [U, d, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc, Unitary.coe_star_mul_self, one_mul]
        have hentry (i j : n) : M i j * (d i+d j) = M i j := by
          have he := congrArg (fun X : Matrix n n ℂ =>
            (star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) i j) htan
          have heq : star (U : Matrix n n ℂ) * (B*rho+rho*B) * U =
              M*diagonal d+diagonal d*M := by
            rw [← hdiag]
            dsimp only [M]
            simp only [mul_add, add_mul, Matrix.mul_assoc, ← mul_assoc (U : Matrix n n ℂ), hu', one_mul]
          rw [heq] at he
          simp only [Matrix.add_apply, mul_diagonal, diagonal_mul] at he
          change M i j*d j+d i*M i j=M i j at he
          linear_combination he
        have hterm (i j : n) : 2*Complex.normSq (M i j) /
            (hp.isHermitian.eigenvalues i+hp.isHermitian.eigenvalues j) = 2*Complex.normSq (M i j) := by
          by_cases hz : M i j=0
          · simp [hz]
          · have hs : d i+d j=1 := mul_left_cancel₀ hz (by simpa using hentry i j)
            have hsR : hp.isHermitian.eigenvalues i+hp.isHermitian.eigenvalues j=1 := by
              simpa [d] using congrArg Complex.re hs
            rw [hsR, div_one]
        have ht : (B*B).trace=(M*M).trace := by
          dsimp only [M]
          simp only [Matrix.mul_assoc, ← mul_assoc (U : Matrix n n ℂ), hu', one_mul]
          rw [trace_mul_comm (star (U : Matrix n n ℂ))]
          simp only [Matrix.mul_assoc, hu', mul_one]
        rw [ht]
        unfold spectralQFI
        change (∑ i, ∑ j, 2*Complex.normSq (M i j) / _) = _
        simp_rw [hterm]
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [← hM.apply j i]
        simp [Complex.mul_conj, Complex.normSq_apply]

      intro rho I hI h0 hc hrho O x c ε s hs hinside hcoord
      let D := deriv rho 0
      have hd : HasDerivAt rho D 0 :=
        (hc.differentiableOn (by norm_num) 0 h0).differentiableAt (hI.mem_nhds h0) |>.hasDerivAt
      have he (i j : Fin 2) : HasDerivAt (fun u => rho u i j) (D i j) 0 :=
        hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) j
      have hD : D.IsHermitian := by
        apply Matrix.IsHermitian.ext
        intro i j
        apply (he j i).star.unique
        apply (he i j).congr_of_eventuallyEq
        filter_upwards [hI.mem_nhds h0] with u hu
        exact (hrho u hu).1.isHermitian.apply i j
      have hprod : HasDerivAt (fun u => rho u * rho u) (D*rho 0+rho 0*D) 0 := by
        apply hasDerivAt_pi.mpr
        intro i
        apply hasDerivAt_pi.mpr
        intro j
        simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
        exact HasDerivAt.fun_sum fun k _ => (he i k).mul (he k j)
      have htan : D*rho 0+rho 0*D=D := by
        apply hprod.unique
        apply hd.congr_of_eventuallyEq
        filter_upwards [hI.mem_nhds h0] with u hu
        exact (hrho u hu).2.2
      have hpureQ := pure_energy (rho 0) D (hrho 0 h0).1 hD htan
      let y := Real.sqrt (4*ε*(1-ε)-x^2)
      have hy : 0 < y := Real.sqrt_pos.mpr (sub_pos.mpr hinside)
      have hy2 : y^2=4*ε*(1-ε)-x^2 := Real.sq_sqrt (sub_nonneg.mpr hinside.le)
      let r := blochMatrix 1 (WithLp.toLp 2 ![x,s*y,1-2*ε])
      let d := blochMatrix 0 (WithLp.toLp 2 ![c,-s*x*c/y,0])
      have hx : HasDerivAt (fun u : ℝ => x+c*u) c 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).const_mul c).const_add x
      have hys : HasDerivAt (fun u : ℝ => s*Real.sqrt (4*ε*(1-ε)-(x+c*u)^2))
          (-s*x*c/y) 0 := by
        have hh := (((hasDerivAt_const (0:ℝ) (4*ε*(1-ε))).sub (hx.pow 2)).sqrt
          (by simpa using ne_of_gt (sub_pos.mpr hinside))).const_mul s
        convert hh using 1 <;> first | rfl | (dsimp [y]; ring)
      have hxC : HasDerivAt (fun u : ℝ => ((x+c*u : ℝ):ℂ)) (c:ℂ) 0 :=
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hx
      have hyC : HasDerivAt (fun u : ℝ => ((s*Real.sqrt (4*ε*(1-ε)-(x+c*u)^2):ℝ):ℂ))
          ((-s*x*c/y:ℝ):ℂ) 0 := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hys
      have harc : HasDerivAt (fun u : ℝ => blochMatrix 1 (WithLp.toLp 2
          ![x+c*u,s*Real.sqrt (4*ε*(1-ε)-(x+c*u)^2),1-2*ε])) d 0 := by
        apply hasDerivAt_pi.mpr
        intro i
        apply hasDerivAt_pi.mpr
        intro j
        fin_cases i <;> fin_cases j
        · simpa [blochMatrix,d] using hasDerivAt_const (0:ℝ) (((1+(1-2*ε):ℝ):ℂ)/2)
        · exact (hxC.sub (hyC.mul_const Complex.I)).div_const 2
        · exact (hxC.add (hyC.mul_const Complex.I)).div_const 2
        · simpa [blochMatrix,d] using hasDerivAt_const (0:ℝ) (((1-(1-2*ε):ℝ):ℂ)/2)
      have hframe : HasDerivAt (fun u => reframe O (rho u)) (reframe O D) 0 :=
        (reframeLinear O).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hd
      have hDd : reframe O D=d := by
        apply hframe.unique
        apply harc.congr_of_eventuallyEq
        filter_upwards [hI.mem_nhds h0] with u hu
        exact hcoord u hu
      have hpair : 2*(Matrix.trace (d*d)).re=2*(Matrix.trace (D*D)).re := by
        rw [← hDd]
        exact reframe_energy O D hD
      have hdd : 2*(Matrix.trace (d*d)).re = c^2+(s*x*c/y)^2 := by
        rw [bloch_energy]
        simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
        ring
      have hs2 : s^2=1 := by rcases hs with rfl | rfl <;> norm_num
      change spectralQFI (rho 0) D (hrho 0 h0).1 = _
      rw [hpureQ, ← hpair, hdd]
      simp only [div_pow, mul_pow, hs2, one_mul, hy2]
      field_simp [ne_of_gt (sub_pos.mpr hinside)]
      <;> ring

    classical
    choose basis x c e s A q b hcpos hepos hele hs
      hcoeff hqsum hcoord hinside hend using fun n =>
        actual_rank_two_parameters (N n) (rho n) p v (I n) (hI n) (hconn n)
          (h0 n) hv (hN n) (hnorm n) (hc n) (hrho n) (hread n) (hrank n)
    let Q := fun n => spectralQFI (rho n 0) (deriv (rho n) 0)
      (hrho n 0 (h0 n)).1
    have hQf (n : ℕ) : Q n = c n^2*(4*e n*(1-e n))/(4*e n*(1-e n)-x n^2) := by
      exact htransfer (rho n) (I n) (hI n) (h0 n) (hc n) (hrho n)
        (basis n).repr (x n) (c n) (e n) (s n) (hs n)
        (by simpa only [mul_zero, add_zero] using hinside n 0 (h0 n)) (hcoord n)
    have hRadius (n : ℕ) : c n^2*R n^2 ≤ 4*e n*(1-e n) := by
      have he1 : 0 ≤ 1-e n := by linarith [hele n]
      have hk : 0 ≤ 4*e n*(1-e n) :=
        mul_nonneg (mul_nonneg (by norm_num) (hepos n).le) he1
      have hb := hend n (R n) (hR n).le (hRI n)
      have hcR : 0 ≤ c n*R n := mul_nonneg (hcpos n).le (hR n).le
      have hb' : c n*R n < Real.sqrt (4*e n*(1-e n)) := by
        linarith [abs_nonneg (x n)]
      have hsq := mul_self_le_mul_self hcR hb'.le
      rw [← pow_two, ← pow_two, Real.sq_sqrt hk] at hsq
      nlinarith only [hsq]
    exact coefficient_matching_lower p v B hp hpsum hv hvsum hB
      hthree e c x Q q A b (fun n => ⟨hepos n,hele n⟩) hcpos
      (fun n j => (hcoeff n j).1) (fun n j => (hcoeff n j).2.1) hqsum
      (fun n j => (hcoeff n j).2.2.2.1) (fun n j => (hcoeff n j).2.2.2.2)
      (fun n j => (hcoeff n j).2.2.1) (fun n => by simpa using hinside n 0 (h0 n))
      hQf hQ R hR hRadius

  have score_separation {ι : Type} [Fintype ι]
      (p s : ι → ℝ) (hp : ∀ j, 0<p j) (hp1 : ∑ j,p j=1)
      (hs : ∑ j,p j*s j=0)
      (hthree : ∃ i j k, s i≠s j ∧ s i≠s k ∧ s j≠s k) :
      let B := ∑ j,p j*s j^2
      let V := (∑ j,p j*s j^4)-B^2-(∑ j,p j*s j^3)^2/B
      0<B ∧ 0<V ∧ ∃ lo hi, s lo<0 ∧ 0<s hi ∧ B < -s lo*s hi := by
    clear * - p s hp hp1 hs hthree
    classical
    dsimp only
    let B := ∑ j,p j*s j^2
    let C := ∑ j,p j*s j^3
    let D := ∑ j,p j*s j^4
    obtain ⟨i,j,k,hij,hik,hjk⟩ := hthree
    have hsne : ∃ a, s a≠0 := by by_contra! h; exact hij ((h i).trans (h j).symm)
    obtain ⟨a,ha⟩ := hsne
    have hB : 0<B := sum_pos' (fun j _ => mul_nonneg (hp j).le (sq_nonneg _))
      ⟨a,mem_univ _,mul_pos (hp a) (sq_pos_of_ne_zero ha)⟩
    have hrid : (∑ j,p j*(s j^2-B-C/B*s j)^2)=D-B^2-C^2/B := by
      have hid (j : ι) : p j*(s j^2-B-C/B*s j)^2 =
          p j*s j^4 - 2*(C/B)*(p j*s j^3) + ((C/B)^2-2*B)*(p j*s j^2) +
          (2*C)*(p j*s j) + B^2*p j := by
        field_simp
        <;> ring
      simp_rw [hid]
      simp only [sum_add_distrib,sum_sub_distrib,←mul_sum,hp1,hs,mul_zero,add_zero,mul_one]
      change D-2*(C/B)*C+((C/B)^2-2*B)*B+B^2=D-B^2-C^2/B
      field_simp
      <;> ring
    have hV : 0<D-B^2-C^2/B := by
      rw [←hrid]
      apply sum_pos'
      · intro j _; exact mul_nonneg (hp j).le (sq_nonneg _)
      · by_contra! h
        have hz (a : ι) : s a^2-B-C/B*s a=0 := by
          have hh := h a (mem_univ a)
          have : (s a^2-B-C/B*s a)^2=0 := by nlinarith only [hh, hp a,sq_nonneg (s a^2-B-C/B*s a)]
          exact sq_eq_zero_iff.mp this
        have hf (a b : ι) : (s a-s b)*(s a+s b-C/B)=0 := by linear_combination hz a - hz b
        have h1 := (mul_eq_zero.mp (hf i j)).resolve_left (sub_ne_zero.mpr hij)
        have h2 := (mul_eq_zero.mp (hf i k)).resolve_left (sub_ne_zero.mpr hik)
        exact hjk (by linarith only [h1,h2])
    obtain ⟨lo,_,hlo⟩ := exists_min_image univ s ⟨i,mem_univ _⟩
    obtain ⟨hi,_,hhi⟩ := exists_max_image univ s ⟨i,mem_univ _⟩
    have hmin a := hlo a (mem_univ a)
    have hmax a := hhi a (mem_univ a)
    have hmid : ∃ a, s lo<s a ∧ s a<s hi := by
      by_contra! h
      have he (a : ι) : s a=s lo ∨ s a=s hi := by
        rcases eq_or_lt_of_le (hmin a) with hh|hh
        · exact Or.inl hh.symm
        · exact Or.inr (le_antisymm (hmax a) (h a hh))
      rcases he i with hi'|hi' <;> rcases he j with hj'|hj' <;>
        rcases he k with hk'|hk' <;> first | exact hij (hi'.trans hj'.symm) | exact hik (hi'.trans hk'.symm) | exact hjk (hj'.trans hk'.symm)
    obtain ⟨a,ha1,ha2⟩ := hmid
    have hlo0 : s lo<0 := by
      have hsum : 0<∑ b,p b*(s b-s lo) := sum_pos'
        (fun b _ => mul_nonneg (hp b).le (sub_nonneg.mpr (hmin b)))
        ⟨a,mem_univ _,mul_pos (hp a) (sub_pos.mpr ha1)⟩
      simp only [mul_sub,sum_sub_distrib,←sum_mul,hs,hp1,one_mul] at hsum
      linarith only [hsum]
    have hhi0 : 0<s hi := by
      have hsum : 0<∑ b,p b*(s hi-s b) := sum_pos'
        (fun b _ => mul_nonneg (hp b).le (sub_nonneg.mpr (hmax b)))
        ⟨a,mem_univ _,mul_pos (hp a) (sub_pos.mpr ha2)⟩
      simp only [mul_sub,sum_sub_distrib,←sum_mul,hs,hp1,one_mul] at hsum
      linarith only [hsum]
    have hgap : B < -s lo*s hi := by
      have hsum : 0<∑ b,p b*(s b-s lo)*(s hi-s b) := sum_pos'
        (fun b _ => mul_nonneg (mul_nonneg (hp b).le (sub_nonneg.mpr (hmin b)))
          (sub_nonneg.mpr (hmax b)))
        ⟨a,mem_univ _,mul_pos (mul_pos (hp a) (sub_pos.mpr ha1)) (sub_pos.mpr ha2)⟩
      have hid (b : ι) : p b*(s b-s lo)*(s hi-s b) =
        (s hi+s lo)*(p b*s b)-p b*s b^2-(s lo*s hi)*p b := by ring
      simp_rw [hid] at hsum
      simp only [sum_sub_distrib,←mul_sum,hs,hp1,mul_zero,mul_one] at hsum
      change 0<0-B-s lo*s hi at hsum
      linarith only [hsum]
    exact ⟨hB,hV,lo,hi,hlo0,hhi0,hgap⟩

  have infimum_limit (S : ℝ → Set ℝ) (B K : ℝ) (U : ℝ → ℝ)
      (hlower : ∀ R,0<R → ∀ q∈S R,B≤q)
      (hupper : ∀ᶠ R in 𝓝[>] 0,U R∈S R)
      (hU : Tendsto (fun R => (U R-B)/R^2) (𝓝[>] 0) (𝓝 K))
      (hseq : ∀ (R Q : ℕ → ℝ), (∀ n,0<R n) → (∀ n,Q n∈S (R n)) →
        Tendsto R atTop (𝓝[>] 0) → Tendsto Q atTop (𝓝 B) →
        ∀ d<K,∀ᶠ n in atTop,d≤(Q n-B)/R n^2) :
      Tendsto (fun R => (guardedInfimum (S R)-B)/R^2) (𝓝[>] 0) (𝓝 K) := by
    clear * - S B K U hlower hupper hU hseq
    classical
    apply tendsto_iff_seq_tendsto.mpr
    intro r hr
    have hev : ∀ᶠ n in atTop,0<r n ∧ U (r n)∈S (r n) :=
      (hr.eventually self_mem_nhdsWithin).and (hr.eventually hupper)
    obtain ⟨n0,hn0⟩ := eventually_atTop.mp hev
    let R := fun n : ℕ => r (n+n0)
    have hR (n : ℕ) : 0<R n := (hn0 (n+n0) (by omega)).1
    have hUm (n : ℕ) : U (R n)∈S (R n) := (hn0 (n+n0) (by omega)).2
    have hRt : Tendsto R atTop (𝓝[>] 0) := hr.comp (tendsto_add_atTop_nat n0)
    have hR0 : Tendsto R atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin hRt
    have hne (n : ℕ) : (S (R n)).Nonempty := ⟨U (R n),hUm n⟩
    have hb (n : ℕ) : BddBelow (S (R n)) := ⟨B,fun q hq => hlower (R n) (hR n) q hq⟩
    let C := fun n => guardedInfimum (S (R n))
    have hC (n : ℕ) : C n=sInf (S (R n)) := by simp [C,guardedInfimum,hne n,hb n]
    have hCU (n : ℕ) : C n≤U (R n) := by rw [hC]; exact csInf_le (hb n) (hUm n)
    have hCB (n : ℕ) : B≤C n := by
      rw [hC]
      exact le_csInf (hne n) (fun q hq => hlower (R n) (hR n) q hq)
    have happrox (n : ℕ) : ∃ q∈S (R n),q<C n+R n^3 := by
      apply exists_lt_of_csInf_lt (hne n)
      rw [←hC]
      exact lt_add_of_pos_right _ (pow_pos (hR n) _)
    choose Q hQm hQa using happrox
    have hQlo (n : ℕ) : B≤Q n := hlower (R n) (hR n) (Q n) (hQm n)
    have hQhi (n : ℕ) : Q n≤U (R n)+R n^3 := (hQa n).le.trans (add_le_add (hCU n) le_rfl)
    have hUt : Tendsto (fun n => (U (R n)-B)/R n^2) atTop (𝓝 K) := hU.comp hRt
    have hU0 : Tendsto (fun n => U (R n)) atTop (𝓝 B) := by
      have ht := (hUt.mul (hR0.pow 2)).add_const B
      have heq : (fun n => (U (R n)-B)/R n^2*R n^2+B)=(fun n => U (R n)) := by
        funext n
        field_simp [(hR n).ne']
        <;> ring
      rw [heq] at ht
      simpa using ht
    have hQt : Tendsto Q atTop (𝓝 B) := tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (by simpa using hU0.add (hR0.pow 3)) hQlo hQhi
    have hClim : Tendsto (fun n => (C n-B)/R n^2) atTop (𝓝 K) := by
      apply tendsto_order.mpr
      constructor
      · intro d hd
        let d' := (d+K)/2
        have hdd : d<d' := by dsimp [d']; linarith
        have hdK : d'<K := by dsimp [d']; linarith
        filter_upwards [hseq R Q hR hQm hRt hQt d' hdK,
          hR0.eventually (gt_mem_nhds (sub_pos.mpr hdd))] with n hn hsmall
        have hsq : 0<R n^2 := sq_pos_of_pos (hR n)
        have hlow := (le_div_iff₀ hsq).mp hn
        have hdiff : d*R n^2 < Q n-B-R n^3 := by
          have hmul := mul_lt_mul_of_pos_right hsmall hsq
          nlinarith only [hmul,hlow]
        apply (lt_div_iff₀ hsq).mpr
        linarith only [hQa n, hdiff]
      · intro d hd
        filter_upwards [hUt.eventually (gt_mem_nhds hd)] with n hn
        exact lt_of_le_of_lt (div_le_div_of_nonneg_right (sub_le_sub_right (hCU n) B)
          (sq_nonneg _)) hn
    apply (tendsto_add_atTop_iff_nat n0).mp
    exact hClim

  have cost_set_bounds {m : ℕ} (p v : Fin m → ℝ)
      (hp : ∀ j, 0<p j) (hp1 : ∑ j,p j=1) (hv0 : ∑ j,v j=0) (hv : v≠0) :
      (∀ R, 0≤R → ∀ Q ∈ costs p v R, (∑ j,v j^2/p j) ≤ Q) ∧
      (∀ᶠ R in 𝓝[>] 0, (costs p v R).Nonempty ∧ BddBelow (costs p v R)) := by
    clear * - p v hp hp1 hv0 hv upper_result
    have hlower (R : ℝ) (hR : 0≤R) (Q : ℝ) (hQ : Q ∈ costs p v R) :
        (∑ j,v j^2/p j) ≤ Q := by
      obtain ⟨N,rho,I,hI,hconn,hRI,hN,hNs,hc,hrho,hread,hcost⟩ := hQ
      have h0 : 0∈I := hRI ⟨by linarith,hR⟩
      have hpos : ∀ᶠ u in 𝓝 0, (rho u).PosSemidef :=
        (show ∀ᶠ u in 𝓝 (0:ℝ), u ∈ I from hI.mem_nhds h0).mono fun u hu => (hrho u hu).1
      have hh := actual_fisher (n := Fin 2) (ι := Fin m) N rho p v hN hNs hp
        ((hc.differentiableOn (by norm_num) 0 h0).differentiableAt (hI.mem_nhds h0)) hpos
        ((show ∀ᶠ u in 𝓝 (0:ℝ), u ∈ I from hI.mem_nhds h0).mono fun u hu j => by
          simpa using congrArg Complex.re (hread u hu j).1)
      rw [hcost] at hh
      exact hh
    refine ⟨hlower,?_⟩
    have hv' : ∃ j,v j≠0 := by contrapose! hv; ext j; exact hv j
    obtain ⟨N,rho,I,Q,hlim,hprog⟩ := upper_result p v hp hp1 hv0 hv'
    filter_upwards [hprog, self_mem_nhdsWithin] with R hR hRp
    have hmem : Q R ∈ costs p v R := ⟨N R,rho R,I R,hR⟩
    exact ⟨⟨Q R,hmem⟩,⟨∑ j,v j^2/p j,fun q hq => hlower R (le_of_lt hRp) q hq⟩⟩

  have all_program_lower {m : ℕ} (p v : Fin m → ℝ)
      (hp : ∀ j, 0<p j) (hp1 : ∑ j,p j=1) (hv0 : ∑ j,v j=0) (hv : v≠0)
      (hthree : ∃ i j k, v i/p i≠v j/p j ∧ v i/p i≠v k/p k ∧ v j/p j≠v k/p k)
      (R Q : ℕ → ℝ) (hR : ∀ n,0<R n) (hmem : ∀ n,Q n ∈ costs p v (R n))
      (hQ : Tendsto Q atTop (𝓝 (∑ j,v j^2/p j))) :
      ∀ d : ℝ, d<((∑ j,p j*(v j/p j)^4)-(∑ j,v j^2/p j)^2-
        (∑ j,p j*(v j/p j)^3)^2/(∑ j,v j^2/p j))/4 →
        ∀ᶠ n in atTop, d≤(Q n-(∑ j,v j^2/p j))/R n^2 := by
    clear * - p v hp hp1 hv0 hv hthree R Q hR hmem hQ score_separation actual_rank_two_lower
    classical
    let B := ∑ j,v j^2/p j
    have hB : B=∑ j,p j*(v j/p j)^2 := by
      apply Finset.sum_congr rfl
      intro j _
      field_simp
    have hs : ∑ j,p j*(v j/p j)=0 := by
      simpa [mul_div_cancel₀ _ (hp _).ne'] using hv0
    obtain ⟨hBp,hVp,lo,hi,hlo,hhi,hgap⟩ := score_separation p (fun j => v j/p j) hp hp1 hs hthree
    rw [←hB] at hgap
    choose N rho I hprog using hmem
    have h0 (n : ℕ) : 0∈I n := (hprog n).2.2.1 ⟨by linarith [hR n],(hR n).le⟩
    have hpure (n : ℕ) (u : ℝ) (hu : u∈I n) :
        (rho n u).PosSemidef ∧ trace (rho n u)=1 ∧ rho n u*rho n u=rho n u :=
      ⟨((hprog n).2.2.2.2.2.2.1 u hu).1,
        ((hprog n).2.2.2.2.2.2.1 u hu).2.1,
        ((hprog n).2.2.2.2.2.2.1 u hu).2.2.1⟩
    have hread (n : ℕ) (u : ℝ) (hu : u∈I n) (j : Fin m) :
        (trace (N n j*rho n u)).re=p j+u*v j := by
      simpa using congrArg Complex.re (((hprog n).2.2.2.2.2.2.2.1 u hu j).1)
    have hrank : ∀ᶠ n in atTop,Module.finrank ℝ (effectReadout (N n)).range=2 := by
      filter_upwards [hQ.eventually (gt_mem_nhds hgap)] with n hn
      rcases actual_rank_alternative (N n) (rho n) p v (I n) (hprog n).1 (h0 n) hv hp
        (hprog n).2.2.2.1 (hprog n).2.2.2.2.2.1 (hpure n) (hread n) lo hi hlo hhi with hh | hl
      · exact hh
      · rw [(hprog n).2.2.2.2.2.2.2.2] at hl
        exact False.elim (not_le_of_gt hn hl)
    obtain ⟨n0,hn0⟩ := eventually_atTop.mp hrank
    have hcost : ∀ n,spectralQFI (rho n 0) (deriv (rho n) 0)
        (hpure n 0 (h0 n)).1=Q n := fun n => (hprog n).2.2.2.2.2.2.2.2 _
    have hQt : Tendsto (fun n => spectralQFI (rho (n+n0) 0)
        (deriv (rho (n+n0)) 0) (hpure (n+n0) 0 (h0 (n+n0))).1) atTop (𝓝 B) := by
      simp only [hcost]
      exact hQ.comp (tendsto_add_atTop_nat n0)
    have ht := actual_rank_two_lower p v B hp hp1 hv hv0 hB hthree
      (fun n => N (n+n0)) (fun n => rho (n+n0)) (fun n => I (n+n0)) (fun n => R (n+n0))
      (fun n => (hprog (n+n0)).1) (fun n => (hprog (n+n0)).2.1)
      (fun n => h0 (n+n0)) (fun n => hR (n+n0)) (fun n => (hprog (n+n0)).2.2.1)
      (fun n => (hprog (n+n0)).2.2.2.1) (fun n => (hprog (n+n0)).2.2.2.2.1)
      (fun n => (hprog (n+n0)).2.2.2.2.2.1) (fun n => hpure (n+n0))
      (fun n => hread (n+n0)) (fun n => hn0 (n+n0) (by omega)) hQt
    intro d hd
    have hh := ht d hd
    simp only [hcost] at hh
    obtain ⟨k,hk⟩ := eventually_atTop.mp hh
    apply eventually_atTop.mpr
    refine ⟨k+n0,fun n hn => ?_⟩
    have hn' : n-n0≥k := by omega
    simpa [Nat.sub_add_cancel (show n0≤n by omega)] using hk (n-n0) hn'
  intro m p v hp hp1 hv0 hv hthree
  dsimp only
  let B := ∑ j,v j^2/p j
  have hB : (∑ j,p j*(v j/p j)^2)=B := by
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have h3 : (∑ j,p j*(v j/p j)^3)=(∑ j,v j^3/(p j)^2) := by
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have h4 : (∑ j,p j*(v j/p j)^4)=(∑ j,v j^4/(p j)^3) := by
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have hs : ∑ j,p j*(v j/p j)=0 := by
    simpa [mul_div_cancel₀ _ (hp _).ne'] using hv0
  have hV := (score_separation p (fun j => v j/p j) hp hp1 hs hthree).2.1
  refine ⟨hV,?_,?_⟩
  · filter_upwards [(cost_set_bounds p v hp hp1 hv0 hv).2] with R hR
    refine ⟨hR.1,hR.2,?_⟩
    have heq : C2 p v R=sInf (costs p v R) := by
      simp [C2,guardedInfimum,hR.1,hR.2]
    rw [heq]
    exact isGLB_csInf hR.1 hR.2
  · rw [hB]
    have hv' : ∃ j,v j≠0 := by contrapose! hv; ext j; exact hv j
    obtain ⟨N,rho,I,Q,hlim,hprog⟩ := upper_result p v hp hp1 hv0 hv'
    refine infimum_limit (costs p v) B
      (((∑ j,p j*(v j/p j)^4)-B^2-(∑ j,p j*(v j/p j)^3)^2/B)/4) Q ?_ ?_ ?_ ?_
    · intro R hR q hq
      exact (cost_set_bounds p v hp hp1 hv0 hv).1 R hR.le q hq
    · filter_upwards [hprog] with R hR
      exact ⟨N R,rho R,I R,hR⟩
    · simpa only [h3,h4] using hlim
    · intro R Q hR hmem _hRt hQt
      exact all_program_lower p v hp hp1 hv0 hv hthree R Q hR hmem hQt

end D5.S3.Quantum.Information.ActualPureQubitCostInfimum
