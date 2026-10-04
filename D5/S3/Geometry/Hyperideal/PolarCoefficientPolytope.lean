/- GID: D5/S3/Geometry/Hyperideal/PolarCoefficientPolytope
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/PolarCoefficientPolytope
   mirror-E: none(waiver:marked-coefficient-geometry)
   anchors: []
   utility: none
   digest: Exact ordered vertices and all marked supporting intersections of a polar coefficient polytope. -/

import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology
namespace D5.S3.Geometry.Hyperideal.PolarCoefficientPolytope

abbrev Coeff := Fin 4 → ℝ
def row (G : Fin 4 → Fin 4 → ℝ) (a : Coeff) (i : Fin 4) := ∑ j, G i j * a j
def polytope (G : Fin 4 → Fin 4 → ℝ) : Set Coeff :=
  {a | a ∈ stdSimplex ℝ (Fin 4) ∧ ∀ i, row G a i ≤ 0}
def endpoint (G : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) : Coeff :=
  fun k => if k = i then -G i j / (1-G i j) else if k = j then 1/(1-G i j) else 0
def endpoints (G : Fin 4 → Fin 4 → ℝ) : Set Coeff :=
  {a | ∃ i j : Fin 4,i≠j ∧ a=endpoint G i j}

/-- Simultaneous actual supporting equations, retaining all labels. -/
def supportingFace (G : Fin 4 → Fin 4 → ℝ) (S T : Finset (Fin 4)) : Set Coeff :=
  {a | a∈polytope G ∧ (∀ h∈S,a h=0) ∧ (∀ k∈T,row G a k=0)}

set_option maxHeartbeats 1000000 in
/-- All ordered endpoints, their strict incidence, and arbitrary marked face intersections. -/
theorem marked_coefficient_classification (G : Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i, G i i = 1) (ho : ∀ i j, i ≠ j → G i j < -1)
    (hs : ∀ i j, G i j = G j i) :
    (polytope G).extremePoints ℝ = endpoints G ∧
    ((∀ i j, i≠j → endpoint G i j∈polytope G ∧
      (∀ k,row G (endpoint G i j) k=0 ↔ k=i) ∧
      (∀ k,k≠i → row G (endpoint G i j) k<0) ∧
      (∀ k,endpoint G i j k=0 ↔ k≠i ∧ k≠j)) ∧
      (∀ i j k l,i≠j → k≠l → endpoint G i j=endpoint G k l → i=k ∧ j=l)) ∧
    (∀ S T : Finset (Fin 4), supportingFace G S T=convexHull ℝ
      {a | ∃ i j,i≠j ∧ (∀ h∈S,h≠i ∧ h≠j) ∧ (∀ k∈T,k=i) ∧ a=endpoint G i j}) := by
  have row_add (G : Fin 4 → Fin 4 → ℝ) (a b : Coeff) (i : Fin 4) :
      row G (a+b) i = row G a i + row G b i := by
    simp [row, mul_add, Finset.sum_add_distrib]
  have row_smul (G : Fin 4 → Fin 4 → ℝ) (t : ℝ) (a : Coeff) (i : Fin 4) :
      row G (t • a) i = t * row G a i := by
    simp only [row, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have row_single (G : Fin 4 → Fin 4 → ℝ) (j i : Fin 4) :
      row G (Pi.single j 1) i = G i j := by
    simp [row, Pi.single_apply, mul_ite]
  have mass_smul (t : ℝ) (a : Coeff) : (∑ i, (t • a) i) = t * ∑ i, a i := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  have preliminary (G : Fin 4 → Fin 4 → ℝ)
      (hd : ∀ i, G i i = 1) (ho : ∀ i j, i ≠ j → G i j < -1)
      (hs : ∀ i j, G i j = G j i) :
      IsCompact (polytope G) ∧ Convex ℝ (polytope G) ∧
        (∀ a ∈ stdSimplex ℝ (Fin 4), ∀ i, 0 ≤ row G a i → (1/2:ℝ) < a i) ∧
        (∀ a ∈ polytope G, ∀ i j, row G a i = 0 → row G a j = 0 → i=j) ∧
        (∀ a ∈ polytope G, (∑ i, a i * row G a i) < 0) := by
    have hrow (a : Coeff) (i : Fin 4) :
        row G a i = a i + ∑ j ∈ Finset.univ.erase i, G i j * a j := by
      rw [row, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), hd]
      ring
    have hsum (a : Coeff) (ha : a ∈ stdSimplex ℝ (Fin 4)) (i : Fin 4) :
        ∑ j ∈ Finset.univ.erase i, a j = 1-a i := by
      have hh := Finset.sum_erase_add (Finset.univ (α := Fin 4)) a (Finset.mem_univ i)
      rw [ha.2] at hh
      linarith
    have heavy (a : Coeff) (ha : a ∈ stdSimplex ℝ (Fin 4)) (i : Fin 4)
        (hi : 0 ≤ row G a i) : (1/2:ℝ) < a i := by
      by_contra hh
      have hai : a i ≤ 1/2 := le_of_not_gt hh
      have hm : 0 < ∑ j ∈ Finset.univ.erase i, a j := by rw [hsum a ha i]; linarith
      obtain ⟨j,hj,haj⟩ := Finset.sum_pos_iff_of_nonneg
        (fun j hj => ha.1 j) |>.mp hm
      have hjne : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
      have hb : (∑ j ∈ Finset.univ.erase i, G i j * a j) <
          ∑ j ∈ Finset.univ.erase i, -a j := by
        apply Finset.sum_lt_sum
        · intro k hk
          have hkne : i ≠ k := Ne.symm (Finset.ne_of_mem_erase hk)
          have hx := mul_le_mul_of_nonneg_right (le_of_lt (ho i k hkne)) (ha.1 k)
          simpa using hx
        · refine ⟨j,hj,?_⟩
          have hx := mul_lt_mul_of_pos_right (ho i j hjne) haj
          simpa using hx
      rw [Finset.sum_neg_distrib, hsum a ha i] at hb
      rw [hrow] at hi
      linarith
    have unique (a : Coeff) (ha : a ∈ polytope G) (i j : Fin 4)
        (hi : row G a i = 0) (hj : row G a j = 0) : i=j := by
      by_contra hij
      have hai := heavy a ha.1 i hi.ge
      have haj := heavy a ha.1 j hj.ge
      have hpair : a i + a j ≤ 1 := by
        have hle := Finset.sum_le_sum_of_subset_of_nonneg
          (show ({i,j}:Finset (Fin 4)) ⊆ Finset.univ by simp) (fun k hk hk' => ha.1.1 k)
        simpa [Finset.sum_pair hij, ha.1.2] using hle
      linarith
    have hneg (a : Coeff) (ha : a ∈ polytope G) : (∑ i, a i * row G a i) < 0 := by
      have hn (i : Fin 4) : a i * row G a i ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (ha.1.1 i) (ha.2 i)
      have hle : (∑ i, a i * row G a i) ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
      refine lt_of_le_of_ne hle ?_
      intro heq
      have he (i : Fin 4) : a i * row G a i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hn i)).mp heq i (Finset.mem_univ i)
      have hex : ∃ i, 0 < a i := by
        have hh : 0 < ∑ i, a i := by rw [ha.1.2]; norm_num
        exact Finset.sum_pos_iff_of_nonneg (fun i _ => ha.1.1 i) |>.mp hh |>.imp
          (fun i h => h.2)
      obtain ⟨i,hai⟩ := hex
      have hi : row G a i = 0 := (mul_eq_zero.mp (he i)).resolve_left (ne_of_gt hai)
      have others : ∀ j, j ≠ i → a j = 0 := by
        intro j hji
        by_contra hj
        have haj : 0 < a j := lt_of_le_of_ne (ha.1.1 j) (Ne.symm hj)
        have hrj : row G a j = 0 := (mul_eq_zero.mp (he j)).resolve_left (ne_of_gt haj)
        exact hji (unique a ha j i hrj hi)
      have hai1 : a i = 1 := by
        have hh : ∑ j, a j = a i := Finset.sum_eq_single i (fun j _ hji => others j hji)
          (by simp)
        linarith [ha.1.2]
      have hi1 : row G a i = 1 := by
        rw [hrow, hai1]
        have hh : (∑ j ∈ Finset.univ.erase i, G i j*a j)=0 :=
          Finset.sum_eq_zero (fun j hj => by rw [others j (Finset.ne_of_mem_erase hj),mul_zero])
        rw [hh]; norm_num
      linarith
    have hc : IsClosed (polytope G) := by
      have heq : polytope G = stdSimplex ℝ (Fin 4) ∩ ⋂ i, {a | row G a i ≤ 0} := by
        ext a; simp [polytope]
      rw [heq]
      apply (isClosed_stdSimplex ℝ (Fin 4)).inter
      apply isClosed_iInter
      intro i
      apply isClosed_le _ continuous_const
      unfold row
      fun_prop
    have hconv : Convex ℝ (polytope G) := by
      intro a ha b hb r t hr ht hrt
      refine ⟨(convex_stdSimplex ℝ (Fin 4)) ha.1 hb.1 hr ht hrt,?_⟩
      intro i
      have hh : row G (r • a + t • b) i = r*row G a i+t*row G b i := by
        rw [row_add, row_smul, row_smul]
      rw [hh]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hr (ha.2 i))
        (mul_nonpos_of_nonneg_of_nonpos ht (hb.2 i))
    exact ⟨(isCompact_stdSimplex ℝ (Fin 4)).of_isClosed_subset hc (fun a ha => ha.1),
      hconv, heavy, unique, hneg⟩

  have deformation (G : Fin 4 → Fin 4 → ℝ) (a d : Coeff)
      (ha : a ∈ (polytope G).extremePoints ℝ)
      (hd : ∑ i, d i = 0)
      (hz : ∀ i, a i = 0 → d i = 0)
      (hr : ∀ i, row G a i = 0 → row G d i = 0) : d=0 := by
    have hrow (t : ℝ) (i : Fin 4) :
        row G (a+t • d) i = row G a i+t*row G d i := by
      rw [row_add, row_smul]
    have hcoord (i : Fin 4) : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ (a+t • d) i := by
      by_cases hi : a i = 0
      · have hh := hz i hi
        filter_upwards [] with t
        simp [hi,hh]
      · have hi' : 0 < a i := lt_of_le_of_ne (ha.1.1.1 i) (Ne.symm hi)
        have cont : ContinuousAt (fun t : ℝ => a i+t*d i) 0 := by fun_prop
        have ht := continuousAt_const.eventually_lt cont (show 0 < a i+0*d i by simpa using hi')
        filter_upwards [ht] with t ht
        exact ht.le
    have hineq (i : Fin 4) : ∀ᶠ t : ℝ in 𝓝 0, row G (a+t • d) i ≤ 0 := by
      by_cases hi : row G a i = 0
      · have hh := hr i hi
        filter_upwards [] with t
        rw [hrow,hi,hh];simp
      · have hi' : row G a i < 0 := lt_of_le_of_ne (ha.1.2 i) hi
        have cont : ContinuousAt (fun t : ℝ => row G a i+t*row G d i) 0 := by fun_prop
        have ht := cont.eventually_lt continuousAt_const (show row G a i+0*row G d i < 0 by simpa using hi')
        filter_upwards [ht] with t ht
        rw [hrow];exact ht.le
    have hc : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 ≤ (a+t • d) i :=
      (Filter.eventually_all).mpr hcoord
    have hi : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, row G (a+t • d) i ≤ 0 :=
      (Filter.eventually_all).mpr hineq
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, a+t • d ∈ polytope G := by
      filter_upwards [hc,hi] with t hc hi
      refine ⟨⟨hc,?_⟩,hi⟩
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      rw [mass_smul, ha.1.1.2, hd]
      ring
    obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hnear
    have hp : a+(ε/2) • d ∈ polytope G := hball (by
      simp [Real.dist_eq,abs_of_pos hε];linarith)
    have hm : a+(-ε/2) • d ∈ polytope G := hball (by
      simp [Real.dist_eq,abs_of_pos hε];linarith)
    have hseg : a ∈ openSegment ℝ (a+(ε/2) • d) (a+(-ε/2) • d) := by
      refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
      funext i
      simp;ring
    have heq := ha.2 hp hm hseg
    funext i
    have hpoint := congrFun heq i
    change a i+(ε/2)*d i=a i at hpoint
    have hh : ε/2≠0 := ne_of_gt (show 0<ε/2 by linarith)
    exact (mul_eq_zero.mp (show (ε/2)*d i=0 by linarith)).resolve_left hh

  /- Feasible two-sided perturbations exclude all additional extreme points. -/

  have extreme_characterization (G : Fin 4 → Fin 4 → ℝ)
      (hd : ∀ i, G i i = 1) (ho : ∀ i j, i ≠ j → G i j < -1)
      (hs : ∀ i j, G i j = G j i) :
      (polytope G).extremePoints ℝ = {a | ∃ i j : Fin 4, i≠j ∧ a=endpoint G i j} := by
    have hp := preliminary G hd ho hs
    have heavy := hp.2.2.1
    have unique := hp.2.2.2.1
    have hsum (a : Coeff) (ha : a ∈ polytope G) (i : Fin 4) :
        ∑ j ∈ Finset.univ.erase i, a j = 1-a i := by
      have hh := Finset.sum_erase_add (Finset.univ (α := Fin 4)) a (Finset.mem_univ i)
      rw [ha.1.2] at hh;linarith
    have coordinate_lt_one (a : Coeff) (ha : a ∈ polytope G) (i : Fin 4) : a i<1 := by
      refine lt_of_le_of_ne (mem_Icc_of_mem_stdSimplex ha.1 i).2 ?_
      intro h
      have ht := hsum a ha i
      have hz : ∀ j, j≠i → a j=0 := by
        intro j hji
        have hn := ha.1.1 j
        have hzero : ∑ j ∈ Finset.univ.erase i, a j = 0 := by linarith
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => ha.1.1 k)).mp hzero j
          (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
      have hr : row G a i=1 := by
        simp only [row]
        rw [Finset.sum_eq_single i]
        · rw [hd,h];ring
        · intro j hj hji;rw [hz j hji,mul_zero]
        · simp
      linarith [ha.2 i]
    have other_positive (a : Coeff) (ha : a ∈ polytope G) (i : Fin 4) :
        ∃ j, j≠i ∧ 0<a j := by
      have hpositive : 0 < ∑ j ∈ Finset.univ.erase i, a j := by
        rw [hsum a ha i];linarith [coordinate_lt_one a ha i]
      obtain ⟨j,hj,haj⟩ :=
        (Finset.sum_pos_iff_of_nonneg (fun j hj => ha.1.1 j)).mp hpositive
      exact ⟨j,Finset.ne_of_mem_erase hj,haj⟩
    have ep_spec (i j : Fin 4) (hij : i≠j) :
        endpoint G i j ∈ polytope G ∧ row G (endpoint G i j) i=0 ∧
        (∀ k,k≠i → k≠j → endpoint G i j k=0) := by
      have hg := ho i j hij
      have hden : 0<1-G i j := by linarith
      have hrepr : endpoint G i j =
          (-G i j/(1-G i j)) • Pi.single i 1+(1/(1-G i j)) • Pi.single j 1 := by
        funext k
        by_cases hki : k=i
        · subst k;simp [endpoint,Pi.single_apply,hij]
        · by_cases hkj : k=j
          · subst k;simp [endpoint,Pi.single_apply,Ne.symm hij]
          · simp [endpoint,Pi.single_apply,hki,hkj]
      have hepr (k : Fin 4) : row G (endpoint G i j) k =
          (-G i j*G k i+G k j)/(1-G i j) := by
        rw [hrepr]
        rw [row_add, row_smul, row_smul, row_single, row_single]
        ring
      have him : endpoint G i j ∈ stdSimplex ℝ (Fin 4) := by
        constructor
        · intro k
          simp only [endpoint]
          split_ifs
          · exact div_nonneg (by linarith) hden.le
          · exact div_nonneg (by norm_num) hden.le
          · exact le_refl 0
        · rw [hrepr]
          simp only [Pi.add_apply, Finset.sum_add_distrib]
          rw [mass_smul, mass_smul]
          simp
          field_simp;ring
      have hr (k : Fin 4) : row G (endpoint G i j) k ≤ 0 := by
        rw [hepr]
        apply div_nonpos_of_nonpos_of_nonneg _ hden.le
        by_cases hki : k=i
        · subst k;rw [hd];ring_nf;exact le_refl 0
        · by_cases hkj : k=j
          · subst k;rw [hd,hs j i];nlinarith
          · have hgi := ho k i hki
            have hgj := ho k j hkj
            have ht : (-G i j)*G k i<0 :=
              mul_neg_of_pos_of_neg (by linarith) (by linarith)
            linarith
      refine ⟨⟨him,hr⟩,?_,?_⟩
      · rw [hepr,hd];ring
      · intro k hki hkj;simp [endpoint,hki,hkj]
    ext a
    constructor
    · intro ha
      have exists_active : ∃ i, row G a i=0 := by
        by_contra h
        have hn : ∀ i, row G a i≠0 := by simpa using h
        have hex : ∃ i, 0<a i := by
          have hh : 0<∑ i,a i := by rw [ha.1.1.2];norm_num
          obtain ⟨i,hi,hp⟩ :=
            (Finset.sum_pos_iff_of_nonneg (fun i hi => ha.1.1.1 i)).mp hh
          exact ⟨i,hp⟩
        obtain ⟨i,hai⟩ := hex
        obtain ⟨j,hji,haj⟩ := other_positive a ha.1 i
        let d : Coeff := Pi.single i 1-Pi.single j 1
        have hdsum : ∑ k,d k=0 := by simp [d,Finset.sum_sub_distrib]
        have hdz : ∀ k,a k=0 → d k=0 := by
          intro k hk
          have hki : k≠i := by intro hki;subst k;linarith
          have hkj : k≠j := by intro hkj;subst k;linarith
          simp [d,Pi.single_apply,hki,hkj]
        have hdr : ∀ k,row G a k=0 → row G d k=0 := by
          intro k hk;exact False.elim (hn k hk)
        have hz := deformation G a d ha hdsum hdz hdr
        have hh := congrFun hz i
        simp [d,Pi.single_apply,Ne.symm hji] at hh
      obtain ⟨i,hi⟩ := exists_active
      have hai : 0<a i := by linarith [heavy a ha.1.1 i hi.ge]
      obtain ⟨j,hji,haj⟩ := other_positive a ha.1 i
      have remaining_zero (k : Fin 4) (hki : k≠i) (hkj : k≠j) : a k=0 := by
        by_contra hk
        have hak : 0<a k := lt_of_le_of_ne (ha.1.1.1 k) (Ne.symm hk)
        let d : Coeff := (G i j-G i k) • Pi.single i 1+
          (G i k-1) • Pi.single j 1+(1-G i j) • Pi.single k 1
        have hdsum : ∑ l,d l=0 := by
          change (∑ l, (((G i j-G i k) • Pi.single i 1 +
            (G i k-1) • Pi.single j 1 + (1-G i j) • Pi.single k 1 : Coeff) l))=0
          simp only [Pi.add_apply, Finset.sum_add_distrib]
          rw [mass_smul, mass_smul, mass_smul]
          simp
        have hdz : ∀ l,a l=0 → d l=0 := by
          intro l hl
          have hli : l≠i := by intro hli;subst l;linarith
          have hlj : l≠j := by intro hlj;subst l;linarith
          have hlk : l≠k := by intro hlk;subst l;linarith
          simp [d,Pi.single_apply,hli,hlj,hlk]
        have hrowi : row G d i=0 := by
          change row G ((G i j-G i k) • Pi.single i 1 +
            (G i k-1) • Pi.single j 1 + (1-G i j) • Pi.single k 1) i=0
          rw [row_add, row_add, row_smul, row_smul, row_smul, row_single, row_single, row_single, hd]
          ring
        have hdr : ∀ l,row G a l=0 → row G d l=0 := by
          intro l hl
          have hli := unique a ha.1 l i hl hi
          subst l;exact hrowi
        have hz := deformation G a d ha hdsum hdz hdr
        have hh := congrFun hz k
        have hkj' := Ne.symm hkj
        simp [d,Pi.single_apply,hki,hkj,hkj'] at hh
        linarith [ho i j (Ne.symm hji)]
      have hmass : a i+a j=1 := by
        have hsum : ∑ k,a k=a i+a j := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
          have hh : (∑ k ∈ Finset.univ.erase i,a k)=a j := by
            apply Finset.sum_eq_single j
            · intro k hk hkj;exact remaining_zero k (Finset.ne_of_mem_erase hk) hkj
            · simp [hji]
          rw [hh];ring
        linarith [ha.1.1.2]
      have hrow : a i+G i j*a j=0 := by
        have he : row G a i=a i+G i j*a j := by
          unfold row
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
          have hh : (∑ k ∈ Finset.univ.erase i,G i k*a k)=G i j*a j := by
            apply Finset.sum_eq_single j
            · intro k hk hkj;rw [remaining_zero k (Finset.ne_of_mem_erase hk) hkj,mul_zero]
            · simp [hji]
          rw [hh,hd];ring
        linarith
      have hden : 1-G i j≠0 := by linarith [ho i j (Ne.symm hji)]
      have haj' : a j=1/(1-G i j) := by
        apply (eq_div_iff hden).mpr;nlinarith [hmass,hrow]
      have hai' : a i= -G i j/(1-G i j) := by
        apply (eq_div_iff hden).mpr
        have hmassg := congrArg (fun t : ℝ => G i j*t) hmass
        nlinarith [hmassg,hrow]
      refine ⟨i,j,Ne.symm hji,?_⟩
      funext k
      by_cases hki : k=i
      · subst k;simp [endpoint,hai']
      · by_cases hkj : k=j
        · subst k;simp [endpoint,hji,haj']
        · simp [endpoint,hki,hkj,remaining_zero k hki hkj]
    · rintro ⟨i,j,hij,rfl⟩
      have hspecific := ep_spec i j hij
      refine ⟨hspecific.1,?_⟩
      intro b hb c hc hseg
      obtain ⟨r,t,hr,ht,hrt,hpt⟩ := hseg
      have hzero (k : Fin 4) (hki : k≠i) (hkj : k≠j) : b k=0 := by
        have he := congrFun hpt k
        have hz := hspecific.2.2 k hki hkj
        change r*b k+t*c k=endpoint G i j k at he
        rw [hz] at he
        have hbr : 0≤r*b k := mul_nonneg hr.le (hb.1.1 k)
        have hct : 0≤t*c k := mul_nonneg ht.le (hc.1.1 k)
        have hbr0 : r*b k=0 := by linarith
        exact (mul_eq_zero.mp hbr0).resolve_left (ne_of_gt hr)
      have hactive : row G b i=0 := by
        have he : r*row G b i+t*row G c i=row G (endpoint G i j) i := by
          rw [← hpt]
          rw [row_add, row_smul, row_smul]
        rw [hspecific.2.1] at he
        have hbr : r*row G b i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le (hb.2 i)
        have hct : t*row G c i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (hc.2 i)
        have hbr0 : r*row G b i=0 := by linarith
        exact (mul_eq_zero.mp hbr0).resolve_left (ne_of_gt hr)
      have hmass : b i+b j=1 := by
        have hsum : ∑ k,b k=b i+b j := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
          have hh : (∑ k ∈ Finset.univ.erase i,b k)=b j := by
            apply Finset.sum_eq_single j
            · intro k hk hkj;exact hzero k (Finset.ne_of_mem_erase hk) hkj
            · simp [Ne.symm hij]
          rw [hh];ring
        linarith [hb.1.2]
      have he : b i+G i j*b j=0 := by
        have hh : row G b i=b i+G i j*b j := by
          unfold row
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
          have hz : (∑ k ∈ Finset.univ.erase i,G i k*b k)=G i j*b j := by
            apply Finset.sum_eq_single j
            · intro k hk hkj;rw [hzero k (Finset.ne_of_mem_erase hk) hkj,mul_zero]
            · simp [Ne.symm hij]
          rw [hz,hd];ring
        linarith
      have hden : 1-G i j≠0 := by linarith [ho i j hij]
      have hbj : b j=1/(1-G i j) := by
        apply (eq_div_iff hden).mpr;nlinarith [hmass,he]
      have hbi : b i= -G i j/(1-G i j) := by
        apply (eq_div_iff hden).mpr
        have hmassg := congrArg (fun t : ℝ => G i j*t) hmass
        nlinarith [hmassg,he]
      funext k
      by_cases hki : k=i
      · subst k;simp [endpoint,hbi]
      · by_cases hkj : k=j
        · subst k;simp [endpoint,Ne.symm hij,hbj]
        · simp [endpoint,hki,hkj,hzero k hki hkj]

  have supporting_incidence (G : Fin 4 → Fin 4 → ℝ)
      (hd : ∀ i,G i i=1) (ho : ∀ i j,i≠j → G i j < -1)
      (hs : ∀ i j,G i j=G j i) :
      (∀ i j, i≠j → endpoint G i j∈polytope G ∧
        (∀ k,row G (endpoint G i j) k=0 ↔ k=i) ∧
        (∀ k,k≠i → row G (endpoint G i j) k<0) ∧
        (∀ k,endpoint G i j k=0 ↔ k≠i ∧ k≠j)) ∧
      (∀ i j k l,i≠j → k≠l → endpoint G i j=endpoint G k l → i=k ∧ j=l) := by
    have hp := preliminary G hd ho hs
    have hE := extreme_characterization G hd ho hs
    have ep_in (i j : Fin 4) (hij : i≠j) : endpoint G i j∈polytope G := by
      apply (extremePoints_subset (𝕜 := ℝ))
      rw [hE]
      exact ⟨i,j,hij,rfl⟩
    have ep_row (i j : Fin 4) (hij : i≠j) (k : Fin 4) :
        row G (endpoint G i j) k=(-G i j*G k i+G k j)/(1-G i j) := by
      have heq : endpoint G i j=(-G i j/(1-G i j)) • Pi.single i 1+
          (1/(1-G i j)) • Pi.single j 1 := by
        funext l
        by_cases hli : l=i
        · subst l;simp [endpoint,hij]
        · by_cases hlj : l=j
          · subst l;simp [endpoint,Ne.symm hij]
          · simp [endpoint,hli,hlj]
      rw [heq,row_add,row_smul,row_smul,row_single,row_single]
      ring
    have active (i j : Fin 4) (hij : i≠j) : row G (endpoint G i j) i=0 := by
      rw [ep_row i j hij i,hd];ring
    have active_iff (i j : Fin 4) (hij : i≠j) (k : Fin 4) :
        row G (endpoint G i j) k=0 ↔ k=i := by
      constructor
      · intro hk;exact hp.2.2.2.1 _ (ep_in i j hij) k i hk (active i j hij)
      · intro hki;rw [hki];exact active i j hij
    have support (i j : Fin 4) (hij : i≠j) (k : Fin 4) :
        endpoint G i j k=0 ↔ k≠i ∧ k≠j := by
      have hden : 0<1-G i j := by linarith [ho i j hij]
      have hi : 0<endpoint G i j i := by
        simp only [endpoint,ite_true]
        exact div_pos (by linarith [ho i j hij]) hden
      have hj : 0<endpoint G i j j := by
        simp only [endpoint,if_neg (Ne.symm hij),ite_true]
        exact div_pos (by norm_num) hden
      constructor
      · intro hk
        constructor
        · intro hki;subst k;linarith
        · intro hkj;subst k;linarith
      · rintro ⟨hki,hkj⟩;simp [endpoint,hki,hkj]
    constructor
    · intro i j hij
      refine ⟨ep_in i j hij,active_iff i j hij,?_,support i j hij⟩
      intro k hki
      exact lt_of_le_of_ne ((ep_in i j hij).2 k)
        (fun hk => hki ((active_iff i j hij k).mp hk))
    · intro i j k l hij hkl heq
      have hik : i=k := by
        apply (active_iff k l hkl i).mp
        rw [←heq];exact active i j hij
      subst k
      refine ⟨rfl,?_⟩
      by_contra hjl
      have hz : endpoint G i l j=0 := (support i l hkl j).mpr ⟨Ne.symm hij,hjl⟩
      rw [←heq] at hz
      have bad := (support i j hij j).mp hz
      exact bad.2 rfl

  have supporting_intersection_hulls (G : Fin 4 → Fin 4 → ℝ)
      (hd : ∀ i,G i i=1) (ho : ∀ i j,i≠j → G i j < -1)
      (hs : ∀ i j,G i j=G j i) (S T : Finset (Fin 4)) :
      supportingFace G S T=convexHull ℝ
        {a | ∃ i j,i≠j ∧ (∀ h∈S,h≠i ∧ h≠j) ∧ (∀ k∈T,k=i) ∧ a=endpoint G i j} := by
    have hp := preliminary G hd ho hs
    have hi := supporting_incidence G hd ho hs
    have hE := extreme_characterization G hd ho hs
    have hext : IsExtreme ℝ (polytope G) (supportingFace G S T) := by
      refine ⟨fun a ha => ha.1,?_⟩
      intro a ha b hb c hc hseg
      obtain ⟨r,t,hr,ht,hrt,hcomb⟩ := hseg
      refine ⟨ha,?_,?_⟩
      · intro h hh
        have hsum : r*a h+t*b h=0 := by
          have hcoord := congrFun hcomb h
          change r*a h+t*b h=c h at hcoord
          rw [hc.2.1 h hh] at hcoord
          exact hcoord
        have har : 0≤r*a h := mul_nonneg hr.le (ha.1.1 h)
        have hbt : 0≤t*b h := mul_nonneg ht.le (hb.1.1 h)
        exact (mul_eq_zero.mp (show r*a h=0 by linarith)).resolve_left (ne_of_gt hr)
      · intro k hk
        have hsum : r*row G a k+t*row G b k=0 := by
          have hrow := congrArg (fun x => row G x k) hcomb
          rw [row_add,row_smul,row_smul,hc.2.2 k hk] at hrow
          exact hrow
        have har : r*row G a k≤0 := mul_nonpos_of_nonneg_of_nonpos hr.le (ha.2 k)
        have hbt : t*row G b k≤0 := mul_nonpos_of_nonneg_of_nonpos ht.le (hb.2 k)
        exact (mul_eq_zero.mp (show r*row G a k=0 by linarith)).resolve_left (ne_of_gt hr)
    have hclosed : IsClosed (supportingFace G S T) := by
      have heq : supportingFace G S T=polytope G ∩
          ((⋂ h∈S,{a : Coeff | a h=0}) ∩ (⋂ k∈T,{a : Coeff | row G a k=0})) := by
        ext a;simp [supportingFace,and_assoc,and_left_comm,and_comm]
      rw [heq]
      refine hp.1.isClosed.inter (IsClosed.inter ?_ ?_)
      · apply isClosed_iInter;intro h
        apply isClosed_iInter;intro hh
        exact isClosed_eq (continuous_apply h) continuous_const
      · apply isClosed_iInter;intro k
        apply isClosed_iInter;intro hk
        apply isClosed_eq _ continuous_const
        unfold row;fun_prop
    have hconv : Convex ℝ (supportingFace G S T) := by
      intro a ha b hb r t hr ht hrt
      refine ⟨hp.2.1 ha.1 hb.1 hr ht hrt,?_,?_⟩
      · intro h hh
        change r*a h+t*b h=0
        rw [ha.2.1 h hh,hb.2.1 h hh];ring
      · intro k hk
        rw [row_add,row_smul,row_smul,ha.2.2 k hk,hb.2.2 k hk];ring
    have hvert : (supportingFace G S T).extremePoints ℝ=
        {a | ∃ i j,i≠j ∧ (∀ h∈S,h≠i ∧ h≠j) ∧ (∀ k∈T,k=i) ∧ a=endpoint G i j} := by
      rw [hext.extremePoints_eq,hE]
      ext a
      constructor
      · rintro ⟨ha,i,j,hij,rfl⟩
        refine ⟨i,j,hij,?_,?_,rfl⟩
        · intro h hh;exact (hi.1 i j hij).2.2.2 h |>.mp (ha.2.1 h hh)
        · intro k hk;exact (hi.1 i j hij).2.1 k |>.mp (ha.2.2 k hk)
      · rintro ⟨i,j,hij,hS,hT,rfl⟩
        refine ⟨⟨(hi.1 i j hij).1,?_,?_⟩,i,j,hij,rfl⟩
        · intro h hh;exact (hi.1 i j hij).2.2.2 h |>.mpr (hS h hh)
        · intro k hk;exact (hi.1 i j hij).2.1 k |>.mpr (hT k hk)
    have hcompact := hp.1.of_isClosed_subset hclosed (fun a ha => ha.1)
    have hkm := closure_convexHull_extremePoints hcompact hconv
    rw [hvert] at hkm
    have hf : {a : Coeff | ∃ i j,i≠j ∧ (∀ h∈S,h≠i ∧ h≠j) ∧
        (∀ k∈T,k=i) ∧ a=endpoint G i j}.Finite := by
      apply (Set.finite_range (fun p : Fin 4 × Fin 4 => endpoint G p.1 p.2)).subset
      rintro a ⟨i,j,hij,hS,hT,rfl⟩;exact ⟨(i,j),rfl⟩
    rw [(hf.isClosed_convexHull ℝ).closure_eq] at hkm
    exact hkm.symm

  exact ⟨extreme_characterization G hd ho hs,
    supporting_incidence G hd ho hs, supporting_intersection_hulls G hd ho hs⟩

end D5.S3.Geometry.Hyperideal.PolarCoefficientPolytope
