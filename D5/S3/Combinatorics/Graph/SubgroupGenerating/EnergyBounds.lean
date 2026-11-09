/- GID: D5/S3/Combinatorics/Graph/SubgroupGenerating/EnergyBounds
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubgroupGenerating/EnergyBounds
   mirror-E: none(waiver:noncomputable-spectral-energies)
   anchors: []
   utility: none
   digest: Global energies and the full finite-nonabelian subgroup-generating bounds. -/

import D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra

/-! All ten spectral and globally centered energy conclusions for finite nonabelian groups. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix Finset
open scoped Classical
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open D5.S3.Combinatorics.Graph.SubgroupGenerating.GeneratingFibers
open D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra
open D5.S3.Combinatorics.Graph.SubgroupGenerating.FiberSpectra

namespace D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds
noncomputable section
variable {G : Type} [Group G] [Fintype G]
attribute [local instance] CyclicExtensionRefutation.subgroupFintype

private theorem sum_map_sum {ι : Type*} (s : Finset ι) (m : ι → Multiset ℝ) (f : ℝ → ℝ) :
    ((∑ i ∈ s, m i).map f).sum = ∑ i ∈ s, ((m i).map f).sum := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert, hi, Multiset.map_add, ih]

private theorem star_adjacency_energy (r : ℕ) :
    ((starValues r .adjacency).map (fun x => |x|)).sum = 2 * Real.sqrt r := by
  by_cases hr : r = 0
  · simp [starValues, hr]
  · simp [starValues, hr, abs_of_nonneg (Real.sqrt_nonneg r)]
    ring

private theorem star_cn_energy (r : ℕ) :
    ((starValues r .commonNeighbour).map (fun x => |x|)).sum =
      2 * ((r : ℝ) - if r = 0 then 0 else 1) := by
  by_cases hr : r = 0
  · simp [starValues, hr]
  · have h1 : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
    have hc : ((r-1 : ℕ) : ℝ) = (r : ℝ)-1 := by rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hr)]; norm_num
    simp [starValues, hr, abs_of_nonneg (by linarith : 0 ≤ (r : ℝ)-1), hc]
    ring

private theorem star_centered_energy (r : ℕ) (d : ℝ) (hd : 0 ≤ d) (hd2 : d < 2) :
    ((starValues r .laplacian).map (fun x => |x-d|)).sum =
      d + ((r : ℝ) - if r = 0 then 0 else 1) * |1-d| +
        (r : ℝ) + (if r = 0 then 0 else 1) - (if r = 0 then 0 else 1)*d := by
  by_cases hr : r = 0
  · simp [starValues, hr, abs_of_nonneg hd]
  · have h1 : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
    have hc : ((r-1 : ℕ) : ℝ) = (r : ℝ)-1 := by rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hr)]; norm_num
    simp [starValues, hr, abs_of_nonneg hd,
      abs_of_nonneg (by linarith : 0 ≤ (r : ℝ)+1-d), hc]
    ring

private theorem indicator_sum :
    (∑ H : Subgroup G, (if pairCount H = 0 then (0 : ℝ) else 1)) =
      (positiveFibers (G := G)).card := by
  simpa only [positiveFibers, Nat.pos_iff_ne_zero, ite_not] using
    (Finset.sum_boole (R := ℝ) (fun H : Subgroup G => pairCount H ≠ 0) Finset.univ)

private theorem pair_sum :
    (∑ H : Subgroup G, (pairCount H : ℝ)) = (Fintype.card G : ℝ)^2 := by
  exact_mod_cast (sum_pairCount (G := G))

private theorem average_degree : averageDegree (sgbGraph G) =
    2 * (Fintype.card G : ℝ)^2 /
      ((Fintype.card G : ℝ)^2 + Fintype.card (Subgroup G)) := by
  simp [averageDegree, edge_count, Fintype.card_sum, Fintype.card_prod, pow_two]

private theorem average_range : 0 ≤ averageDegree (sgbGraph G) ∧
    averageDegree (sgbGraph G) < 2 := by
  rw [average_degree]
  have hM : 0 < (Fintype.card G : ℝ)^2 := by positivity
  have hk : 0 < (Fintype.card (Subgroup G) : ℝ) := by positivity
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity)).mpr
    linarith

/-- All four literal energies use the complete carrier and one whole-graph center. -/
theorem sgb_energy :
    graphEnergy (sgbGraph G) .adjacency = 2 * ∑ H : Subgroup G, Real.sqrt (pairCount H) ∧
    graphEnergy (sgbGraph G) .commonNeighbour =
      2 * ((Fintype.card G : ℝ)^2 - (positiveFibers (G := G)).card) ∧
    graphEnergy (sgbGraph G) .laplacian =
      Fintype.card (Subgroup G) * averageDegree (sgbGraph G) +
      ((Fintype.card G : ℝ)^2 - (positiveFibers (G := G)).card) * |1-averageDegree (sgbGraph G)| +
      (Fintype.card G : ℝ)^2 + (positiveFibers (G := G)).card -
      (positiveFibers (G := G)).card * averageDegree (sgbGraph G) ∧
    graphEnergy (sgbGraph G) .signless = graphEnergy (sgbGraph G) .laplacian := by
  have hd := average_range (G := G)
  constructor
  · simp only [graphEnergy, sgb_spectrum, sub_zero, sum_map_sum, star_adjacency_energy,
      ← Finset.mul_sum]
  constructor
  · simp only [graphEnergy, sgb_spectrum, sub_zero, sum_map_sum, star_cn_energy,
      ← Finset.mul_sum, Finset.sum_sub_distrib, pair_sum, indicator_sum]
  constructor
  · simp only [graphEnergy, sgb_spectrum, sum_map_sum,
      star_centered_energy _ _ hd.1 hd.2, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pair_sum, indicator_sum]
  · simp only [graphEnergy, sgb_spectrum, starValues]

private theorem sqrt_prime_interval (p : ℕ) (hp : p.Prime) :
    (p : ℝ)-1 < Real.sqrt (p^2-1 : ℕ) ∧ Real.sqrt (p^2-1 : ℕ) < p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hc : ((p^2-1 : ℕ) : ℝ) = (p : ℝ)^2-1 := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ p^2)]; push_cast; rfl
  have hs : Real.sqrt (p^2-1 : ℕ)^2 = (p : ℝ)^2-1 :=
    (Real.sq_sqrt (Nat.cast_nonneg (p^2-1))).trans hc
  have hn := Real.sqrt_nonneg (p^2-1 : ℕ)
  constructor <;> nlinarith

/-- A Cauchy prime-order subgroup supplies an actual irrational adjacency eigenvalue. -/
theorem adjacency_not_integral (hG : 1 < Fintype.card G) :
    ¬ IntegralSpectrum (graphSpectrum (sgbGraph G) .adjacency) := by
  obtain ⟨p,H,hp,_,hr⟩ := exists_prime_fiber (G := G) hG
  have hpos : pairCount H ≠ 0 := by
    have hs : 4 ≤ p^2 := by nlinarith [hp.two_le]
    omega
  have hm : Real.sqrt (pairCount H) ∈ graphSpectrum (sgbGraph G) .adjacency := by
    rw [sgb_spectrum]
    apply Multiset.mem_sum.mpr
    exact ⟨H,Finset.mem_univ _,by simp [starValues,hpos]⟩
  intro hi
  obtain ⟨z,hz⟩ := hi _ hm
  have hs := sqrt_prime_interval p hp
  rw [← hr,hz] at hs
  have hlo : (p : ℤ)-1 < z := by exact_mod_cast hs.1
  have hhi : z < (p : ℤ) := by exact_mod_cast hs.2
  omega

private theorem star_integral (r : ℕ) (kind : MatrixKind)
    (hk : kind ≠ .adjacency) : IntegralSpectrum (starValues r kind) := by
  intro x hx
  by_cases hr : r = 0
  · simp [starValues,hr,Multiset.mem_replicate] at hx
    exact ⟨0, by simpa using hx⟩
  · cases kind with
    | adjacency => exact (hk rfl).elim
    | laplacian =>
      simp [starValues,hr,Multiset.mem_replicate] at hx
      rcases hx with rfl | rfl | ⟨_,rfl⟩
      · exact ⟨0,by norm_num⟩
      · exact ⟨(r : ℤ)+1,by push_cast; rfl⟩
      · exact ⟨1,by norm_num⟩
    | signless =>
      simp [starValues,hr,Multiset.mem_replicate] at hx
      rcases hx with rfl | rfl | ⟨_,rfl⟩
      · exact ⟨0,by norm_num⟩
      · exact ⟨(r : ℤ)+1,by push_cast; rfl⟩
      · exact ⟨1,by norm_num⟩
    | commonNeighbour =>
      simp [starValues,hr,Multiset.mem_replicate] at hx
      rcases hx with rfl | rfl | ⟨_,rfl⟩
      · exact ⟨0,by norm_num⟩
      · exact ⟨(r : ℤ)-1,by push_cast; rfl⟩
      · exact ⟨-1,by norm_num⟩

/-- The other three actual eigenvalue multisets consist entirely of integers. -/
theorem other_spectra_integral (kind : MatrixKind) (hk : kind ≠ .adjacency) :
    IntegralSpectrum (graphSpectrum (sgbGraph G) kind) := by
  rw [sgb_spectrum]
  intro x hx
  obtain ⟨H,_,hx⟩ := Multiset.mem_sum.mp hx
  exact star_integral _ kind hk x hx

private theorem adjacency_lt_order (hG : 1 < Fintype.card G) :
    graphEnergy (sgbGraph G) .adjacency < (Fintype.card (Vertex G) : ℝ) := by
  obtain ⟨p,H,hp,_,hr⟩ := exists_prime_fiber (G := G) hG
  have hb (K : Subgroup G) : 2 * Real.sqrt (pairCount K) ≤ (pairCount K : ℝ)+1 := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg (pairCount K))
    nlinarith [sq_nonneg (Real.sqrt (pairCount K)-1)]
  have hstrict : 2 * Real.sqrt (pairCount H) < (pairCount H : ℝ)+1 := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg (pairCount H))
    have h3 : 3 ≤ pairCount H := by
      have hs : 4 ≤ p^2 := by nlinarith [hp.two_le]
      omega
    have h3R : (3 : ℝ) ≤ pairCount H := by exact_mod_cast h3
    have hn := Real.sqrt_nonneg (pairCount H)
    have hne : Real.sqrt (pairCount H) ≠ 1 := by intro he; rw [he] at hs; norm_num at hs; linarith
    have hp' := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    nlinarith
  have hs := Finset.sum_lt_sum (fun K (_ : K ∈ (Finset.univ : Finset (Subgroup G))) => hb K)
    ⟨H,Finset.mem_univ _,hstrict⟩
  rw [(sgb_energy (G := G)).1]
  simpa only [Finset.mul_sum, Finset.sum_add_distrib, pair_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_sum, Fintype.card_prod, Nat.cast_add, Nat.cast_mul, pow_two] using hs

private theorem numeric_bounds (M k t d S : ℝ)
    (hM : 1 ≤ M) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hd : 0 ≤ d) (hd2 : d < 2) (hc : d*(M+k) = 2*M)
    (hS : 0 ≤ S) (hdef : S ≤ M-t) :
    let ell := k*d+(M-t)*|1-d|+M+t-t*d
    ell ≤ 2*(M+k-1) ∧ 2*S ≤ ell ∧
      2*(M-t) ≤ 2*(M+k-1)*(M+k-2) := by
  dsimp only
  have hN : 2 ≤ M+k := by linarith
  have hCN : 2*(M-t) ≤ 2*(M+k-2) := by linarith
  have hCN' : 2*(M+k-2) ≤ 2*(M+k-1)*(M+k-2) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ M+k-2) (by linarith : 0 ≤ M+k-2)]
  by_cases hd1 : d ≤ 1
  · rw [abs_of_nonneg (by linarith : 0 ≤ 1-d)]
    have he : k*d+(M-t)*(1-d)+M+t-t*d = 2*k*d := by nlinarith [hc]
    rw [he]
    have hMk : M ≤ k := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-d) (by linarith : 0 ≤ M+k)]
    have hu : 2*k*d ≤ M+k := by
      have hsq := sq_nonneg (M-k)
      have hmul : (2*k*d)*(M+k) = 4*M*k := by nlinarith [hc]
      nlinarith
    have hl : 2*M ≤ 2*k*d := by nlinarith [mul_nonneg hd (sub_nonneg.mpr hMk)]
    exact ⟨by linarith,by linarith,hCN.trans hCN'⟩
  · rw [abs_of_nonpos (by linarith : 1-d ≤ 0)]
    have he : k*d+(M-t)*(-(1-d))+M+t-t*d = 2*M-2*t*(d-1) := by nlinarith [hc]
    rw [he]
    have hp : 0 ≤ t*(d-1) := mul_nonneg (by linarith) (by linarith)
    have hpay : 0 ≤ t*(2-d) := mul_nonneg (by linarith) (by linarith)
    exact ⟨by nlinarith,by nlinarith,hCN.trans hCN'⟩

/-- All ten literal conclusions hold together for every finite nonabelian group. -/
theorem result (hn : ∃ a b : G, a*b ≠ b*a) :
    ¬ IntegralSpectrum (graphSpectrum (sgbGraph G) .adjacency) ∧
    IntegralSpectrum (graphSpectrum (sgbGraph G) .laplacian) ∧
    IntegralSpectrum (graphSpectrum (sgbGraph G) .signless) ∧
    IntegralSpectrum (graphSpectrum (sgbGraph G) .commonNeighbour) ∧
    graphEnergy (sgbGraph G) .adjacency < (Fintype.card (Vertex G) : ℝ) ∧
    graphEnergy (sgbGraph G) .adjacency ≤ 2*((Fintype.card (Vertex G) : ℝ)-1) ∧
    graphEnergy (sgbGraph G) .laplacian ≤ 2*((Fintype.card (Vertex G) : ℝ)-1) ∧
    graphEnergy (sgbGraph G) .signless ≤ 2*((Fintype.card (Vertex G) : ℝ)-1) ∧
    graphEnergy (sgbGraph G) .commonNeighbour ≤
      2*((Fintype.card (Vertex G) : ℝ)-1)*((Fintype.card (Vertex G) : ℝ)-2) ∧
    graphEnergy (sgbGraph G) .adjacency ≤ graphEnergy (sgbGraph G) .laplacian := by
  have hG : 1 < Fintype.card G := by
    by_contra h
    haveI : Subsingleton G := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    obtain ⟨a,b,hab⟩ := hn
    exact hab (Subsingleton.elim _ _)
  have hN : (Fintype.card (Vertex G) : ℝ) =
      (Fintype.card G : ℝ)^2+Fintype.card (Subgroup G) := by
    simp [Fintype.card_sum,Fintype.card_prod,pow_two]
  have hM : (1 : ℝ) ≤ (Fintype.card G : ℝ)^2 := by
    have : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast (by omega : 1 ≤ Fintype.card G)
    nlinarith
  have hk : (1 : ℝ) ≤ Fintype.card (Subgroup G) := by exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card (Subgroup G))
  have ht : (1 : ℝ) ≤ (positiveFibers (G := G)).card := by
    have ht' : 0 < (positiveFibers (G := G)).card := Finset.card_pos.mpr
      ⟨⊥,by simp [positiveFibers,pairCount_bot]⟩
    exact_mod_cast (by omega : 1 ≤ (positiveFibers (G := G)).card)
  have hc : averageDegree (sgbGraph G) *
      ((Fintype.card G : ℝ)^2+Fintype.card (Subgroup G)) = 2*(Fintype.card G : ℝ)^2 := by
    rw [average_degree]
    exact div_mul_cancel₀ _ (by positivity)
  have hs0 : 0 ≤ ∑ H : Subgroup G, Real.sqrt (pairCount H) :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hb := numeric_bounds _ _ _ _ _ hM hk ht (average_range (G := G)).1
    (average_range (G := G)).2 hc hs0 (sqrt_sum_le_deficit hn)
  have he := sgb_energy (G := G)
  have hstrict := adjacency_lt_order (G := G) hG
  refine ⟨adjacency_not_integral hG,other_spectra_integral _ (by intro he; cases he),
    other_spectra_integral _ (by intro he; cases he),other_spectra_integral _ (by intro he; cases he),
    hstrict,?_,?_,?_,?_,?_⟩
  · rw [hN] at hstrict ⊢
    linarith
  · rw [he.2.2.1,hN]
    exact hb.1
  · rw [he.2.2.2,he.2.2.1,hN]
    exact hb.1
  · rw [he.2.1,hN]
    exact hb.2.2
  · rw [he.1,he.2.2.1]
    exact hb.2.1

end
end D5.S3.Combinatorics.Graph.SubgroupGenerating.EnergyBounds
