/- GID: D5/S3/Combinatorics/Graph/LegalWords/BlockGrowth
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/BlockGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Subadditive]
   utility: none
   digest: Native legal-word loads are nearly additive with a finite growth constant. -/

import D5.S3.Combinatorics.Graph.QuadraticLoad.NativeTransport
import D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Topology
open Finset Set Filter
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Combinatorics.Graph.LegalWordDegree
open D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
open D5.S3.Combinatorics.Graph.QuadraticEdgeLoad
open D5.S3.Combinatorics.Graph.QuadraticLoad.NativeTransport
open D5.S3.Combinatorics.Graph.LegalWords.ConstrainedHarmonicOptimizer

namespace D5.S3.Combinatorics.Graph.LegalWords.BlockGrowth

private instance legal_nonempty (n : ℕ) : Nonempty (Legal n) :=
  ⟨⟨fun _ => false, (adm_iff_no_adjacent_true n _).mpr (by simp)⟩⟩

private def firstBlock (n m : ℕ) (w : Legal (n+m)) : Legal n :=
  ⟨fun i => w.val ⟨i.val, by omega⟩, by
    apply (adm_iff_no_adjacent_true n _).mpr
    intro i j hij
    exact (adm_iff_no_adjacent_true (n+m) _).mp w.property
      ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij⟩

private def lastBlock (n m : ℕ) (w : Legal (n+m)) : Legal m :=
  ⟨fun i => w.val ⟨n+i.val, by omega⟩, by
    apply (adm_iff_no_adjacent_true m _).mpr
    intro i j hij
    exact (adm_iff_no_adjacent_true (n+m) _).mp w.property
      ⟨n+i.val, by omega⟩ ⟨n+j.val, by omega⟩ (by simp only [Fin.val_mk]; omega)⟩

private def splitWord (n m : ℕ) (w : Legal (n+m)) : Legal n × Legal m :=
  (firstBlock n m w, lastBlock n m w)

private theorem split_injective (n m : ℕ) : Function.Injective (splitWord n m) := by
  intro a b h
  apply Subtype.ext
  funext i
  by_cases hi : i.val < n
  · have he := congrArg (fun p : Legal n × Legal m => p.1.val ⟨i.val,hi⟩) h
    simpa only [splitWord, firstBlock] using he
  · have he := congrArg (fun p : Legal n × Legal m => p.2.val ⟨i.val-n,by omega⟩) h
    simpa [splitWord, lastBlock, Nat.add_sub_of_le (by omega : n ≤ i.val)] using he

private theorem split_adj (n m : ℕ) (a b : Legal (n+m))
    (h : (legalWordGraph (n+m)).Adj a b) :
    ((legalWordGraph n) □ (legalWordGraph m)).Adj (splitWord n m a) (splitWord n m b) := by
  obtain ⟨i, hi, haw⟩ := (adj_iff (n+m) a b).mp h
  by_cases hin : i.val < n
  · apply Or.inl
    constructor
    · apply (adj_iff n _ _).mpr
      refine ⟨⟨i.val,hin⟩, hi, ?_⟩
      intro j hj
      exact haw ⟨j.val,by omega⟩ (by intro he; apply hj; exact Fin.ext (congrArg (fun k : Fin (n+m) => k.val) he))
    · apply Subtype.ext
      funext j
      exact haw ⟨n+j.val,by omega⟩ (by intro he; have hv : n+j.val = i.val := congrArg (fun k : Fin (n+m) => k.val) he; omega)
  · apply Or.inr
    constructor
    · apply (adj_iff m _ _).mpr
      refine ⟨⟨i.val-n,by omega⟩, ?_, ?_⟩
      · simpa [splitWord, lastBlock, Nat.add_sub_of_le (by omega : n ≤ i.val)] using hi
      · intro j hj
        exact haw ⟨n+j.val,by omega⟩ (by
          intro he; apply hj; apply Fin.ext; have := congrArg Fin.val he; simp only [Fin.val_mk] at *; omega)
    · apply Subtype.ext
      funext j
      exact haw ⟨j.val,by omega⟩ (by intro he; have hv : j.val = i.val := congrArg (fun k : Fin (n+m) => k.val) he; omega)

private def zeroWord (n m : ℕ) (b : Legal n) (c : Legal m) :
    Fin (n+m+1) → Bool := fun i =>
  if hi : i.val < n then b.val ⟨i.val,hi⟩
  else if he : i.val = n then false
  else c.val ⟨i.val-n-1,by omega⟩

private theorem zeroWord_legal (n m : ℕ) (b : Legal n) (c : Legal m) :
    Adm (n+m+1) (zeroWord n m b c) := by
  apply (adm_iff_no_adjacent_true _ _).mpr
  intro i j hij
  by_cases hi : i.val < n
  · by_cases hj : j.val < n
    · simpa [zeroWord, hi, hj] using
        (adm_iff_no_adjacent_true n _).mp b.property ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij
    · have he : j.val = n := by omega
      simp [zeroWord, hj, he]
  · by_cases hj : j.val < n
    · omega
    · by_cases hin : i.val = n
      · simp [zeroWord, hi, hin]
      · have hjn : j.val ≠ n := by omega
        simpa [zeroWord, hi, hj, hin, hjn] using
          (adm_iff_no_adjacent_true m _).mp c.property
            ⟨i.val-n-1,by omega⟩ ⟨j.val-n-1,by omega⟩ (by simp only [Fin.val_mk]; omega)

private def zeroJoin (n m : ℕ) (x : Legal n × Legal m) : Legal (n+m+1) :=
  ⟨zeroWord n m x.1 x.2, zeroWord_legal n m x.1 x.2⟩

private theorem zero_left (n m : ℕ) (x : Legal n × Legal m) (i : Fin n) :
    (zeroJoin n m x).val ⟨i.val,by omega⟩ = x.1.val i := by
  simp [zeroJoin, zeroWord, i.isLt]

private theorem zero_right (n m : ℕ) (x : Legal n × Legal m) (i : Fin m) :
    (zeroJoin n m x).val ⟨n+1+i.val,by omega⟩ = x.2.val i := by
  simp [zeroJoin, zeroWord, show ¬n+1+i.val < n by omega,
    show n+1+i.val ≠ n by omega, show n+1+i.val-n-1 = i.val by omega]

private theorem zeroJoin_injective (n m : ℕ) : Function.Injective (zeroJoin n m) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    funext i
    simpa only [zero_left] using congrArg
      (fun w : Legal (n+m+1) => w.val ⟨i.val,by omega⟩) h
  · apply Subtype.ext
    funext i
    simpa only [zero_right] using congrArg
      (fun w : Legal (n+m+1) => w.val ⟨n+1+i.val,by omega⟩) h

private theorem zeroJoin_adj (n m : ℕ) (x y : Legal n × Legal m)
    (h : ((legalWordGraph n) □ (legalWordGraph m)).Adj x y) :
    (legalWordGraph (n+m+1)).Adj (zeroJoin n m x) (zeroJoin n m y) := by
  rcases x with ⟨b,c⟩
  rcases y with ⟨b',c'⟩
  rcases h with ⟨hbb,hcc⟩ | ⟨hcc,hbb⟩
  · change c = c' at hcc
    subst c'
    obtain ⟨i,hi,haw⟩ := (adj_iff n b b').mp hbb
    apply (adj_iff _ _ _).mpr
    refine ⟨⟨i.val,by omega⟩, by simpa only [zero_left] using hi, ?_⟩
    intro j hj
    by_cases hjn : j.val < n
    · simpa [zeroJoin, zeroWord, hjn] using haw ⟨j.val,hjn⟩ (by
        intro he; apply hj; apply Fin.ext; exact congrArg (fun k : Fin n => k.val) he)
    · simp [zeroJoin, zeroWord, hjn]
  · change b = b' at hbb
    subst b'
    obtain ⟨i,hi,haw⟩ := (adj_iff m c c').mp hcc
    apply (adj_iff _ _ _).mpr
    refine ⟨⟨n+1+i.val,by omega⟩, by simpa only [zero_right] using hi, ?_⟩
    intro j hj
    by_cases hjn : j.val < n
    · simp [zeroJoin, zeroWord, hjn]
    · by_cases hje : j.val = n
      · simp [zeroJoin, zeroWord, hjn, hje]
      · simpa [zeroJoin, zeroWord, hjn, hje] using haw ⟨j.val-n-1,by omega⟩ (by
          intro he; apply hj; apply Fin.ext
          have := congrArg Fin.val he; simp only [Fin.val_mk] at *; omega)

local notation "K" => (fun n : ℕ => kappa (legalWordGraph n))

private theorem nearly_additive (n m : ℕ) :
    K (n+m) ≤ K n + K m ∧ K n + K m ≤ K (n+m+1) := by
  have h1 := kappa_le_of_injective_hom (legalWordGraph (n+m))
    ((legalWordGraph n) □ (legalWordGraph m)) (splitWord n m) (split_injective n m) (split_adj n m)
  have h2 := kappa_le_of_injective_hom ((legalWordGraph n) □ (legalWordGraph m))
    (legalWordGraph (n+m+1)) (zeroJoin n m) (zeroJoin_injective n m) (zeroJoin_adj n m)
  rw [kappa_box] at h1 h2
  exact ⟨h1,h2⟩

private theorem native_zero : K 0 = 0 := by
  change kappa (legalWordGraph 0) = 0
  obtain ⟨a, ha, hm⟩ := minimum_attained (legalWordGraph 0)
  have he (b c : Legal 0) : ¬(legalWordGraph 0).Adj b c := by
    intro h
    obtain ⟨i,hi,haw⟩ := (adj_iff 0 b c).mp h
    exact Fin.elim0 i
  have hl (b : Legal 0) : load (legalWordGraph 0) a b = 0 := by
    simp [load, SimpleGraph.neighborFinset_eq_filter, he]
  rw [← hm]
  simp [maxLoad, hl]

private theorem native_nonneg (n : ℕ) : 0 ≤ K n := by
  change 0 ≤ kappa (legalWordGraph n)
  obtain ⟨a,ha,hm⟩ := minimum_attained (legalWordGraph n)
  rw [← hm]
  exact (sum_nonneg fun c _ => sq_nonneg (a (Classical.arbitrary (Legal n)) c)).trans
    (load_le_maxLoad (legalWordGraph n) a (Classical.arbitrary (Legal n)))

/-- The full native near-additivity, limit, infimum, supremum and all-length bracket. -/
theorem growth_constant :
    K 0 = 0 ∧
    (∀ n m, K (n+m) ≤ K n + K m ∧ K n + K m ≤ K (n+m+1)) ∧
    ∃ c : ℝ, Tendsto (fun n => K n / (n:ℝ)) atTop (𝓝 c) ∧
      c = sInf ((fun n : ℕ => K n / (n:ℝ)) '' Ici 1) ∧
      c = sSup (range (fun n : ℕ => K n / ((n:ℝ)+1))) ∧
      ∀ n : ℕ, c * n ≤ K n ∧ K n ≤ c * ((n:ℝ)+1) := by
  have hz := native_zero
  have hs : Subadditive K := fun n m => (nearly_additive n m).1
  have hb : BddBelow (range (fun n => K n / (n:ℝ))) :=
    ⟨0, by rintro r ⟨n,rfl⟩; exact div_nonneg (native_nonneg n) (Nat.cast_nonneg n)⟩
  let c := hs.lim
  have hc : Tendsto (fun n => K n / (n:ℝ)) atTop (𝓝 c) := hs.tendsto_lim hb
  have hr : Tendsto (fun n : ℕ => (n:ℝ)/((n:ℝ)+1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have hcshift : Tendsto (fun n : ℕ => K n / ((n:ℝ)+1)) atTop (𝓝 c) := by
    have ht := hc.mul hr
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    exact div_mul_div_cancel₀ hnr
  let u : ℕ → ℝ := fun j => -K (j-1)
  have hu : Subadditive u := by
    intro n m
    by_cases hn : n = 0
    · simp [u,hn,hz]
    by_cases hm : m = 0
    · simp [u,hm,hz]
    have he : n-1+(m-1)+1 = n+m-1 := by omega
    have hh := (nearly_additive (n-1) (m-1)).2
    change -K (n+m-1) ≤ -K (n-1) + -K (m-1)
    rw [← he]
    linarith
  have hlinear (n : ℕ) : K n ≤ (n:ℝ) * K 1 := by
    calc
      K n = K (n*1+0) := congrArg (fun j : ℕ => K j) (by omega)
      _ ≤ (n:ℝ) * K 1 + K 0 := hs.apply_mul_add_le n 1 0
      _ = (n:ℝ) * K 1 := by rw [hz, add_zero]
  have hub : BddBelow (range (fun n => u n / (n:ℝ))) := by
    refine ⟨-K 1, ?_⟩
    rintro r ⟨n,rfl⟩
    by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero, div_zero]
      exact neg_nonpos.mpr (native_nonneg 1)
    · apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
      have hn' : ((n-1:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      have ht := (hlinear (n-1)).trans (mul_le_mul_of_nonneg_right hn' (native_nonneg 1))
      change -K 1 * (n:ℝ) ≤ -K (n-1)
      nlinarith
  have huc : hu.lim = -c := by
    apply tendsto_nhds_unique (hu.tendsto_lim hub)
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa [u, Nat.cast_add, Nat.cast_one, neg_div] using hcshift.neg
  have hupper (n : ℕ) : K n / ((n:ℝ)+1) ≤ c := by
    have he := hu.lim_le_div hub (n := n+1) (by omega)
    have hv : u (n+1) = -K n := by
      change -K (n+1-1) = -K n
      exact congrArg (fun j : ℕ => -K j) (by omega)
    have heBound : -c ≤ -(K n / ((n:ℝ)+1)) := by
      calc
        -c = hu.lim := huc.symm
        _ ≤ u (n+1) / ((n+1:ℕ):ℝ) := he
        _ = (-K n) / ((n:ℝ)+1) := by rw [hv, Nat.cast_add, Nat.cast_one]
        _ = -(K n / ((n:ℝ)+1)) := neg_div _ _
    exact neg_le_neg_iff.mp heBound
  have hrat : BddAbove (range (fun n : ℕ => K n / ((n:ℝ)+1))) :=
    ⟨c, by rintro r ⟨n,rfl⟩; exact hupper n⟩
  refine ⟨hz, nearly_additive, c, hc, ?_, ?_, ?_⟩
  · change hs.lim = _
    rw [Subadditive.lim]
  · apply le_antisymm
    · exact le_of_tendsto hcshift (Eventually.of_forall fun n => le_csSup hrat (mem_range_self n))
    · exact csSup_le (range_nonempty _) (by rintro r ⟨n,rfl⟩; exact hupper n)
  · intro n
    constructor
    · by_cases hn : n = 0
      · calc
          c * (n:ℝ) = 0 := by rw [hn, Nat.cast_zero, mul_zero]
          _ ≤ K n := native_nonneg n
      · exact (le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mp (hs.lim_le_div hb hn)
    · exact (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mp (hupper n)

#print axioms growth_constant
#check growth_constant

end D5.S3.Combinatorics.Graph.LegalWords.BlockGrowth
