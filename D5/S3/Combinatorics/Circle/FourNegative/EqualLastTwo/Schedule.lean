/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastTwo/Schedule
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:consumed-physical-realization)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical bank masses and all-prefix reconstruction for equal last two gaps. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Physical
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo
open SourceWidth PeriodicShortening RunFirstEarTransport
open private rank amplitude delta heads newHeads successor newSuccessor start length f g N
  source source_numeric shift image_Ico image_range bankLarge bankAdjacent
  largeP largeQ largeR largeG adjacentP adjacentQ adjacentR adjacentG
  corner2P corner2Q corner2R corner2G corner3P corner3Q corner3R corner3G
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Source
open private size base source_totals from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private label lift_order marked_word from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private inserted_perm from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical

private def weight (P : Finset ℕ) : ℤ := ∑ i ∈ P, (2:ℤ)^i
private theorem weight_range (n : ℕ) : weight (Finset.range n)=(2:ℤ)^n-1 := by
  simpa [weight] using geom_sum_mul (2:ℤ) n
private theorem weight_Ico (lo hi : ℕ) (h : lo ≤ hi) :
    weight (Finset.Ico lo hi)=(2:ℤ)^hi-2^lo := by
  simpa [weight] using geom_sum_Ico_mul (2:ℤ) h
private theorem weight_insert (i : ℕ) (P : Finset ℕ) (h : i ∉ P) :
    weight (insert i P)=(2:ℤ)^i+weight P := by
  exact Finset.sum_insert h
private theorem weight_singleton (i : ℕ) : weight {i}=(2:ℤ)^i := by simp [weight]

private theorem toList_sum (P : Finset ℕ) (v : ℕ → ℤ) :
    (P.toList.map v).sum=∑ i ∈ P, v i := by
  simp only [←Finset.sum_toList, List.sum_map]

private theorem bank_data (a b d : ℕ) (hd : 2 ≤ d) (hb : d < b) (ha : b < a)
    (r : Fin 4) (P : Finset ℕ) (hP : ∀ i ∈ P, i < length a b d r-1) :
    (∑ i ∈ shift (start b d r) P, f a b d i) =
      weight P*heads ((2:ℤ)^a) (2^b) (2^d) r ∧
    (∑ i ∈ shift (start b d r) P, g a b d i) =
      weight P*newHeads ((2:ℤ)^a) (2^b) (2^d) r := by
  have tab := (source a b d hd hb ha).2.2.1
  have hf : ∀ i ∈ P, f a b d (start b d r+i)=(2:ℤ)^i*heads ((2:ℤ)^a) (2^b) (2^d) r :=
    fun i hi => (tab r i (hP i hi)).1
  have hg : ∀ i ∈ P, g a b d (start b d r+i)=(2:ℤ)^i*newHeads ((2:ℤ)^a) (2^b) (2^d) r :=
    fun i hi => (tab r i (hP i hi)).2
  constructor
  · rw [shift,Finset.sum_image (by intro i hi j hj hij; omega)]
    rw [Finset.sum_congr rfl hf,←Finset.sum_mul]; rfl
  · rw [shift,Finset.sum_image (by intro i hi j hj hij; omega)]
    rw [Finset.sum_congr rfl hg,←Finset.sum_mul]; rfl

private theorem finish (a b d : ℕ) (hd : 2 ≤ d) (hb : d < b) (ha : b < a)
    (cut : ℕ) (P T : List ℕ) (hc : P.length=cut)
    (hp : (P++T).Perm (List.range (rank a b d)))
    (hold : InStrip (f a b d) (N a b d/2) 0 (P++T))
    (hnew : InStrip (g a b d) (N a b d) 0 (P++rank a b d::T)) :
    ∃ sigma : List (Fin (rank a b d)), cut ≤ rank a b d ∧
      OriginalOrder (rank a b d) (amplitude a b d) sigma ∧
      OriginalOrder (rank a b d+1) (2*amplitude a b d)
        (earWord (rank a b d) sigma cut) := by
  have hk : 0 < rank a b d := by dsimp [rank]; omega
  obtain ⟨_,hmod,hmodn,hamp⟩ := source_numeric a b d
  have hbase : base a b d d 0=(amplitude a b d:ℤ) := by
    rw [hamp]; dsimp [base,heads,delta]; ring
  have hf : f a b d=fun i => centered (modulus (rank a b d)) ((2:ℤ)^i*amplitude a b d) := by
    funext i; dsimp [f]; rw [hmod,hbase]; rfl
  have hg : g a b d=fun i => centered (modulus (rank a b d+1)) ((2:ℤ)^i*(2*amplitude a b d)) := by
    funext i; dsimp [g]; rw [hmodn,hbase]; rfl
  have hz := source_totals a b d d (by omega) (by omega) hd hd
  have hzero : ((List.range (rank a b d+1)).map (g a b d)).sum=0 := by
    rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    change ((List.range (size a b d d)).map (g a b d)).sum+g a b d (rank a b d)=0
    rw [hz.2.1,(source a b d hd hb ha).2.2.2.2,hbase,hamp]; ring
  refine ⟨(P++T).map (label (rank a b d) hk),?_,?_,?_⟩
  · have hl := hp.length_eq
    simp only [List.length_append,List.length_range,hc] at hl
    omega
  · apply lift_order _ _ hk _ hp
    · simpa only [hf,hmod] using hold
    · simpa only [hf,f,rank,size] using hz.1
  · rw [marked_word (rank a b d) cut hk P T hc hp]
    apply lift_order _ _ (by omega) _ (inserted_perm _ _ _ hp)
    · have hh : modulus (rank a b d+1)/2=N a b d := by rw [hmodn]; omega
      simpa only [hg,hh,Nat.cast_mul,Nat.cast_ofNat] using hnew
    · simpa only [hg,Nat.cast_mul,Nat.cast_ofNat] using hzero

end D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo
