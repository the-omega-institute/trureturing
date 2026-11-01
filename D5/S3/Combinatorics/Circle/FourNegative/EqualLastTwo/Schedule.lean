/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastTwo/Schedule
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:consumed-physical-realization)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical bank masses and all-prefix reconstruction for equal last two gaps. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Physical
import D5.S3.Combinatorics.Circle.FourNegative.Descending.Banks
/-! Exact physical construction and doubled packet checks. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo
open SourceWidth PeriodicShortening RunFirstEarTransport
open private rank amplitude delta heads newHeads successor newSuccessor start length f g N
  source source_numeric shift image_Ico image_range bankLarge bankAdjacent
  largeP largeQ largeR largeG adjacentP adjacentQ adjacentR adjacentG
  corner2P corner2Q corner2R corner2G corner3P corner3Q corner3R corner3G
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Source
open private size base oldValue newValue source_totals from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private label lift_order marked_word from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private inserted_perm from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical

open private shift_sum sum_range_two sum_Ico_two from D5.S3.Combinatorics.Circle.FourNegative.Descending.Banks

private def weight (P : Finset ℕ) : ℤ := ∑ i ∈ P, (2:ℤ)^i
private theorem toList_sum (P : Finset ℕ) (v : ℕ → ℤ) :
    (P.toList.map v).sum=∑ i ∈ P, v i := by
  change ((P.toList : Multiset ℕ).map v).sum=_
  rw [Finset.coe_toList]
  rfl

private theorem large_weights (a b d : ℕ) (hd : 2 ≤ d) (hb : d+2 ≤ b) (ha : b < a) :
    let m : ℤ := 2^(a-d-3)
    let u : ℤ := 2^(a-b-1)
    weight (bankLarge a d (a-b-1) 0)=2^(a-1)-7*m ∧
    weight (bankLarge a d (a-b-1) 1)=2*m ∧
    weight (bankLarge a d (a-b-1) 2)=5*m-u ∧
    weight (bankLarge a d (a-b-1) 3)=u-1 := by
  have h0 : Disjoint ({a-d-3}:Finset ℕ) (Finset.Ico (a-d) (a-1)) := by
    simp [Finset.disjoint_left]; omega
  have h2 : Disjoint ({a-d-1}:Finset ℕ) (Finset.Ico (a-b-1) (a-d-3)) := by
    simp [Finset.disjoint_left]; omega
  simp only [bankLarge, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [weight,Finset.sum_union h0,Finset.sum_union h2,Finset.sum_singleton,
    sum_Ico_two _ _ (show a-d ≤ a-1 by omega),
    sum_Ico_two _ _ (show a-b-1 ≤ a-d-3 by omega),sum_range_two]
  have e0 : (2:ℤ)^(a-d)=2^(a-d-3)*2^3 := by
    rw [←pow_add]; congr 1; omega
  have e1 : (2:ℤ)^(a-d-2)=2^(a-d-3)*2^1 := by
    rw [←pow_add]; congr 1; omega
  have e2 : (2:ℤ)^(a-d-1)=2^(a-d-3)*2^2 := by
    rw [←pow_add]; congr 1; omega
  rw [e0,e1,e2]
  norm_num
  ring_nf <;> simp

private theorem adjacent_weights (a d : ℕ) (hd : 2 ≤ d) (ha : d+4 ≤ a) :
    let m : ℤ := 2^(a-d-4)
    weight (bankAdjacent a d 0)=2^(a-1)-15*m ∧
    weight (bankAdjacent a d 1)=2*m ∧
    weight (bankAdjacent a d 2)=8*m ∧
    weight (bankAdjacent a d 3)=5*m-1 := by
  have h0 : Disjoint ({a-d-4}:Finset ℕ) (Finset.Ico (a-d) (a-1)) := by
    simp [Finset.disjoint_left]; omega
  have h3 : Disjoint ({a-d-2}:Finset ℕ) (Finset.range (a-d-4)) := by
    simp [Finset.disjoint_left]; omega
  simp only [bankAdjacent, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [weight,Finset.sum_union h0,Finset.sum_union h3,Finset.sum_singleton,
    sum_Ico_two _ _ (show a-d ≤ a-1 by omega),sum_range_two]
  have e0 : (2:ℤ)^(a-d)=2^(a-d-4)*2^4 := by
    rw [←pow_add]; congr 1; omega
  have e1 : (2:ℤ)^(a-d-3)=2^(a-d-4)*2^1 := by
    rw [←pow_add]; congr 1; omega
  have e2 : (2:ℤ)^(a-d-1)=2^(a-d-4)*2^3 := by
    rw [←pow_add]; congr 1; omega
  have e3 : (2:ℤ)^(a-d-2)=2^(a-d-4)*2^2 := by
    rw [←pow_add]; congr 1; omega
  rw [e0,e1,e2,e3]
  norm_num
  ring_nf <;> simp

private theorem native_sum (v : ℕ → ℤ) (s n : ℕ) (A : ℤ)
    (h : ∀ i < n, v (s+i)=(2:ℤ)^i*A) :
    (∑ i ∈ shift s (Finset.range n), v i)=((2:ℤ)^n-1)*A := by
  exact (shift_sum v s (Finset.range n) A (fun i hi => h i (Finset.mem_range.mp hi))).trans
    (by rw [sum_range_two])

private theorem large_mass (a b d : ℕ) (hd : 2 ≤ d) (hb : d+2 ≤ b) (ha : b < a)
    (v : ℕ → ℤ) (U V W X : ℤ)
    (hU : ∀ i < d-1, v i=(2:ℤ)^i*U)
    (hV : ∀ i < d-1, v (d+i)=(2:ℤ)^i*V)
    (hW : ∀ i < b-1, v (2*d+i)=(2:ℤ)^i*W)
    (hX : ∀ i < a-1, v (2*d+b+i)=(2:ℤ)^i*X) :
    let m : ℤ := 2^(a-d-3)
    let u : ℤ := 2^(a-b-1)
    (∑ i ∈ largeP a b d, v i)=(2^(a-1)-7*m)*X ∧
    (∑ i ∈ largeQ a b d, v i)=(2^(d-1)-1)*U+2*m*X ∧
    (∑ i ∈ largeR a b d, v i)=(2^(d-1)-1)*V+(5*m-u)*X ∧
    (∑ i ∈ largeG a b d, v i)=(2^(b-1)-1)*W+(u-1)*X := by
  have bw := large_weights a b d hd hb ha
  have bx (r : Fin 4) :
      (∑ i ∈ shift (2*d+b) (bankLarge a d (a-b-1) r), v i)=weight (bankLarge a d (a-b-1) r)*X :=
    shift_sum v (2*d+b) (bankLarge a d (a-b-1) r) X (by
    intro i hi; apply hX i
    fin_cases r <;> simp [bankLarge] at hi <;> omega)
  have bU := native_sum v 0 (d-1) U (by simpa using hU)
  have bV := native_sum v d (d-1) V hV
  have bW := native_sum v (2*d) (b-1) W hW
  have dQ : Disjoint (Finset.range (d-1)) (shift (2*d+b) (bankLarge a d (a-b-1) 1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [shift] at hj; simp at hi; omega
  have dR : Disjoint (shift d (Finset.range (d-1))) (shift (2*d+b) (bankLarge a d (a-b-1) 2)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [shift] at hi hj; omega
  have dG : Disjoint (shift (2*d) (Finset.range (b-1))) (shift (2*d+b) (bankLarge a d (a-b-1) 3)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [shift] at hi hj; omega
  dsimp only [largeP,largeQ,largeR,largeG]
  rw [Finset.sum_union dQ,Finset.sum_union dR,Finset.sum_union dG,bx 0,bx 1,bx 2,bx 3,
    bw.1,bw.2.1,bw.2.2.1,bw.2.2.2,show (∑ i ∈ Finset.range (d-1),v i)=((2:ℤ)^(d-1)-1)*U by simpa [shift] using bU,bV,bW]
  exact ⟨rfl,rfl,rfl,rfl⟩

private theorem adjacent_mass (a d : ℕ) (hd : 2 ≤ d) (ha : d+4 ≤ a)
    (v : ℕ → ℤ) (U V W X : ℤ)
    (hU : ∀ i < d-1, v i=(2:ℤ)^i*U)
    (hV : ∀ i < d-1, v (d+i)=(2:ℤ)^i*V)
    (hW : ∀ i < d, v (2*d+i)=(2:ℤ)^i*W)
    (hX : ∀ i < a-1, v (3*d+1+i)=(2:ℤ)^i*X) :
    let m : ℤ := 2^(a-d-4)
    (∑ i ∈ adjacentP a d, v i)=(2^(a-1)-15*m)*X ∧
    (∑ i ∈ adjacentQ a d, v i)=(2^(d-1)-1)*U+2*m*X ∧
    (∑ i ∈ adjacentR a d, v i)=(2^(d-1)-1)*V+(8*m)*X ∧
    (∑ i ∈ adjacentG a d, v i)=(2^(d)-1)*W+(5*m-1)*X := by
  have bw := adjacent_weights a d hd ha
  have bx (r : Fin 4) :
      (∑ i ∈ shift (3*d+1) (bankAdjacent a d r), v i)=weight (bankAdjacent a d r)*X :=
    shift_sum v (3*d+1) (bankAdjacent a d r) X (by
    intro i hi; apply hX i
    fin_cases r <;> simp [bankAdjacent] at hi <;> omega)
  have bU := native_sum v 0 (d-1) U (by simpa using hU)
  have bV := native_sum v d (d-1) V hV
  have bW := native_sum v (2*d) (d) W hW
  have dQ : Disjoint (Finset.range (d-1)) (shift (3*d+1) (bankAdjacent a d 1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [shift] at hj; simp at hi; omega
  have dR : Disjoint (shift d (Finset.range (d-1))) (shift (3*d+1) (bankAdjacent a d 2)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [shift] at hi hj; omega
  have dG : Disjoint (shift (2*d) (Finset.range (d))) (shift (3*d+1) (bankAdjacent a d 3)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [shift] at hi hj; omega
  dsimp only [adjacentP,adjacentQ,adjacentR,adjacentG]
  rw [Finset.sum_union dQ,Finset.sum_union dR,Finset.sum_union dG,bx 0,bx 1,bx 2,bx 3,
    bw.1,bw.2.1,bw.2.2.1,bw.2.2.2,show (∑ i ∈ Finset.range (d-1),v i)=((2:ℤ)^(d-1)-1)*U by simpa [shift] using bU,bV,bW]
  exact ⟨rfl,rfl,rfl,rfl⟩

private theorem corner_two_mass (d : ℕ) (hd : 2 ≤ d)
    (v : ℕ → ℤ) (U V W X : ℤ)
    (hU : ∀ i < d-1, v i=(2:ℤ)^i*U)
    (hV : ∀ i < d-1, v (d+i)=(2:ℤ)^i*V)
    (hW : ∀ i < d, v (2*d+i)=(2:ℤ)^i*W)
    (hX : ∀ i < d+2-1, v (3*d+1+i)=(2:ℤ)^i*X) :
    (∑ i ∈ corner2P d, v i)=(2^(d-1)-1)*U+X ∧
    (∑ i ∈ corner2Q d, v i)=(2^(d-1)-1)*V+2*X ∧
    (∑ i ∈ corner2R d, v i)=(2^(d+1)-4)*X ∧
    (∑ i ∈ corner2G d, v i)=(2^d-1)*W := by
  have bU := native_sum v 0 (d-1) U (by simpa using hU)
  have bV := native_sum v d (d-1) V hV
  have bW := native_sum v (2*d) d W hW
  have x0 := hX 0 (by omega)
  have x1 := hX 1 (by omega)
  have bX : (∑ i ∈ shift (3*d+1) (Finset.Ico 2 (d+2-1)), v i)=
      (∑ i ∈ Finset.Ico 2 (d+2-1), (2:ℤ)^i)*X :=
    shift_sum v (3*d+1) (Finset.Ico 2 (d+2-1)) X (by
    intro i hi; apply hX; exact (Finset.mem_Ico.mp hi).2)
  rw [sum_Ico_two _ _ (show 2 ≤ d+2-1 by omega)] at bX
  have eX : shift (3*d+1) (Finset.Ico 2 (d+2-1))=
      Finset.Ico (3*d+3) (4*d+2) := by
    rw [shift,image_Ico]
    congr 1 <;> omega
  rw [eX,show d+2-1=d+1 by omega] at bX
  have dP : Disjoint (Finset.range (d-1)) ({3*d+1}:Finset ℕ) := by
    simp [Finset.disjoint_left]; omega
  have dQ : Disjoint (shift d (Finset.range (d-1))) ({3*d+2}:Finset ℕ) := by
    simp [Finset.disjoint_left,shift,image_range]; omega
  dsimp only [corner2P,corner2Q,corner2R,corner2G]
  rw [Finset.sum_union dP,Finset.sum_union dQ,Finset.sum_singleton,Finset.sum_singleton,
    show (∑ i ∈ Finset.range (d-1),v i)=((2:ℤ)^(d-1)-1)*U by simpa [shift] using bU,
    bV,bW,bX]
  simp only [Nat.add_zero,pow_zero,one_mul] at x0
  norm_num at x1
  rw [x0,show 3*d+2=3*d+1+1 by omega,x1]
  ring_nf <;> simp

private theorem corner_three_mass (d : ℕ) (hd : 2 ≤ d)
    (v : ℕ → ℤ) (U V W X : ℤ)
    (hU : ∀ i < d-1, v i=(2:ℤ)^i*U)
    (hV : ∀ i < d-1, v (d+i)=(2:ℤ)^i*V)
    (hW : ∀ i < d, v (2*d+i)=(2:ℤ)^i*W)
    (hX : ∀ i < d+3-1, v (3*d+1+i)=(2:ℤ)^i*X) :
    (∑ i ∈ corner3P d, v i)=(2^(d+2)-7)*X ∧
    (∑ i ∈ corner3Q d, v i)=(2^(d-1)-1)*V+4*X ∧
    (∑ i ∈ corner3R d, v i)=(2^(d-1)-1)*U+2*X ∧
    (∑ i ∈ corner3G d, v i)=(2^d-1)*W := by
  have bU := native_sum v 0 (d-1) U (by simpa using hU)
  have bV := native_sum v d (d-1) V hV
  have bW := native_sum v (2*d) d W hW
  have x0 := hX 0 (by omega)
  have x1 := hX 1 (by omega)
  have x2 := hX 2 (by omega)
  have bX : (∑ i ∈ shift (3*d+1) (Finset.Ico 3 (d+3-1)), v i)=
      (∑ i ∈ Finset.Ico 3 (d+3-1), (2:ℤ)^i)*X :=
    shift_sum v (3*d+1) (Finset.Ico 3 (d+3-1)) X (by
    intro i hi; apply hX; exact (Finset.mem_Ico.mp hi).2)
  rw [sum_Ico_two _ _ (show 3 ≤ d+3-1 by omega)] at bX
  have eX : shift (3*d+1) (Finset.Ico 3 (d+3-1))=
      Finset.Ico (3*d+4) (4*d+3) := by
    rw [shift,image_Ico]
    congr 1 <;> omega
  rw [eX,show d+3-1=d+2 by omega] at bX
  have dP : Disjoint ({3*d+1}:Finset ℕ) (Finset.Ico (3*d+4) (4*d+3)) := by
    simp [Finset.disjoint_left]
  have dQ : Disjoint (shift d (Finset.range (d-1))) ({3*d+3}:Finset ℕ) := by
    simp [Finset.disjoint_left,shift,image_range]; omega
  have dR : Disjoint (Finset.range (d-1)) ({3*d+2}:Finset ℕ) := by
    simp [Finset.disjoint_left]; omega
  dsimp only [corner3P,corner3Q,corner3R,corner3G]
  rw [Finset.sum_union dP,Finset.sum_union dQ,Finset.sum_union dR,
    Finset.sum_singleton,Finset.sum_singleton,Finset.sum_singleton,
    show (∑ i ∈ Finset.range (d-1),v i)=((2:ℤ)^(d-1)-1)*U by simpa [shift] using bU,
    bV,bW,bX]
  simp only [Nat.add_zero,pow_zero,one_mul] at x0
  norm_num at x1 x2
  rw [x0,show 3*d+2=3*d+1+1 by omega,x1,show 3*d+3=3*d+1+2 by omega,x2]
  ring_nf <;> simp

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
    funext i; dsimp [f,oldValue]; rw [hmod,hbase]; rfl
  have hg : g a b d=fun i => centered (modulus (rank a b d+1)) ((2:ℤ)^i*(2*amplitude a b d)) := by
    funext i; dsimp [g,newValue]; rw [hmodn,hbase]; rfl
  have hz := source_totals a b d d (by omega) (by omega) hd hd
  have hzero : ((List.range (rank a b d+1)).map (g a b d)).sum=0 := by
    rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    change ((List.range (size a b d d)).map (g a b d)).sum+g a b d (rank a b d)=0
    rw [show ((List.range (size a b d d)).map (g a b d)).sum = -base a b d d 0 from hz.2.1, (source a b d hd hb ha).2.2.2.2,hbase,hamp]; ring
  refine ⟨(P++T).map (label (rank a b d) hk),?_,?_,?_⟩
  · have hl := hp.length_eq
    simp only [List.length_append,List.length_range,hc] at hl
    omega
  · apply lift_order _ _ hk _ hp
    · simpa only [hf,hmod] using hold
    · have hzold : ((List.range (rank a b d)).map (f a b d)).sum=0 := hz.1
      simpa only [hf] using hzold
  · rw [marked_word (rank a b d) cut hk P T hc hp]
    apply lift_order _ _ (by omega) _ (inserted_perm _ _ _ hp)
    · have hh : modulus (rank a b d+1)/2=N a b d := by rw [hmodn]; omega
      simpa only [hg,hh,Nat.cast_mul,Nat.cast_ofNat] using hnew
    · simpa only [hg,Nat.cast_mul,Nat.cast_ofNat] using hzero

end D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo
