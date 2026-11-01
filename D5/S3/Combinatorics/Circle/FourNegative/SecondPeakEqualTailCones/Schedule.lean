/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Schedule
   generality: I
   mirror-B: none(waiver:private-consumed-all-prefix-construction)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Twelve seams control both physical words and the late fresh prefix. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Physical
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Physical
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open SourceWidth PeriodicShortening RunFirstEarTransport
open private rank amplitude N f g heads newHeads successor newSuccessor sourceN delta
  row_bounds terminal_row terminal_nonpos totals source_numeric
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Source
open private p H F C E domain_bounds mask_casts
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Native
open private allocation nativeAllocation dot termOrder doubledSeams gate last_seams
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Seams
open private all_gates
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Charts
open private bank terminal pre post terminal_index bank_inventory bank_masses bank_positive
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Physical
open private Checks
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Arithmetic
open private checks_strip
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Physical
open private blocksWord
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private oldValue newValue base
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private inserted_perm
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical

-- A seam cap is equivalent to the preceding positive peak cap after its terminal.
private theorem checks_four (cap p0 p1 p2 p3 n0 n1 n2 n3 : ℤ)
    (ht : p0+n0+p1+n1+p2+n2+p3+n3=0)
    (h0 : 0≤p0+n0) (c0 : p0+n0≤cap+n0)
    (h1 : 0≤p0+n0+p1+n1) (c1 : p0+n0+p1+n1≤cap+n1)
    (h2 : 0≤p0+n0+p1+n1+p2+n2) (c2 : p0+n0+p1+n1+p2+n2≤cap+n2)
    (c3 : 0≤cap+n3) :
    Checks cap 0 [(p0,n0),(p1,n1),(p2,n2),(p3,n3)] := by
  dsimp [Checks]
  repeat' constructor
  all_goals linarith

private theorem polynomial_checks (x y z u h v c wf xf : ℤ)
    (hu : 2*(u+1)=z) (hw : 2*(wf+1)=y) (hx : 2*(xf+1)=x)
    (hL : 1≤heads x y z 2) (hLn : 1≤newHeads x y z 2)
    (hg : ∀ r slot, 0≤gate x y z (allocation u h v c wf xf) r slot) :
    let m := allocation u h v c wf xf
    let A := heads x y z 0
    let n := sourceN x y z
    Checks (n-1) 0
      [(2*dot (heads x y z) (m 0),successor x y z 2-n),
       (2*dot (heads x y z) (m 1),successor x y z 0-n),
       (2*dot (heads x y z) (m 2),successor x y z 3-n),
       (2*dot (heads x y z) (m 3),successor x y z 1-n)] ∧
    Checks (2*n) 0
      [(2*dot (newHeads x y z) (m 0),newSuccessor x y z 2-(2*n+1)),
       (2*dot (newHeads x y z) (m 1),newSuccessor x y z 0-(2*n+1)),
       (2*dot (newHeads x y z) (m 2)+2*A,newSuccessor x y z 3-(2*n+1)),
       (2*dot (newHeads x y z) (m 3),newSuccessor x y z 1-(2*n+1))] := by
  have ht := last_seams x y z u h v c wf xf hu hw hx
  have a0 := hg 0 0
  have a1 := hg 0 1
  have a2 := hg 1 0
  have a3 := hg 1 1
  have a4 := hg 2 0
  have a5 := hg 2 1
  have b0 := hg 0 2
  have b1 := hg 0 3
  have b2 := hg 1 2
  have b3 := hg 1 3
  have b4 := hg 2 2
  have b5 := hg 2 3
  dsimp only [gate,doubledSeams] at a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 ht
  simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] at a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 ht
  dsimp only
  constructor
  · apply checks_four
    · linarith [ht.1]
    · linarith [a0]
    · linarith [a1]
    · linarith [a2]
    · linarith [a3]
    · linarith [a4]
    · linarith [a5]
    · simp only [successor,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
      linarith
  · apply checks_four
    · linarith [ht.2]
    · linarith [b0]
    · linarith [b1]
    · linarith [b2]
    · linarith [b3]
    · linarith [b4]
    · linarith [b5]
    · simp only [newSuccessor,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
      linarith

private def oldPackets (a b s : ℕ) : List (List ℕ×ℕ) :=
  [(bank a b s 0,terminal a b s 0),(bank a b s 1,terminal a b s 1),
   (bank a b s 2,terminal a b s 2),(bank a b s 3,terminal a b s 3)]
private def newPackets (a b s : ℕ) : List (List ℕ×ℕ) :=
  [(bank a b s 0,terminal a b s 0),(bank a b s 1,terminal a b s 1),
   (rank a b s::bank a b s 2,terminal a b s 2),(bank a b s 3,terminal a b s 3)]

set_option maxHeartbeats 1000000 in
private theorem physical_strips (a b s : ℕ) (hs : 2≤s)
    (hcone : (2*s+2≤a ∧ a+1≤b) ∨ (s+1≤a ∧ max (a+1) (3*s+1)≤b)) :
    InStrip (f a b s) (N a b s/2) 0 (pre a b s++post a b s) ∧
    InStrip (g a b s) (N a b s) 0 (pre a b s++rank a b s::post a b s) := by
  have bd := domain_bounds a b s hs hcone
  have bounds := row_bounds a b s (by omega) (by omega) hs
  have casts := mask_casts a b s hs bd.1 bd.2.1 bd.2.2
  have half (n : ℕ) (hn : 1≤n) : (2:ℤ)^n=2*2^(n-1) := by
    conv_lhs => rw [show n=(n-1)+1 by omega,pow_succ]
    ring
  have hu : 2*((2:ℤ)^(s-1)-1+1)=(2:ℤ)^s := by rw [half s (by omega)]; ring
  have hw : 2*((F b:ℤ)+1)=(2:ℤ)^b := by rw [casts.2.2.1,half b (by omega)]; ring
  have hx : 2*((E a:ℤ)+1)=(2:ℤ)^a := by rw [casts.2.2.2.2,half a (by omega)]; ring
  have gates := polynomial_checks (2^a) (2^b) (2^s) ((2:ℤ)^(s-1)-1)
    (H b s) (p a b s) (C a b s) (F b) (E a) hu hw hx
    (bounds.1 2).1 (bounds.2 2).1 (all_gates a b s hs hcone)
  have mf (r : Fin 4) :
      ((bank a b s r).map (f a b s)).sum=
        dot (heads (2^a) (2^b) (2^s)) (nativeAllocation a b s r) :=
    bank_masses a b s hs bd.1 bd.2.1 bd.2.2 false r
  have mg (r : Fin 4) :
      ((bank a b s r).map (g a b s)).sum=
        dot (newHeads (2^a) (2^b) (2^s)) (nativeAllocation a b s r) :=
    bank_masses a b s hs bd.1 bd.2.1 bd.2.2 true r
  have nt (r : Fin 4) :
      2*f a b s (terminal a b s r)=successor (2^a) (2^b) (2^s) (termOrder r)-N a b s ∧
      2*g a b s (terminal a b s r)=newSuccessor (2^a) (2^b) (2^s) (termOrder r)-(2*N a b s+1) := by
    rw [terminal_index a b s hs (by omega) (by omega)]
    exact terminal_row a b s (by omega) (by omega) hs (termOrder r)
  have negs (r : Fin 4) : f a b s (terminal a b s r)≤0 ∧ g a b s (terminal a b s r)≤0 := by
    rw [terminal_index a b s hs (by omega) (by omega)]
    exact terminal_nonpos a b s (by omega) (by omega) hs (termOrder r)
  have hear := (totals a b s (by omega) (by omega) hs).2.2
  have hN : 0≤N a b s := by have h := bounds.1 0; omega
  have hcap : 2*(N a b s/2)=N a b s-1 := by
    have he : N a b s=2*((2:ℤ)^(a-1)*2^b*2^s*2^s)-1 := by
      dsimp [N,sourceN]; rw [half a (by omega)]; ring
    omega
  have oldchecks : Checks (2*(N a b s/2)) 0
      ((oldPackets a b s).map (fun B => (2*(B.1.map (f a b s)).sum,2*f a b s B.2))) := by
    rw [hcap]
    simpa only [oldPackets,List.map_cons,List.map_nil,mf,
      (nt 0).1,(nt 1).1,(nt 2).1,(nt 3).1,termOrder,N,nativeAllocation,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
      using gates.1
  have newchecks : Checks (2*N a b s) 0
      ((newPackets a b s).map (fun B => (2*(B.1.map (g a b s)).sum,2*g a b s B.2))) := by
    simpa only [newPackets,List.map_cons,List.map_nil,List.sum_cons,mg,hear,
      (nt 0).2,(nt 1).2,(nt 2).2,(nt 3).2,
      termOrder,N,mul_add,add_comm,nativeAllocation,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] using gates.2
  have oldstrip : InStrip (f a b s) (N a b s/2) 0 (blocksWord (oldPackets a b s)) := by
    apply checks_strip _ _ _ (by omega) ?_ ?_ oldchecks
    · intro B hB i hi
      simp only [oldPackets,List.mem_cons,List.mem_nil_iff,or_false] at hB
      rcases hB with rfl|rfl|rfl|rfl
      · exact bank_positive a b s hs bd.1 bd.2.1 false 0 i hi
      · exact bank_positive a b s hs bd.1 bd.2.1 false 1 i hi
      · exact bank_positive a b s hs bd.1 bd.2.1 false 2 i hi
      · exact bank_positive a b s hs bd.1 bd.2.1 false 3 i hi
    · intro B hB
      simp only [oldPackets,List.mem_cons,List.mem_nil_iff,or_false] at hB
      rcases hB with rfl|rfl|rfl|rfl
      · exact (negs 0).1
      · exact (negs 1).1
      · exact (negs 2).1
      · exact (negs 3).1
  have newstrip : InStrip (g a b s) (N a b s) 0 (blocksWord (newPackets a b s)) := by
    apply checks_strip _ _ _ hN ?_ ?_ newchecks
    · intro B hB i hi
      simp only [newPackets,List.mem_cons,List.mem_nil_iff,or_false] at hB
      rcases hB with rfl|rfl|rfl|rfl
      · exact bank_positive a b s hs bd.1 bd.2.1 true 0 i hi
      · exact bank_positive a b s hs bd.1 bd.2.1 true 1 i hi
      · rcases List.mem_cons.mp hi with rfl|hi
        · rw [hear]
          have hh := (bounds.1 0).1
          omega
        · exact bank_positive a b s hs bd.1 bd.2.1 true 2 i hi
      · exact bank_positive a b s hs bd.1 bd.2.1 true 3 i hi
    · intro B hB
      simp only [newPackets,List.mem_cons,List.mem_nil_iff,or_false] at hB
      rcases hB with rfl|rfl|rfl|rfl
      · exact (negs 0).2
      · exact (negs 1).2
      · exact (negs 2).2
      · exact (negs 3).2
  constructor
  · simpa only [oldPackets,blocksWord,pre,post,List.append_assoc,List.singleton_append] using oldstrip
  · simpa only [newPackets,blocksWord,pre,post,List.append_assoc,List.singleton_append,
      List.cons_append] using newstrip

private theorem physical_finish (a b s : ℕ) (hs : 2≤s)
    (hcone : (2*s+2≤a ∧ a+1≤b) ∨ (s+1≤a ∧ max (a+1) (3*s+1)≤b)) :
    ∃ sigma : List (Fin (rank a b s)), ∃ j : ℕ, j≤rank a b s ∧
      OriginalOrder (rank a b s) (amplitude a b s) sigma ∧
      OriginalOrder (rank a b s+1) (2*amplitude a b s) (earWord (rank a b s) sigma j) := by
  have bd := domain_bounds a b s hs hcone
  have hp := bank_inventory a b s hs bd.1 bd.2.1 bd.2.2
  have strips := physical_strips a b s hs hcone
  have hk : 0<rank a b s := by dsimp [rank]; omega
  have num := source_numeric a b s
  have hbase : base a b s s 0=(amplitude a b s:ℤ) := by
    rw [num.2.2]
    dsimp [base,heads,delta]
    ring
  have hf : f a b s=fun i => centered (modulus (rank a b s)) ((2:ℤ)^i*amplitude a b s) := by
    funext i
    dsimp [f,oldValue]
    rw [num.1,hbase]
    rfl
  have hg : g a b s=fun i => centered (modulus (rank a b s+1)) ((2:ℤ)^i*(2*amplitude a b s)) := by
    funext i
    dsimp [g,newValue]
    rw [num.2.1,hbase]
    rfl
  have hz := totals a b s (by omega) (by omega) hs
  have hzn : ((List.range (rank a b s+1)).map (g a b s)).sum=0 := by
    rw [List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hz.2.1,hz.2.2]
    ring
  refine ⟨(pre a b s++post a b s).map (label (rank a b s) hk),(pre a b s).length,?_,?_,?_⟩
  · have hl := hp.length_eq
    simp only [List.length_append,List.length_range] at hl
    omega
  · apply lift_order _ _ hk _ hp
    · simpa only [hf,num.1] using strips.1
    · simpa only [hf] using hz.1
  · rw [marked_word (rank a b s) (pre a b s).length hk (pre a b s) (post a b s) rfl hp]
    apply lift_order _ _ (by omega) _ (inserted_perm _ _ _ hp)
    · have hh : modulus (rank a b s+1)/2=N a b s := by rw [num.2.1]; omega
      simpa only [hg,hh,Nat.cast_mul,Nat.cast_ofNat] using strips.2
    · simpa only [hg,Nat.cast_mul,Nat.cast_ofNat] using hzn

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
