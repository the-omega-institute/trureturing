/- GID: D5/S1/Words/Palindromes/PeriodDoubling/BaseArithmetic
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/BaseArithmetic
   mirror-E: none(waiver:unbounded-transducer-arithmetic-realization)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result; instance=D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTable
   digest: Concrete transducer paths encode exact signed-weight differences of rounded halves. -/

/-
proof_shape: content (base_path_signed_weight_difference)
escape_witness: Carry-state reconstruction and greedy signed-digit induction for arbitrary path lengths.
admission_basis: escape-witness
Direct frozen dependencies: none; BaseCertificates and SignedWeight are delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.BaseCertificates
import D5.S1.Words.Palindromes.PeriodDoubling.SignedWeight
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates

private def edgeArithmeticCheck (i : ℕ) : Bool :=
  let S := (baseTable i).1
  ((baseTable i).2.1).all fun e =>
    let T := (baseTable e.1).1
    let dn := T[10]?.getD 0
    let dj := T[12]?.getD 0
    decide (
      (dn = -1 ∨ dn = 0 ∨ dn = 1) ∧
      (dj = -1 ∨ dj = 0 ∨ dj = 1) ∧
      2*e.2.2.2.1+2*(S[4]?.getD 0)+(S[6]?.getD 0)+(S[8]?.getD 0) =
        dn+2*(2*(T[4]?.getD 0)+(T[6]?.getD 0)+(T[8]?.getD 0)) ∧
      2*e.2.2.2.2+2*(S[5]?.getD 0)+(S[7]?.getD 0)+(S[9]?.getD 0) =
        dj+2*(2*(T[5]?.getD 0)+(T[7]?.getD 0)+(T[9]?.getD 0)) ∧
      (dn ≠ 0 → ((T[6]?.getD 0)+(T[8]?.getD 0)) % 2 = 0) ∧
      (dj ≠ 0 → ((T[7]?.getD 0)+(T[9]?.getD 0)) % 2 = 0) ∧
      e.2.1 = (Bool.toNat (dn != 0) : ℤ)-(Bool.toNat (dj != 0) : ℤ))

private def arithmeticBlockCheck (start count : ℕ) : Bool :=
  (List.range count).all fun k => edgeArithmeticCheck (start+k)

/-- Accepted base paths encode exactly the difference of their two signed weights. -/
theorem base_path_signed_weight_difference (charge : Bool) {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
    (hs : s ∈ (baseAutomaton charge).start)
    (ht : t ∈ (baseAutomaton charge).accept)
    (p : (baseAutomaton charge).Path s t xs) :
    pathCharge (fun _ a _ => a.1) p =
      (signedWeight (xs.foldr (fun a x => a.2.2.1 + 2*x) 0 +
        ((baseTable s.val).1[2]?.getD 0)) : ℤ) -
      (signedWeight (xs.foldr (fun a x => a.2.2.2 + 2*x) 0 +
        ((baseTable s.val).1[3]?.getD 0)) : ℤ) := by
  obtain ⟨hz,h1,hn,htw,he,ho⟩ := signed_weight_arithmetic
  have neighbor (x : ℤ) : signedWeight x ≤ signedWeight (x+1)+1 ∧
      signedWeight (x+1) ≤ signedWeight x+1 := by
    have hminus : signedWeight (-1) = 1 := (hn 1).trans h1
    have hlow := htw (x+1) (-1)
    have hupp := htw x 1
    simp only [show x+1+-1=x by ring, hminus] at hlow
    simp only [h1] at hupp
    exact ⟨hlow,hupp⟩
  have greedy (X d : ℤ) (hd : d=-1 ∨ d=0 ∨ d=1)
      (hpar : d ≠ 0 → X%2=0) :
      signedWeight (d+2*X) = Bool.toNat (d != 0)+signedWeight X := by
    rcases hd with hd | hd | hd
    · subst d
      have hp := hpar (by decide)
      let k := X/2
      have hk : X = 2*k := by dsimp [k]; omega
      rw [hk]
      have hl : signedWeight (2*k-1) ≥ signedWeight k := by
        have hh := ho (k-1)
        have hnbr := (neighbor (k-1)).2
        have hkm : k-1+1=k := by ring
        rw [hkm] at hh hnbr
        have eq : 2*(k-1)+1=2*k-1 := by ring
        rw [eq] at hh
        omega
      have hw := ho (2*k-1)
      rw [show 2*(2*k-1)+1 = -1+2*(2*k) by ring] at hw
      have hh := he k
      have hm : (2*k-1)+1=2*k := by ring
      rw [hm] at hw
      simp only [show ((-1:ℤ) != 0) = true by decide, Bool.toNat_true]
      rw [hw]
      omega
    · subst d
      simpa using he X
    · subst d
      have hp := hpar (by decide)
      let k := X/2
      have hk : X = 2*k := by dsimp [k]; omega
      rw [hk]
      have hl : signedWeight (2*k+1) ≥ signedWeight k := by
        have hh := ho k
        have hnbr := (neighbor k).1
        omega
      have hw := ho (2*k)
      have hh := he k
      simp only [show ((1:ℤ) != 0) = true by decide, Bool.toNat_true]
      rw [show 1+2*(2*k) = 2*(2*k)+1 by ring, hw]
      omega
  have checked (i : ℕ) (hi : i<1492) : edgeArithmeticCheck i = true := by
    have blocks : ∀ b : Fin 24,
      arithmeticBlockCheck (64*b.val) (min 64 (1492-64*b.val)) = true := by
      intro b
      fin_cases b <;> decide
    have h := blocks ⟨i/64, by omega⟩
    dsimp [arithmeticBlockCheck] at h
    have hk : i%64 ∈ List.range (min 64 (1492-64*(i/64))) := by
      simp only [List.mem_range]; omega
    have hh := List.all_eq_true.mp h (i%64) hk
    have heq : 64*(i/64)+i%64=i := by omega
    simpa only [heq] using hh
  let rawN : List (ℤ × ℤ × ℤ × ℤ) → ℤ := fun xs => xs.foldr (fun a x => a.2.2.1+2*x) 0
  let rawJ : List (ℤ × ℤ × ℤ × ℤ) → ℤ := fun xs => xs.foldr (fun a x => a.2.2.2+2*x) 0
  let RN : Fin 1492 → List (ℤ × ℤ × ℤ × ℤ) → ℤ := fun s xs =>
    2*(rawN xs+(baseTable s.val).1[4]?.getD 0)+
      (baseTable s.val).1[6]?.getD 0+(baseTable s.val).1[8]?.getD 0
  let RJ : Fin 1492 → List (ℤ × ℤ × ℤ × ℤ) → ℤ := fun s xs =>
    2*(rawJ xs+(baseTable s.val).1[5]?.getD 0)+
      (baseTable s.val).1[7]?.getD 0+(baseTable s.val).1[9]?.getD 0
  have hf : baseTerminal (baseTable t.val).1 = true := by
    have ht' := ht
    simp only [baseAutomaton, Set.mem_ofPred_eq] at ht'
    simp only [Bool.and_eq_true] at ht'
    exact ht'.1
  have hend : RN t [] = 0 ∧ RJ t [] = 0 := by
    simp only [baseTerminal, Bool.and_eq_true, List.all_eq_true] at hf
    have ht4 := hf.2 4 (by simp)
    have ht5 := hf.2 5 (by simp)
    have ht6 := hf.2 6 (by simp)
    have ht7 := hf.2 7 (by simp)
    have ht8 := hf.2 8 (by simp)
    have ht9 := hf.2 9 (by simp)
    simp only [beq_iff_eq] at ht4 ht5 ht6 ht7 ht8 ht9
    simp [RN,RJ,rawN,rawJ,ht4,ht5,ht6,ht7,ht8,ht9]
  have pathid {s t : Fin 1492} {xs : List (ℤ × ℤ × ℤ × ℤ)}
      (p : (baseAutomaton charge).Path s t xs) :
      pathCharge (fun _ a _ => a.1) p =
        ((signedWeight (RN s xs) : ℤ)-(signedWeight (RJ s xs) : ℤ)) -
        ((signedWeight (RN t []) : ℤ)-(signedWeight (RJ t []) : ℤ)) := by
    induction p with
    | nil s => simp [pathCharge]
    | cons q s t a xs hstep p ih =>
      have hc := List.all_eq_true.mp (checked s.val s.isLt)
      have hm : (q.val,a) ∈ (baseTable s.val).2.1 := hstep
      have hrel := hc (q.val,a) hm
      dsimp only [edgeArithmeticCheck] at hrel
      have hdata := of_decide_eq_true hrel
      rcases hdata with ⟨hdn,hdj,hnstep,hjstep,hnpar,hjpar,hfstep⟩
      have hRn : RN s (a::xs) = (baseTable q.val).1[10]?.getD 0+2*RN q xs := by
        dsimp [RN,rawN]
        omega
      have hRj : RJ s (a::xs) = (baseTable q.val).1[12]?.getD 0+2*RJ q xs := by
        dsimp [RJ,rawJ]
        omega
      have hnp : (baseTable q.val).1[10]?.getD 0 ≠ 0 → RN q xs % 2=0 := by
        intro hh
        have hv := hnpar hh
        dsimp [RN]
        omega
      have hjp : (baseTable q.val).1[12]?.getD 0 ≠ 0 → RJ q xs % 2=0 := by
        intro hh
        have hv := hjpar hh
        dsimp [RJ]
        omega
      have hwn := greedy (RN q xs) _ hdn hnp
      have hwj := greedy (RJ q xs) _ hdj hjp
      rw [hRn,hRj,hwn,hwj]
      simp only [pathCharge]
      omega
  have hp := pathid p
  rw [hend.1,hend.2,hz] at hp
  have hs' : s.val=0 ∨ s.val=1 ∨ s.val=2 ∨ s.val=3 ∨ s.val=4 ∨ s.val=5 ∨ s.val=6 := by
    change ([0,1,2,3,4,5,6] : List ℕ).contains s.val = true at hs
    simpa using hs
  have hsn : RN s xs = 2*(rawN xs+(baseTable s.val).1[2]?.getD 0) := by
    dsimp [RN]
    rcases hs' with h | h | h | h | h | h | h <;> rw [h] <;> norm_num [baseTable]
  have hsj : RJ s xs = 2*(rawJ xs+(baseTable s.val).1[3]?.getD 0) := by
    dsimp [RJ]
    rcases hs' with h | h | h | h | h | h | h <;> rw [h] <;> norm_num [baseTable]
  rw [hsn,hsj,he,he] at hp
  simpa [rawN,rawJ] using hp

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.base_path_signed_weight_difference
