/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C2Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C2Endpoint
   mirror-E: none(waiver:physical-dependent-source-registration)
   anchors: [lake/module/D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source]
   utility: none
   digest: Actual c2 physical sides with the exceptional order retained. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C2Gates
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.Completion

/-! Actual c2 physical sides with the exceptional order retained. Original source owners supply the reused proofs. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
open PacketNormalForm SourceWidth PeriodicShortening RunFirstEarTransport
open private sourceMod charge nextBase nextNewBase chain_values source_totals from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private scalarMass boundary2 oldBoundary2 newBoundary2 from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C2Gates
open scoped BigOperators

private theorem c2_domain (b d : ℕ) (hd : 4 ≤ d) (hbd : d < b) :
    OriginalDomain 3 b 2 d := ⟨hbd, Or.inl ⟨rfl, rfl, hd⟩⟩

private theorem c2_inventory_actual (b d : ℕ) (hd : 4 ≤ d) (hbd : d < b) :
    ∀ r : Fin 4, MaskInventory (chainLength 3 b 2 d r - 1)
      (fun row => c2Banks (d-3) (b-d-1) row r) := by
  simpa [residualBanks] using
    residual_inventory 3 b 2 d (c2_domain b d hd hbd)

private noncomputable def c2Word (b d : ℕ) : List ℕ :=
  physicalWord 3 b 2 d (c2Banks (d-3) (b-d-1)) (c2Order (d-3))

private theorem c2_word_perm (b d : ℕ) (hd : 4 ≤ d) (hbd : d < b) :
    (c2Word b d).Perm (List.range (size 3 b 2 d)) := by
  apply Multiset.coe_eq_coe.mp
  simpa [c2Word, residualBanks, residualOrder] using
    original_physical_partition 3 b 2 d (c2_domain b d hd hbd)

/-- Only parameter substitution: no centered-orbit assertion is inferred
    from the scalar cycle equations. -/
private theorem c2_parameters (b d : ℕ) (hd : 4 ≤ d) (hbd : d < b) :
    sourceMod 3 b 2 d = c2N (2^(d-3)) (2^(b-d-1)) ∧
    base 3 b 2 d = c2OldHead (2^(d-3)) (2^(b-d-1)) ∧
    newBase 3 b 2 d = c2NewHead (2^(d-3)) (2^(b-d-1)) ∧
    nextBase 3 b 2 d = c2OldSuccessor (2^(d-3)) (2^(b-d-1)) ∧
    nextNewBase 3 b 2 d = c2NewSuccessor (2^(d-3)) (2^(b-d-1)) := by
  have hdP : (2 : ℤ)^d = 8 * 2^(d-3) := by
    conv_lhs => rw [show d = (d-3)+3 by omega, pow_add]
    norm_num
    ring
  have hbP : (2 : ℤ)^b = 16 * 2^(d-3) * 2^(b-d-1) := by
    conv_lhs => rw [show b = (d-3)+(b-d-1)+4 by omega, pow_add, pow_add]
    norm_num
    ring
  have hN : sourceMod 3 b 2 d = c2N (2^(d-3)) (2^(b-d-1)) := by
    norm_num [sourceMod, c2N, hdP, hbP]
    ring
  have hB : base 3 b 2 d = c2OldHead (2^(d-3)) (2^(b-d-1)) := by
    funext r
    fin_cases r <;> norm_num [base, c2OldHead, hdP, hbP] <;> ring
  have hBn : newBase 3 b 2 d = c2NewHead (2^(d-3)) (2^(b-d-1)) := by
    funext r
    fin_cases r <;> norm_num [newBase, charge, c2NewHead, hB, hbP] <;> ring
  refine ⟨hN, hB, hBn, ?_, ?_⟩
  · funext r
    fin_cases r <;> simp [nextBase, c2OldSuccessor, hB]
  · funext r
    fin_cases r <;> simp [nextNewBase, c2NewSuccessor, hB, hBn]

/-- The signed quotients are the original terminal expressions, including
    the last NEW successor OLD A.  The fresh label is separately OLD A. -/
private theorem c2_source_terminals (b d : ℕ) (hd : 4 ≤ d) (hbd : d < b) :
    (∀ r : Fin 4,
      oldValue 3 b 2 d (terminalLabel 3 b 2 d r) =
        c2OldDrop (2^(d-3)) (2^(b-d-1)) r ∧
      newValue 3 b 2 d (terminalLabel 3 b 2 d r) =
        c2NewDrop (2^(d-3)) (2^(b-d-1)) r) ∧
    newValue 3 b 2 d (size 3 b 2 d) = base 3 b 2 d 0 := by
  have tab := chain_values 3 b 2 d (by omega) (by omega) (by omega) (by omega)
  obtain ⟨hN,hB,hBn,hnext,hnextn⟩ := c2_parameters b d hd hbd
  refine ⟨?_,tab.2.2.2⟩
  intro r
  have hlen : 1 ≤ chainLength 3 b 2 d r := by
    fin_cases r <;> simp [chainLength] <;> omega
  have ht : chainStart b 2 d r + (chainLength 3 b 2 d r-1) =
      terminalLabel 3 b 2 d r := by dsimp [terminalLabel]; omega
  have ho := tab.2.1 r (chainLength 3 b 2 d r-1) (by omega)
  have hn := tab.2.2.1 r (chainLength 3 b 2 d r-1) (by omega)
  rw [ht, if_neg (by omega), hN, hnext, neg_sub] at ho
  rw [ht, if_neg (by omega), hN, hnextn, neg_sub] at hn
  have halves := c2_scalar_drops (2^(d-3)) (2^(b-d-1)) r
  exact ⟨ho.trans halves.2.2.1, hn.trans halves.2.2.2⟩

private theorem c2_bank_masses (b d : ℕ) (hd : 4 ≤ d) (hbd : d < b)
    (row : Fin 4) :
    oldMass 3 b 2 d (physicalBank 3 b 2 d (c2Banks (d-3) (b-d-1)) row) =
      c2OldMass (d-3) (b-d-1) row ∧
    newMass 3 b 2 d (physicalBank 3 b 2 d (c2Banks (d-3) (b-d-1)) row) =
      c2NewMass (d-3) (b-d-1) row := by
  have inv := c2_inventory_actual b d hd hbd
  have hp := physical_masses 3 b 2 d (by omega) (by omega) (by omega) (by omega)
    (c2Banks (d-3) (b-d-1)) inv row
  have hm := packet_masses 3 b 2 d (by omega) (by omega) (by omega) (by omega)
    (physicalBank 3 b 2 d (c2Banks (d-3) (b-d-1)) row)
    (physical_labels 3 b 2 d (by omega) (by omega) (by omega) (by omega)
      (c2Banks (d-3) (b-d-1)) inv row)
  have par := c2_parameters b d hd hbd
  constructor
  · change (∑ r : Fin 4, base 3 b 2 d r * weightedMask b 2 d
      (physicalBank 3 b 2 d (c2Banks (d-3) (b-d-1)) row) r) = _
    rw [← hm.1, hp.1, par.2.1]
    simp [c2OldMass, scalarMass, Fin.sum_univ_succ, Fin.sum_univ_zero]
    ring
  · change (∑ r : Fin 4, newBase 3 b 2 d r * weightedMask b 2 d
      (physicalBank 3 b 2 d (c2Banks (d-3) (b-d-1)) row) r) = _
    rw [← hm.2, hp.2, par.2.2.1]
    simp [c2NewMass, scalarMass, Fin.sum_univ_succ, Fin.sum_univ_zero]
    ring

private noncomputable def c2OldSeam (b d : ℕ) : Fin 5 → ℤ :=
  boundary2 0 (fun row =>
    oldMass 3 b 2 d (physicalBank 3 b 2 d (c2Banks (d-3) (b-d-1)) row) +
      oldValue 3 b 2 d (terminalLabel 3 b 2 d (c2Order (d-3) row)))

private noncomputable def c2NewSeam (b d : ℕ) : Fin 5 → ℤ :=
  boundary2 (base 3 b 2 d 0) (fun row =>
    newMass 3 b 2 d (physicalBank 3 b 2 d (c2Banks (d-3) (b-d-1)) row) +
      newValue 3 b 2 d (terminalLabel 3 b 2 d (c2Order (d-3) row)))

private theorem c2_boundary_transport (b d : ℕ) (hd : 4 ≤ d) (hbd : d < b)
    (i : Fin 5) :
    2*c2OldSeam b d i = c2OldBoundary2 (d-3) (b-d-1) i ∧
    2*c2NewSeam b d i = c2NewBoundary2 (d-3) (b-d-1) i := by
  have masses := c2_bank_masses b d hd hbd
  have terminal := (c2_source_terminals b d hd hbd).1
  have par := c2_parameters b d hd hbd
  have ho (row : Fin 4) := (c2_scalar_drops (2^(d-3)) (2^(b-d-1))
    (c2Order (d-3) row)).1
  have hn (row : Fin 4) := (c2_scalar_drops (2^(d-3)) (2^(b-d-1))
    (c2Order (d-3) row)).2.1
  have ho0 := ho 0
  have ho1 := ho 1
  have ho2 := ho 2
  have ho3 := ho 3
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  have hn3 := hn 3
  fin_cases i <;> constructor <;>
    simp [c2OldSeam, c2NewSeam, c2OldBoundary2, c2NewBoundary2,
      oldBoundary2, newBoundary2, boundary2, masses, terminal, par.2.1, c2OldMass, c2NewMass] <;>
    nlinarith only [ho0,ho1,ho2,ho3,hn0,hn1,hn2,hn3]

/-- The full c2 cone supplies ACTUAL physical lower-old/upper-new sides
    and separate totals to both consumers of the common completion.
    c2Order is unchanged, including e=4 order [2,3,0,1]. -/
theorem c2_physical_gates (b d : ℕ) (hd : 4 ≤ d) (hbd : d < b) :
    ActualPhysicalGateSides 3 b 2 d := by
  have inv := c2_inventory_actual b d hd hbd
  have masses (r : Fin 4) :
      physicalOldMass 3 b 2 d (c2Banks (d-3) (b-d-1)) r =
        oldMass 3 b 2 d (physicalBank 3 b 2 d (c2Banks (d-3) (b-d-1)) r) ∧
      physicalNewMass 3 b 2 d (c2Banks (d-3) (b-d-1)) r =
        newMass 3 b 2 d (physicalBank 3 b 2 d (c2Banks (d-3) (b-d-1)) r) := by
    exact packet_masses 3 b 2 d (by omega) (by omega) (by omega) (by omega) _
      (physical_labels 3 b 2 d (by omega) (by omega) (by omega) (by omega)
        _ inv r)
  have fresh := (c2_source_terminals b d hd hbd).2
  have hH : physicalOldBoundary 3 b 2 d (residualBanks 3 b 2 d)
      (residualOrder 2 d) = c2OldSeam b d := by
    funext i
    simp [physicalOldBoundary,residualBanks,residualOrder,c2OldSeam,boundary2,masses]
  have hG : physicalNewBoundary 3 b 2 d (residualBanks 3 b 2 d)
      (residualOrder 2 d) = c2NewSeam b d := by
    funext i
    simp [physicalNewBoundary,residualBanks,residualOrder,c2NewSeam,boundary2,masses,fresh]
  have lower (row : Fin 4) : 0 ≤ c2OldSeam b d row.succ := by
    have h := ((c2_doubled_gates (d-3) (b-d-1) (by omega)).1 row).1
    rw [← (c2_boundary_transport b d hd hbd row.succ).1] at h
    omega
  have upper (row : Fin 4) :
      c2NewSeam b d row.castSucc+
        physicalNewMass 3 b 2 d (residualBanks 3 b 2 d) row ≤ sourceMod 3 b 2 d := by
    have h := ((c2_doubled_gates (d-3) (b-d-1) (by omega)).1 row).2
    rw [← (c2_boundary_transport b d hd hbd row.castSucc).2,
      ← (c2_bank_masses b d hd hbd row).2,
      ← (c2_parameters b d hd hbd).1] at h
    simpa [residualBanks,(masses row).2] using
      (show c2NewSeam b d row.castSucc+
        newMass 3 b 2 d (physicalBank 3 b 2 d (c2Banks (d-3) (b-d-1)) row) ≤
        sourceMod 3 b 2 d by omega)
  have finals := (c2_doubled_gates (d-3) (b-d-1) (by omega)).2
  have ho4 := (c2_boundary_transport b d hd hbd 4).1
  have hn4 := (c2_boundary_transport b d hd hbd 4).2
  have H4 : c2OldSeam b d 4 = 0 := by omega
  have G4 : c2NewSeam b d 4 = 0 := by omega
  have hp := c2_word_perm b d hd hbd
  have totals := source_totals 3 b 2 d (by omega) (by omega) (by omega) (by omega)
  have oldzero : ((c2Word b d).map (oldValue 3 b 2 d)).sum = 0 :=
    (hp.map (oldValue 3 b 2 d)).sum_eq.trans totals.1
  have matched : ((c2Word b d).map (newValue 3 b 2 d)).sum = -base 3 b 2 d 0 :=
    (hp.map (newValue 3 b 2 d)).sum_eq.trans totals.2.1
  have ear : physicalEarWord 3 b 2 d = size 3 b 2 d :: c2Word b d := by
    simp [physicalEarWord,cut0,earSlot0,insertAt,c2Word,residualBanks,residualOrder]
  change cut0 = 0 ∧
    physicalEarWord 3 b 2 d = size 3 b 2 d ::
      physicalWord 3 b 2 d (residualBanks 3 b 2 d) (residualOrder 2 d) ∧ _
  refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,fresh,?_⟩
  · simpa [c2Word,residualBanks,residualOrder] using ear
  · rw [hH]
    rfl
  · rw [hG]
    rfl
  · rw [hH]
    exact H4
  · rw [hG]
    exact G4
  · intro row
    rw [hH]
    exact lower row
  · intro row
    rw [hG]
    exact upper row
  · simpa [c2Word,residualBanks,residualOrder] using oldzero
  · simpa [c2Word,residualBanks,residualOrder] using matched
  · rw [ear,List.map_cons,List.sum_cons,fresh,matched]
    ring

/-- Preserved exact c2 endpoint, now consuming the shared physical
    remaining-charge/certificate/order/period completion.  -/
theorem actualSource_c2_residual_joint_lift (b d : ℕ) (hd : 4 ≤ d) (hbd : d < b) :
    ∃ sigma : List (Fin (3+b+2+d)),
      sigma.map Fin.val =
        physicalWord 3 b 2 d (residualBanks 3 b 2 d) (residualOrder 2 d) ∧
      OriginalOrder (3+b+2+d) (1+2^3+2^(3+b)+2^(3+b+2)) sigma ∧
      OriginalOrder (3+b+2+d+1) (2*(1+2^3+2^(3+b)+2^(3+b+2)))
        (earWord (3+b+2+d) sigma cut0) ∧
      ((sigma.map Fin.castSucc).map
        (actualSource (3+b+2+d+1) (2*(1+2^3+2^(3+b)+2^(3+b+2))))).sum =
        -(1+2^3+2^(3+b)+2^(3+b+2) : ℤ) ∧
      actualSource (3+b+2+d+1) (2*(1+2^3+2^(3+b)+2^(3+b+2)))
        (Fin.last (3+b+2+d)) = (1+2^3+2^(3+b)+2^(3+b+2) : ℤ) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (3+b+2+d) (1+2^3+2^(3+b)+2^(3+b+2)))).sum ∈
          Set.Icc (0 : ℤ) (modulus (3+b+2+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (3+b+2+d) sigma cut0)).flatten).take n).map
        (actualSource (3+b+2+d+1) (2*(1+2^3+2^(3+b)+2^(3+b+2))))).sum ∈
          Set.Icc (0 : ℤ) (modulus (3+b+2+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (3+b+2+d) (1+2^3+2^(3+b)+2^(3+b+2)))).sum = 0 ∧
        (((List.replicate m (earWord (3+b+2+d) sigma cut0)).flatten).map
          (actualSource (3+b+2+d+1) (2*(1+2^3+2^(3+b)+2^(3+b+2))))).sum = 0) := by
  exact residual_joint_lift_of_physical_gates 3 b 2 d
    (c2_domain b d hd hbd) (c2_physical_gates b d hd hbd)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
