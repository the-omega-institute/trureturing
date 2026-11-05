/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/Completion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/Completion
   mirror-E: none(waiver:physical-dependent-source-registration)
   anchors: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Source]
   utility: none
   digest: Native charge completes original certificates, orders and all natural repetitions. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C3DiagonalPhysicalGates
import D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

/-! Native charge completes original certificates, orders and all natural repetitions. Original source owners supply the reused proofs. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
open PacketNormalForm SourceWidth PeriodicShortening RunFirstEarTransport
open private seed sourceMod actual_values chain_values source_signs from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private DataCertificate DataCertificate.mk DataCertificate.positiveLabels DataCertificate.negativeOrder DataCertificate.oldEndpoints DataCertificate.newEndpoints finiteChecks finiteEarChecks finiteChecks_equiv from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private strip_iff_packetChecks from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private zero_period_transport from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakMiddleGap.Endpoint
open private label lift_order marked_word from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private sum_linear from D5.S3.Combinatorics.Circle.PeriodicShortening
open scoped BigOperators

private theorem residual_bounds (a b c d : ℕ) (hdom : OriginalDomain a b c d) :
    2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c ∧ 2 ≤ d := by
  obtain ⟨hb,hshape⟩ := hdom
  rcases hshape with h | h | h <;> omega

private noncomputable def residualPackets (a b c d : ℕ) : List (Finset ℕ × ℕ) :=
  physicalPackets a b c d (residualBanks a b c d) (residualOrder c d)

private noncomputable def residualWord (a b c d : ℕ) : List ℕ :=
  physicalWord a b c d (residualBanks a b c d) (residualOrder c d)

private noncomputable def residualH (a b c d : ℕ) : Fin 5 → ℤ :=
  physicalOldBoundary a b c d (residualBanks a b c d) (residualOrder c d)

private noncomputable def residualG (a b c d : ℕ) : Fin 5 → ℤ :=
  physicalNewBoundary a b c d (residualBanks a b c d) (residualOrder c d)

private theorem residual_word_perm (a b c d : ℕ) (hdom : OriginalDomain a b c d) :
    (residualWord a b c d).Perm (List.range (size a b c d)) := by
  exact Multiset.coe_eq_coe.mp (original_physical_partition a b c d hdom)

private theorem residual_seed_cast (a b c d : ℕ) :
    (seed a b c : ℤ) = base a b c d 0 := by
  simp only [seed, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  dsimp [base]
  ring

/-- This bridge identifies actual physical sums with the ORIGINAL certificate
    masses; it does not substitute scalar masses at a new phase. -/
private theorem residual_mass_ids (a b c d : ℕ) (hdom : OriginalDomain a b c d)
    (row : Fin 4) :
    physicalOldMass a b c d (residualBanks a b c d) row =
      oldMass a b c d (physicalBank a b c d (residualBanks a b c d) row) ∧
    physicalNewMass a b c d (residualBanks a b c d) row =
      newMass a b c d (physicalBank a b c d (residualBanks a b c d) row) := by
  obtain ⟨ha,hb,hc,hd⟩ := residual_bounds a b c d hdom
  exact packet_masses a b c d ha hb hc hd _
    (physical_labels a b c d ha hb hc hd _ (residual_inventory a b c d hdom) row)

/-- For every original cone, the native digit theorem's half-seed premise is
    proved from the original chain values. The phase shift then keeps the
    doubled seed at the SAME physical index i, including terminal phases. -/
private theorem residual_native_data (a b c d : ℕ) (hdom : OriginalDomain a b c d) :
    seed a b c ≤ 2^(size a b c d-1)-1 ∧
    ∀ i : Fin (size a b c d),
      0 ≤ PeriodicShorteningArithmetic.charge (size a b c d) (seed a b c) i ∧
      2*oldValue a b c d i.val-newValue a b c d i.val =
        PeriodicShorteningArithmetic.charge (size a b c d) (seed a b c) i := by
  obtain ⟨ha,hb,hc,hd⟩ := residual_bounds a b c d hdom
  have values := (chain_values a b c d ha hb hc hd).1
  have hA := values 0
  have hB := values 1
  have hdPow : (4 : ℤ) ≤ 2^d := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hd
    norm_num at hh
    exact hh
  have hcycle : (2 : ℤ)^d * base a b c d 0 =
      sourceMod a b c d + base a b c d 1 := by
    dsimp [base,sourceMod]
    ring
  have hmul : 4*base a b c d 0 ≤ (2 : ℤ)^d * base a b c d 0 :=
    mul_le_mul_of_nonneg_right hdPow (by omega)
  have hsmall : 2*base a b c d 0 < sourceMod a b c d := by
    nlinarith only [hB.2,hcycle,hmul]
  have hmod : sourceMod a b c d = (2 : ℤ)^(size a b c d)-1 := by
    simp only [sourceMod,size,pow_add]
  have hpow : (2 : ℤ)^(size a b c d) =
      2*(2 : ℤ)^(size a b c d-1) := by
    conv_lhs => rw [show size a b c d = (size a b c d-1)+1 by dsimp [size]; omega,
      pow_succ]
    ring
  have hseed : (seed a b c : ℤ) < (2 : ℤ)^(size a b c d-1) := by
    rw [hmod,hpow] at hsmall
    rw [residual_seed_cast a b c d]
    omega
  have hnat : seed a b c < (2 : ℕ)^(size a b c d-1) := by exact_mod_cast hseed
  have hw : seed a b c ≤ 2^(size a b c d-1)-1 := by omega
  refine ⟨hw,?_⟩
  intro i
  have digit := PeriodicShorteningArithmetic.digit_data (size a b c d) (seed a b c)
    (by dsimp [size]; omega) hw i
  have phase : actualSource (size a b c d+1) (2*seed a b c) i.castSucc =
      actualSource (size a b c d+1) (seed a b c)
        ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩ := by
    dsimp [actualSource]
    push_cast
    rw [pow_succ]
    congr 1 <;> ring
  have he := phase.trans digit.2.2
  rw [(actual_values a b c d).2 i.castSucc,
    (actual_values a b c d).1 i] at he
  simp only [Fin.val_castSucc] at he
  exact ⟨digit.1,by omega⟩

/-- The original physical permutation has total charge A, by charge_sum. -/
private theorem residual_word_charge (a b c d : ℕ) (hdom : OriginalDomain a b c d) :
    ((residualWord a b c d).map (fun i => 2*oldValue a b c d i-newValue a b c d i)).sum =
      base a b c d 0 := by
  obtain ⟨ha,hb,hc,hd⟩ := residual_bounds a b c d hdom
  have data := residual_native_data a b c d hdom
  have hp := residual_word_perm a b c d hdom
  let chi : ℕ → ℤ := fun i => 2*oldValue a b c d i-newValue a b c d i
  change ((residualWord a b c d).map chi).sum = _
  rw [(hp.map chi).sum_eq]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  calc
    _ = ∑ i : Fin (size a b c d), chi i.val :=
      (Fin.sum_univ_eq_sum_range chi (size a b c d)).symm
    _ = ∑ i : Fin (size a b c d),
        PeriodicShorteningArithmetic.charge (size a b c d) (seed a b c) i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (data.2 i).2
    _ = (seed a b c : ℤ) := PeriodicShorteningArithmetic.charge_sum
      (size a b c d) (seed a b c) (by dsimp [size]; omega) data.1
    _ = base a b c d 0 := residual_seed_cast a b c d

/-- Charge is summed over the actual banks and terminals.  The total comes
    from native charge_sum, rather than a separate polynomial charge proof. -/
private theorem residual_row_charges (a b c d : ℕ) (hdom : OriginalDomain a b c d) :
    let m := fun r => physicalOldMass a b c d (residualBanks a b c d) r
    let m' := fun r => physicalNewMass a b c d (residualBanks a b c d) r
    let f := fun r => oldValue a b c d (terminalLabel a b c d (residualOrder c d r))
    let g := fun r => newValue a b c d (terminalLabel a b c d (residualOrder c d r))
    (∀ r : Fin 4, 0 ≤ 2*m r-m' r ∧ 0 ≤ 2*f r-g r) ∧
    (∑ r : Fin 4, ((2*m r-m' r)+(2*f r-g r))) = base a b c d 0 := by
  obtain ⟨ha,hb,hc,hd⟩ := residual_bounds a b c d hdom
  classical
  dsimp only
  let B := physicalBank a b c d (residualBanks a b c d)
  let f := oldValue a b c d
  let g := newValue a b c d
  let t := fun r => terminalLabel a b c d (residualOrder c d r)
  let chi := fun i => 2*f i-g i
  have inv := residual_inventory a b c d hdom
  have data := residual_native_data a b c d hdom
  have bank_charge (r : Fin 4) :
      ((B r).toList.map chi).sum = 2*physicalOldMass a b c d (residualBanks a b c d) r-physicalNewMass a b c d (residualBanks a b c d) r := by
    have ho : ((B r).toList.map f).sum = physicalOldMass a b c d (residualBanks a b c d) r := by
      calc
        _ = ∑ i ∈ B r, f i := by
          simpa using (List.sum_toFinset f (B r).nodup_toList).symm
        _ = _ := rfl
    have hn : ((B r).toList.map g).sum = physicalNewMass a b c d (residualBanks a b c d) r := by
      calc
        _ = ∑ i ∈ B r, g i := by
          simpa using (List.sum_toFinset g (B r).nodup_toList).symm
        _ = _ := rfl
    simpa only [chi, sub_eq_add_neg, neg_one_mul, ho, hn] using
      sum_linear (B r).toList f g 2 (-1)
  have nonneg (r : Fin 4) :
      0 ≤ 2*physicalOldMass a b c d (residualBanks a b c d) r-physicalNewMass a b c d (residualBanks a b c d) r ∧
      0 ≤ 2*f (t r)-g (t r) := by
    constructor
    · rw [← bank_charge r]
      apply List.sum_nonneg
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      have hib := (physical_labels a b c d (by omega) (by omega) (by omega)
        (by omega) (residualBanks a b c d) inv r i (Finset.mem_toList.mp hi)).1
      have hc := data.2 ⟨i,hib⟩
      change 0 ≤ 2*oldValue a b c d i-newValue a b c d i
      rw [hc.2]
      exact hc.1
    · have hib : t r < size a b c d := by
        dsimp [t, terminalLabel]
        generalize residualOrder c d r = s
        fin_cases s <;> simp [chainStart,chainLength,size] <;> omega
      have hc := data.2 ⟨t r,hib⟩
      change 0 ≤ 2*oldValue a b c d (t r)-newValue a b c d (t r)
      rw [hc.2]
      exact hc.1
  refine ⟨nonneg,?_⟩
  have total := residual_word_charge a b c d hdom
  change ((residualWord a b c d).map chi).sum = base a b c d 0 at total
  simp only [residualWord, physicalWord, physicalPackets, orderedPackets, blocksWord,
    List.map_cons, List.map_nil, List.map_append, List.sum_append,
    List.sum_cons, List.sum_nil, add_zero] at total
  change ((B 0).toList.map chi).sum + (chi (t 0) +
    (((B 1).toList.map chi).sum + (chi (t 1) +
    (((B 2).toList.map chi).sum + (chi (t 2) +
    (((B 3).toList.map chi).sum + chi (t 3))))))) = _ at total
  rw [bank_charge 0,bank_charge 1,bank_charge 2,bank_charge 3] at total
  simp [Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp only [chi, f, g, t] at total
  linear_combination total

/-- The remaining charge after a seam or a positive bank is a sum of
    charges of the still unused physical labels. -/
private theorem residual_remaining_charge (a b c d : ℕ) (hdom : OriginalDomain a b c d)
    (row : Fin 4) :
    0 ≤ residualG a b c d row.succ-2*residualH a b c d row.succ ∧
    0 ≤ (residualG a b c d row.castSucc+
      physicalNewMass a b c d (residualBanks a b c d) row)-
      2*(residualH a b c d row.castSucc+
      physicalOldMass a b c d (residualBanks a b c d) row) := by
  obtain ⟨ha,hb,hc,hd⟩ := residual_bounds a b c d hdom
  have fresh := (chain_values a b c d ha hb hc hd).2.2.2
  have charges := residual_row_charges a b c d hdom
  have c0 := charges.1 0
  have c1 := charges.1 1
  have c2 := charges.1 2
  have c3 := charges.1 3
  have total := charges.2
  dsimp only at c0 c1 c2 c3 total
  simp [Fin.sum_univ_succ, Fin.sum_univ_zero] at total
  fin_cases row <;> constructor <;>
    simp [residualH, residualG, physicalOldBoundary, physicalNewBoundary, fresh] <;>
    linarith only [total,c0.1,c0.2,c1.1,c1.2,c2.1,c2.2,c3.1,c3.2]

/-- OLD LOWER and NEW UPPER are actual supplied gates. Remaining native
    charge proves NEW LOWER and OLD UPPER, with integer division by two. -/
private theorem residual_all_endpoint_sides (a b c d : ℕ)
    (hdom : OriginalDomain a b c d) (sides : ActualPhysicalGateSides a b c d)
    (row : Fin 4) :
    0 ≤ residualH a b c d row.succ ∧
    residualH a b c d row.castSucc+
      oldMass a b c d (physicalBank a b c d (residualBanks a b c d) row) ≤
        sourceMod a b c d / 2 ∧
    0 ≤ residualG a b c d row.succ ∧
    residualG a b c d row.castSucc+
      newMass a b c d (physicalBank a b c d (residualBanks a b c d) row) ≤
        sourceMod a b c d := by
  obtain ⟨_,_,_,_,_,_,lower,upper,_,_,_,_⟩ := sides
  have hlo : 0 ≤ residualH a b c d row.succ := lower row
  have hup := upper row
  have rem := residual_remaining_charge a b c d hdom row
  have hm := residual_mass_ids a b c d hdom row
  change physicalNewBoundary a b c d (residualBanks a b c d) (residualOrder c d)
    row.castSucc + physicalNewMass a b c d (residualBanks a b c d) row ≤
      sourceMod a b c d at hup
  change residualG a b c d row.castSucc +
    physicalNewMass a b c d (residualBanks a b c d) row ≤ sourceMod a b c d at hup
  rw [hm.1,hm.2] at rem
  rw [hm.2] at hup
  exact ⟨hlo,by omega,by omega,hup⟩

private theorem residual_complete_checks (a b c d : ℕ) (hdom : OriginalDomain a b c d) (sides : ActualPhysicalGateSides a b c d) :
    finiteChecks (oldMass a b c d) (oldValue a b c d) (sourceMod a b c d / 2)
      0 (residualPackets a b c d) ∧
    finiteChecks (newMass a b c d) (newValue a b c d) (sourceMod a b c d)
      (base a b c d 0) (residualPackets a b c d) := by
  obtain ⟨ha,hb,hc,hd⟩ := residual_bounds a b c d hdom
  have hm := residual_mass_ids a b c d hdom
  have fresh := (chain_values a b c d ha hb hc hd).2.2.2
  have s0 := residual_all_endpoint_sides a b c d hdom sides 0
  have s1 := residual_all_endpoint_sides a b c d hdom sides 1
  have s2 := residual_all_endpoint_sides a b c d hdom sides 2
  have s3 := residual_all_endpoint_sides a b c d hdom sides 3
  constructor
  · simpa [residualPackets,physicalPackets,finiteChecks,residualH,physicalOldBoundary,hm,add_assoc,and_assoc] using
      (show (0 ≤ residualH a b c d (0 : Fin 4).succ ∧
        residualH a b c d (0 : Fin 4).castSucc+
          oldMass a b c d (physicalBank a b c d (residualBanks a b c d) 0) ≤ sourceMod a b c d/2) ∧
        (0 ≤ residualH a b c d (1 : Fin 4).succ ∧
        residualH a b c d (1 : Fin 4).castSucc+
          oldMass a b c d (physicalBank a b c d (residualBanks a b c d) 1) ≤ sourceMod a b c d/2) ∧
        (0 ≤ residualH a b c d (2 : Fin 4).succ ∧
        residualH a b c d (2 : Fin 4).castSucc+
          oldMass a b c d (physicalBank a b c d (residualBanks a b c d) 2) ≤ sourceMod a b c d/2) ∧
        (0 ≤ residualH a b c d (3 : Fin 4).succ ∧
        residualH a b c d (3 : Fin 4).castSucc+
          oldMass a b c d (physicalBank a b c d (residualBanks a b c d) 3) ≤ sourceMod a b c d/2)
        from ⟨⟨s0.1,s0.2.1⟩,⟨s1.1,s1.2.1⟩,⟨s2.1,s2.2.1⟩,⟨s3.1,s3.2.1⟩⟩)
  · simpa [residualPackets,physicalPackets,finiteChecks,residualG,physicalNewBoundary,fresh,hm,add_assoc,and_assoc] using
      (show (0 ≤ residualG a b c d (0 : Fin 4).succ ∧
        residualG a b c d (0 : Fin 4).castSucc+
          newMass a b c d (physicalBank a b c d (residualBanks a b c d) 0) ≤ sourceMod a b c d) ∧
        (0 ≤ residualG a b c d (1 : Fin 4).succ ∧
        residualG a b c d (1 : Fin 4).castSucc+
          newMass a b c d (physicalBank a b c d (residualBanks a b c d) 1) ≤ sourceMod a b c d) ∧
        (0 ≤ residualG a b c d (2 : Fin 4).succ ∧
        residualG a b c d (2 : Fin 4).castSucc+
          newMass a b c d (physicalBank a b c d (residualBanks a b c d) 2) ≤ sourceMod a b c d) ∧
        (0 ≤ residualG a b c d (3 : Fin 4).succ ∧
        residualG a b c d (3 : Fin 4).castSucc+
          newMass a b c d (physicalBank a b c d (residualBanks a b c d) 3) ≤ sourceMod a b c d)
        from ⟨⟨s0.2.2.1,s0.2.2.2⟩,⟨s1.2.2.1,s1.2.2.2⟩,
          ⟨s2.2.2.1,s2.2.2.2⟩,⟨s3.2.2.1,s3.2.2.2⟩⟩)

/-- This is the ORIGINAL certificate, including every finiteChecks and
    finiteEarChecks field and the literal earSlot0. -/
private noncomputable def residual_certificate (a b c d : ℕ) (hdom : OriginalDomain a b c d) (sides : ActualPhysicalGateSides a b c d) :
    Certificate a b c d := by
  obtain ⟨ha,hb,hc,hd⟩ := residual_bounds a b c d hdom
  classical
  have inv := residual_inventory a b c d hdom
  have checks := residual_complete_checks a b c d hdom sides
  refine DataCertificate.mk (residualPackets a b c d) ?_ earSlot0 ?_ ?_ checks.1 ?_
  · exact physical_negative_order a b c d (residualBanks a b c d) (residualOrder c d)
      (residual_order_perm c d)
  · intro p hp i hi
    simp only [residualPackets,physicalPackets,List.mem_cons,List.mem_singleton,
      List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact physical_labels a b c d (by omega) (by omega) (by omega) (by omega)
        (residualBanks a b c d) inv _ i hi
  · change (residualWord a b c d : Multiset ℕ) = _
    exact Multiset.coe_eq_coe.mpr (residual_word_perm a b c d hdom)
  · simpa [residualPackets,physicalPackets,finiteEarChecks,finiteChecks,earSlot0,
      add_assoc,add_left_comm,add_comm] using checks.2

/-- The certificate is consumed through the original packet equivalences.
    Starting the new row at A permits the fresh label to be prepended at
    cut0, without changing the physical old word. -/
private theorem residual_physical_strips (a b c d : ℕ) (hdom : OriginalDomain a b c d) (sides : ActualPhysicalGateSides a b c d) :
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (residualWord a b c d) ∧
    InStrip (newValue a b c d) (sourceMod a b c d) 0
      (size a b c d :: residualWord a b c d) := by
  obtain ⟨ha,hb,hc,hd⟩ := residual_bounds a b c d hdom
  classical
  let cert := residual_certificate a b c d hdom sides
  let bs := orderedPackets (residualPackets a b c d)
  have hlabels := (DataCertificate.positiveLabels cert)
  change ∀ p ∈ residualPackets a b c d, ∀ i ∈ p.1,
    i < size a b c d ∧ i ∉ negatives a b c d at hlabels
  have horder := (DataCertificate.negativeOrder cert)
  change ((residualPackets a b c d).map Prod.snd).Perm (negatives a b c d) at horder
  have hm (p : Finset ℕ × ℕ) (hp : p ∈ residualPackets a b c d) :
      oldMass a b c d p.1 = ∑ i ∈ p.1, oldValue a b c d i ∧
      newMass a b c d p.1 = ∑ i ∈ p.1, newValue a b c d i := by
    have h := packet_masses a b c d (by omega) (by omega) (by omega) (by omega)
      p.1 (hlabels p hp)
    exact ⟨h.1.symm,h.2.symm⟩
  have hpos : ∀ p ∈ bs, ∀ i ∈ p.1,
      0 ≤ oldValue a b c d i ∧ 0 ≤ newValue a b c d i := by
    intro p hp i hi
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have lab := hlabels q hq i (Finset.mem_toList.mp hi)
    have hs := source_signs a b c d (by omega) (by omega) (by omega) (by omega) i lab.1
    rw [if_neg lab.2] at hs
    exact ⟨hs.1.le,hs.2.le⟩
  have hneg : ∀ p ∈ bs,
      oldValue a b c d p.2 ≤ 0 ∧ newValue a b c d p.2 ≤ 0 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have hn : q.2 ∈ negatives a b c d :=
      horder.mem_iff.mp (List.mem_map.mpr ⟨q,hq,rfl⟩)
    have hib : q.2 < size a b c d := by
      simp only [negatives,size,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hn ⊢
      omega
    have hs := source_signs a b c d (by omega) (by omega) (by omega) (by omega) q.2 hib
    rw [if_pos hn] at hs
    exact ⟨hs.1.le,hs.2.le⟩
  have tab := (chain_values a b c d (by omega) (by omega) (by omega) (by omega)).1 0
  have hN : 0 ≤ sourceMod a b c d := by omega
  have hA : 0 ≤ base a b c d 0 ∧ base a b c d 0 ≤ sourceMod a b c d := by omega
  have oldchecks := (DataCertificate.oldEndpoints cert)
  change finiteChecks (oldMass a b c d) (oldValue a b c d) (sourceMod a b c d/2)
    0 (residualPackets a b c d) at oldchecks
  have newchecks := (DataCertificate.newEndpoints cert)
  change finiteEarChecks (newMass a b c d) (newValue a b c d) (sourceMod a b c d)
    (base a b c d 0) 0 earSlot0.val (residualPackets a b c d) at newchecks
  have shiftedchecks : finiteChecks (newMass a b c d) (newValue a b c d)
      (sourceMod a b c d) (base a b c d 0) (residualPackets a b c d) := by
    simpa [residualPackets,physicalPackets,finiteEarChecks,finiteChecks,earSlot0,
      add_assoc,add_left_comm,add_comm] using newchecks
  have oldstrip : InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (residualWord a b c d) := by
    apply (strip_iff_packetChecks (oldValue a b c d) (sourceMod a b c d/2) 0 bs
      ⟨by omega,by omega⟩ (fun p hp i hi => (hpos p hp i hi).1)
      (fun p hp => (hneg p hp).1)).mpr
    exact (finiteChecks_equiv (oldMass a b c d) (oldValue a b c d)
      (sourceMod a b c d/2) 0 (residualPackets a b c d) (fun p hp => (hm p hp).1)).mp oldchecks
  have shifted : InStrip (newValue a b c d) (sourceMod a b c d)
      (base a b c d 0) (residualWord a b c d) := by
    apply (strip_iff_packetChecks (newValue a b c d) (sourceMod a b c d)
      (base a b c d 0) bs hA (fun p hp i hi => (hpos p hp i hi).2)
      (fun p hp => (hneg p hp).2)).mpr
    exact (finiteChecks_equiv (newMass a b c d) (newValue a b c d)
      (sourceMod a b c d) (base a b c d 0) (residualPackets a b c d)
      (fun p hp => (hm p hp).2)).mp shiftedchecks
  refine ⟨oldstrip,?_⟩
  change 0 ≤ (0 : ℤ) ∧ 0 ≤ sourceMod a b c d ∧
    InStrip (newValue a b c d) (sourceMod a b c d)
      (0+newValue a b c d (size a b c d)) (residualWord a b c d)
  exact ⟨by omega,hN,by simpa only [zero_add,(chain_values a b c d ha hb hc hd).2.2.2] using shifted⟩

/-- The original lift and marked-word bridges retain the actual physical
    word, rather than merely extracting an unspecified certificate witness. -/
private theorem residual_original_orders (a b c d : ℕ) (hdom : OriginalDomain a b c d) (sides : ActualPhysicalGateSides a b c d) :
    ∃ sigma : List (Fin (size a b c d)),
      sigma.map Fin.val = residualWord a b c d ∧
      OriginalOrder (size a b c d) (seed a b c) sigma ∧
      OriginalOrder (size a b c d+1) (2*seed a b c)
        (earWord (size a b c d) sigma cut0) ∧
      ((sigma.map Fin.castSucc).map
        (actualSource (size a b c d+1) (2*seed a b c))).sum = -base a b c d 0 ∧
      actualSource (size a b c d+1) (2*seed a b c)
        (Fin.last (size a b c d)) = base a b c d 0 := by
  obtain ⟨ha,hb,hc,hd⟩ := residual_bounds a b c d hdom
  classical
  let k := size a b c d
  let A := seed a b c
  let l := residualWord a b c d
  have hk : 0 < k := by dsimp [k,size]; omega
  have hp : l.Perm (List.range k) := residual_word_perm a b c d hdom
  have strips := residual_physical_strips a b c d hdom sides
  obtain ⟨_,_,_,_,_,_,_,_,physical_oldzero,physical_matched,physical_fresh,
    physical_newzero⟩ := sides
  have hcast : (A : ℤ) = base a b c d 0 := residual_seed_cast a b c d
  have hmod : modulus k = sourceMod a b c d := by
    simp only [k,size,modulus,sourceMod,pow_add]
  have hmod' : modulus (k+1) = 2*sourceMod a b c d+1 := by
    rw [modulus,pow_succ]
    have he : (2 : ℤ)^k = sourceMod a b c d+1 := by
      have h := hmod
      change (2 : ℤ)^k-1 = sourceMod a b c d at h
      omega
    rw [he]
    ring
  have hhalf : modulus (k+1)/2 = sourceMod a b c d := by rw [hmod']; omega
  have oldfun : (fun i => centered (modulus k) ((2 : ℤ)^i*A)) =
      oldValue a b c d := by
    funext i
    rw [hmod,hcast]
    rfl
  have newfun : (fun i => centered (modulus (k+1)) ((2 : ℤ)^i*(2*A : ℕ))) =
      newValue a b c d := by
    funext i
    rw [hmod']
    push_cast
    rw [hcast]
    rfl
  have oldstrip : InStrip (fun i => centered (modulus k) ((2 : ℤ)^i*A))
      (modulus k/2) 0 l := by
    rw [oldfun,hmod]
    exact strips.1
  have newstrip : InStrip (fun i => centered (modulus (k+1)) ((2 : ℤ)^i*(2*A : ℕ)))
      (modulus (k+1)/2) 0 (k::l) := by
    rw [hhalf]
    rw [newfun]
    exact strips.2
  have oldzero : ((List.range k).map
      (fun i => centered (modulus k) ((2 : ℤ)^i*A))).sum = 0 := by
    have hz := physical_oldzero
    change (l.map (oldValue a b c d)).sum = 0 at hz
    rw [(hp.map (oldValue a b c d)).sum_eq] at hz
    rw [oldfun]
    exact hz
  have newzero : ((List.range (k+1)).map
      (fun i => centered (modulus (k+1)) ((2 : ℤ)^i*(2*A : ℕ)))).sum = 0 := by
    have hpEar : (physicalEarWord a b c d).Perm (List.range (k+1)) :=
      Multiset.coe_eq_coe.mp (original_ear_partition a b c d hdom)
    have hz := physical_newzero
    rw [(hpEar.map (newValue a b c d)).sum_eq] at hz
    rw [newfun]
    exact hz
  let sigma := l.map (label k hk)
  have ho : OriginalOrder k A sigma :=
    lift_order k A hk l hp oldstrip oldzero
  have hpnew : (k::l).Perm (List.range (k+1)) :=
    (List.perm_append_singleton k l).symm.trans
      (by simpa only [List.range_succ] using hp.append_right [k])
  have hn : OriginalOrder (k+1) (2*A) (earWord k sigma cut0) := by
    have marked : earWord k sigma cut0 =
        (k::l).map (label (k+1) (by omega)) := by
      simpa only [sigma,List.nil_append] using
        marked_word k cut0 hk [] l (by rfl)
          (by simpa only [List.nil_append] using hp)
    rw [marked]
    exact lift_order (k+1) (2*A) (by omega)
      (k::l) hpnew newstrip newzero
  have labelval (i : ℕ) (hi : i ∈ l) :
      (label k hk i).val = i := by
    exact Nat.mod_eq_of_lt (List.mem_range.mp (hp.mem_iff.mp hi))
  have hval : sigma.map Fin.val = l := by
    calc
      (l.map (label k hk)).map Fin.val = l.map id := by
        rw [List.map_map]
        exact List.map_congr_left labelval
      _ = l := by simp
  have matched : ((sigma.map Fin.castSucc).map (actualSource (k+1) (2*A))).sum =
      -base a b c d 0 := by
    have he : (sigma.map Fin.castSucc).map (actualSource (k+1) (2*A)) =
        l.map (newValue a b c d) := by
      simp only [sigma,List.map_map]
      apply List.map_congr_left
      intro i hi
      change actualSource (k+1) (2*A)
        (label k hk i).castSucc = newValue a b c d i
      rw [(actual_values a b c d).2]
      change newValue a b c d (label k hk i).val = _
      rw [labelval i hi]
    rw [he]
    exact physical_matched
  have fresh : actualSource (k+1) (2*A) (Fin.last k) = base a b c d 0 :=
    ((actual_values a b c d).2 (Fin.last k)).trans physical_fresh
  exact ⟨sigma,hval,ho,hn,matched,fresh⟩

/-- Shared substantive completion, consumed by the C2 endpoint and the
    full-domain Endpoint. Every assumption about physical sides is discharged
    by those consumers before the final public result.  -/
theorem residual_joint_lift_of_physical_gates (a b c d : ℕ) (hdom : OriginalDomain a b c d) (sides : ActualPhysicalGateSides a b c d) :
    ∃ sigma : List (Fin (a+b+c+d)),
      sigma.map Fin.val =
        physicalWord a b c d (residualBanks a b c d) (residualOrder c d) ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma cut0) ∧
      ((sigma.map Fin.castSucc).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum =
        -(1+2^a+2^(a+b)+2^(a+b+c) : ℤ) ∧
      actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (Fin.last (a+b+c+d)) = (1+2^a+2^(a+b)+2^(a+b+c) : ℤ) ∧
      (∀ m n : ℕ, ((((List.replicate m sigma).flatten).take n).map
        (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum ∈
          Set.Icc (0 : ℤ) (modulus (a+b+c+d)/2)) ∧
      (∀ m n : ℕ, ((((List.replicate m (earWord (a+b+c+d) sigma cut0)).flatten).take n).map
        (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum ∈
          Set.Icc (0 : ℤ) (modulus (a+b+c+d))) ∧
      (∀ m : ℕ,
        (((List.replicate m sigma).flatten).map
          (actualSource (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)))).sum = 0 ∧
        (((List.replicate m (earWord (a+b+c+d) sigma cut0)).flatten).map
          (actualSource (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c))))).sum = 0) := by
  obtain ⟨ha,hb,hc,hd⟩ := residual_bounds a b c d hdom
  obtain ⟨sigma,hword,ho,hn,hmatched,hfresh⟩ := residual_original_orders a b c d hdom sides
  have eo (m : ℕ) := zero_period_transport _ _ sigma ho.2.1 ho.2.2 m
  have en (m : ℕ) := zero_period_transport _ _
    (earWord (size a b c d) sigma cut0) hn.2.1 hn.2.2 m
  have half : modulus (size a b c d+1)/2 = modulus (size a b c d) := by
    have hp : (2 : ℤ)^(size a b c d+1) = 2*(2 : ℤ)^(size a b c d) := by
      rw [pow_succ]
      ring
    dsimp [modulus]
    rw [hp]
    omega
  refine ⟨sigma,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hword
  · simpa only [size,seed] using ho
  · simpa only [size,seed] using hn
  · rw [← residual_seed_cast a b c d] at hmatched
    simpa only [size,seed,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using hmatched
  · rw [← residual_seed_cast a b c d] at hfresh
    simpa only [size,seed,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using hfresh
  · intro m n
    simpa only [size,seed] using (eo m).2 n
  · intro m n
    have h := (en m).2 n
    rw [half] at h
    simpa only [size,seed] using h
  · intro m
    simpa only [size,seed] using And.intro (eo m).1 (en m).1

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
