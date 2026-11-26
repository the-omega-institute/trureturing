/- GID: D5/S1/Words/Complexity/CassaigneIndexTransport
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/CassaigneIndexTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Period synchronization preserves the golden asymptotic index. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26320
admission_basis: escape-witness
escape_witness: golden_indStar_replicated
hasPeriod_iff_list: proof_shape: bind-only; escape_witness: none; consumers: hasPeriod_block_iff, per_is_period.
hasPeriod_block_iff: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.period_decode, _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.period_aligned_or_short_overlap, _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.golden_period_length_bound, _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.period_lift, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.golden_indexAt_le_sharp, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.golden_indStar_ge_sharp.
period_decode: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.replicated_period_length_bound, _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_real_exponent_transport.
decode_length_loss: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.replicated_period_length_bound, _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_real_exponent_transport.
transition_in_replicated_window: proof_shape: content; escape_witness: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.transition_in_replicated_window; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.period_aligned_or_short_overlap.
period_aligned_or_short_overlap: proof_shape: content; escape_witness: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.transition_in_replicated_window; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.replicated_period_length_bound, _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_real_exponent_transport.
golden_frequent_transition: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_period_length_bound, _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_real_exponent_transport.
replicated_period_length_bound: proof_shape: content; escape_witness: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.transition_in_replicated_window; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_period_length_bound.
golden_period_length_bound: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_period_length_bound.
vk_period_length_bound: proof_shape: content; escape_witness: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.transition_in_replicated_window; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_real_exponent_transport.
per_is_period: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.exponent_lift, D5.S1.Words.Complexity.CassaigneIndexTransport.exponent_eq_ofReal, _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.one_le_real_exponent, _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_real_exponent_transport, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.golden_indexAt_le_sharp, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.golden_indStar_ge_sharp.
per_le_of_period: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.exponent_lift, _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.one_le_real_exponent, _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_real_exponent_transport, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.golden_indStar_ge_sharp.
period_lift: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.exponent_lift.
exponent_lift: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.indexAt_le_replicated.
indexAt_le_replicated: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.indStar_le_replicated.
indStar_le_replicated: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Words.Complexity.CassaigneIndexTransport.golden_indStar_replicated.
exponent_eq_ofReal: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_exponent_le_tail, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.golden_indexAt_le_sharp, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.golden_indStar_ge_sharp.
block_exponent_le_tail: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_exponent_le_tail, _private.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.0.D5.S1.Words.ReturnWords.GoldenSharpRepetitions.golden_indStar_ge_sharp.
one_le_real_exponent: proof_shape: bind-only; escape_witness: none; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_real_exponent_transport.
vk_real_exponent_transport: proof_shape: content; escape_witness: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.transition_in_replicated_window; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_exponent_le_tail.
vk_exponent_le_tail: proof_shape: content; escape_witness: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.transition_in_replicated_window; consumers: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.vk_indexAt_le_tail.
vk_indexAt_le_tail: proof_shape: content; escape_witness: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.transition_in_replicated_window; consumers: D5.S1.Words.Complexity.CassaigneIndexTransport.golden_indStar_replicated.
indStar_eq_limsup: proof_shape: bind-only; escape_witness: none; consumers: D5.S1.Words.Complexity.CassaigneIndexTransport.golden_indStar_replicated.
golden_indStar_replicated: proof_shape: content; escape_witness: _private.D5.S1.Words.Complexity.CassaigneIndexTransport.0.D5.S1.Words.Complexity.CassaigneIndexTransport.transition_in_replicated_window; consumers: _private.D5.S1.Words.Complexity.CassaigneSturmianCharacterization.0.D5.S1.Words.Complexity.CassaigneSturmianCharacterization.nominated_invariant_values.
-/


import D5.S0.Computability.Coding.BiasedMassFrontier
import D5.S1.Words.Complexity.CassaigneRecurrenceTransport
import D5.S1.Words.GoldenWord
import D5.S1.Words.Powers.GoldenDesubstitution
import D5.S1.Words.Powers.GoldenFourthPower
import Mathlib.Data.List.PeriodicityLemma
set_option maxHeartbeats 1600000

open D5.S0.Computability.Coding.BiasedMassFrontier

namespace D5.S1.Words.Complexity.CassaigneIndexTransport

open Set Filter D5.S1.Words D5.S1.Words.Mechanical D5.S1.Words.Powers
open scoped ENNReal Topology
open D5.S1.Words.Complexity.CassaigneRecurrenceTransport

private theorem hasPeriod_iff_list (w : List Bool) (p : ℕ) :
    HasPeriod w p ↔ 0 < p ∧ List.HasPeriod w p := by
  rw [HasPeriod, List.hasPeriod_iff_getElem?]
  constructor
  · rintro ⟨hp, he⟩
    refine ⟨hp, ?_⟩
    intro i hi
    have hip : i+p < w.length := by omega
    have hi' : i < w.length := by omega
    have hh := he i hip
    simpa [List.getD_eq_getElem, hi', hip] using hh
  · rintro ⟨hp, he⟩
    refine ⟨hp, ?_⟩
    intro i hip
    have hi : i < w.length-p := by omega
    have hi' : i < w.length := by omega
    have hh := he i hi
    simpa [List.getD_eq_getElem, hi', hip] using hh

theorem hasPeriod_block_iff (u : ℕ → Bool) (a L p : ℕ) :
    HasPeriod ((rayPrefix (fun index => u (a + index)) L)) p ↔
      0 < p ∧ ∀ r, r+p < L → u (a+r) = u (a+(r+p)) := by
  rw [hasPeriod_iff_list, List.hasPeriod_iff_getElem?]
  constructor
  · rintro ⟨hp, he⟩
    refine ⟨hp, ?_⟩
    intro r hr
    have hr0 : r < L := by omega
    have hh := he r (by simpa only [rayPrefix, List.length_ofFn] using (show r < L-p by omega))
    simpa only [rayPrefix, List.getElem?_ofFn, hr0, hr, ↓reduceDIte,
      Option.some.injEq] using hh
  · rintro ⟨hp, he⟩
    refine ⟨hp, ?_⟩
    intro r hr
    have hr' : r+p < L := by
      simp only [rayPrefix, List.length_ofFn] at hr
      omega
    have hr0 : r < L := by omega
    simpa only [rayPrefix, List.getElem?_ofFn, hr0, hr', ↓reduceDIte,
      Option.some.injEq] using he r hr'

private theorem period_decode (k : ℕ) (hk : 0 < k) (u : ℕ → Bool)
    (a L q : ℕ) (hq : 0 < q)
    (hp : HasPeriod ((rayPrefix (fun index => (replicated k u) (a + index)) L)) (k*q)) :
    HasPeriod ((rayPrefix (fun index => u ((a/k+1) + index)) ((a+L)/k-(a/k+1)))) q := by
  rw [hasPeriod_block_iff] at hp ⊢
  refine ⟨hq,?_⟩
  intro r hr
  let A := a/k+1
  have hstart : a ≤ k*A := by
    have hd := Nat.div_add_mod a k
    have hm := Nat.mod_lt a hk
    dsimp [A]
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have hend : k*(A+(r+q)) < a+L := by
    have hr0 : A+(r+q) < (a+L)/k := Nat.add_lt_of_lt_sub' hr
    have hm := Nat.mul_lt_mul_of_pos_left hr0 hk
    exact lt_of_lt_of_le hm (by simpa [Nat.mul_comm] using Nat.div_mul_le_self (a+L) k)
  have he := hp.2 (k*(A+r)-a) (by
    have hh : k*(A+r) = k*A+k*r := Nat.mul_add _ _ _
    have hh2 : k*(A+(r+q)) = k*(A+r)+k*q := by simp [Nat.mul_add,Nat.add_assoc]
    omega)
  change u ((a+(k*(A+r)-a))/k) = u ((a+(k*(A+r)-a+k*q))/k) at he
  have hh0 : a+(k*(A+r)-a) = k*(A+r) := by
    have hm : k*A ≤ k*(A+r) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hh1 : a+(k*(A+r)-a+k*q) = k*(A+(r+q)) := by
    rw [← Nat.add_assoc,hh0]
    simp [Nat.mul_add,Nat.add_assoc]
  rw [hh0,hh1,Nat.mul_div_right _ hk,Nat.mul_div_right _ hk] at he
  exact he

private theorem decode_length_loss (k : ℕ) (hk : 0 < k) (a L : ℕ) :
    L ≤ k*((a+L)/k-(a/k+1))+2*k := by
  have ha := Nat.div_add_mod a k
  have he := Nat.div_add_mod (a+L) k
  have ham := Nat.mod_lt a hk
  have hem := Nat.mod_lt (a+L) hk
  by_cases h : a/k+1 ≤ (a+L)/k
  · have hs : (a+L)/k = ((a+L)/k-(a/k+1))+(a/k+1) := (Nat.sub_add_cancel h).symm
    rw [hs,Nat.mul_add,Nat.mul_add,Nat.mul_one] at he
    omega
  · have hd : (a+L)/k ≤ a/k := Nat.le_of_not_lt h
    have hm := Nat.mul_le_mul_left k hd
    have hz : (a+L)/k-(a/k+1)=0 := by omega
    rw [hz,Nat.mul_zero]
    omega

private theorem transition_in_replicated_window (k : ℕ) (hk : 0 < k)
    (u : ℕ → Bool) (B : ℕ)
    (hB : ∀ a, ∃ r < B, u (a+r) ≠ u (a+(r+1))) (a : ℕ) :
    ∃ r, r+1 < k*(B+2) ∧
      replicated k u (a+r) ≠ replicated k u (a+(r+1)) := by
  obtain ⟨r,hr,he⟩ := hB (a/k+1)
  let q := a/k+1+r
  let I := k*q+(k-1)
  have ha : a ≤ I := by
    have hd := Nat.div_add_mod a k
    have hm := Nat.mod_lt a hk
    dsimp [I,q]
    rw [Nat.mul_add,Nat.mul_add,Nat.mul_one]
    omega
  have hnext : I+1 = k*(q+1) := by
    have hmul : k*(q+1) = k*q+k := Nat.mul_succ k q
    rw [hmul]
    dsimp only [I]
    omega
  have he0 : I/k = q := by
    dsimp [I]
    rw [Nat.mul_add_div hk,Nat.div_eq_of_lt (by omega),Nat.add_zero]
  have he1 : (I+1)/k = q+1 := Nat.div_eq_of_eq_mul_right hk hnext
  have hend : I+1 < a+k*(B+2) := by
    have hmul : k*(r+2) < k*(B+2) := Nat.mul_lt_mul_of_pos_left (by omega) hk
    have hbase : k*(a/k) ≤ a := Nat.mul_div_le a k
    rw [hnext]
    have hq : k*(q+1) = k*(a/k)+k*(r+2) := by dsimp [q]; ring
    rw [hq]
    omega
  refine ⟨I-a,by omega,?_⟩
  have hia : a+(I-a) = I := Nat.add_sub_of_le ha
  have hia1 : a+(I-a+1) = I+1 := by omega
  change u ((a+(I-a))/k) ≠ u ((a+(I-a+1))/k)
  rw [hia,hia1,he0,he1]
  exact he

private theorem period_aligned_or_short_overlap (k : ℕ) (hk : 0 < k)
    (u : ℕ → Bool) (B : ℕ)
    (hB : ∀ a, ∃ r < B, u (a+r) ≠ u (a+(r+1))) (a L p : ℕ)
    (hp : HasPeriod ((rayPrefix (fun index => (replicated k u) (a + index)) L)) p) :
    k ∣ p ∨ L ≤ p+k*(B+2) := by
  by_cases hshort : L ≤ p+k*(B+2)
  · exact Or.inr hshort
  left
  obtain ⟨r,hr,he⟩ := transition_in_replicated_window k hk u B hB a
  have hper := (hasPeriod_block_iff _ _ _ _).mp hp
  have he0 := hper.2 r (by omega)
  have he1 := hper.2 (r+1) (by omega)
  have ht : replicated k u (a+(r+p)) ≠ replicated k u (a+(r+1+p)) := by
    rw [← he0,← he1]
    exact he
  have hdiv0 := replicated_transition_aligned k u (a+r) (by simpa [Nat.add_assoc] using he)
  have hdiv1 := replicated_transition_aligned k u (a+(r+p))
    (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht)
  exact (Nat.dvd_add_iff_right hdiv0).mpr
    (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hdiv1)

private theorem golden_frequent_transition :
    ∀ a, ∃ r < 2, D5.S1.Words.goldenWord (a+r) ≠ D5.S1.Words.goldenWord (a+(r+1)) := by
  intro a
  by_cases he : D5.S1.Words.goldenWord a = D5.S1.Words.goldenWord (a+1)
  · have ht : D5.S1.Words.goldenWord a = true := by
      cases hh : D5.S1.Words.goldenWord a
      · have hf : D5.S1.Words.goldenWord (a+1) = false := he.symm.trans hh
        have hb := D5.S1.Words.Powers.golden_no_two_false hh
        simp_all
      · rfl
    have hn : D5.S1.Words.goldenWord (a+1) = true := he.symm.trans ht
    have hnn := D5.S1.Words.Powers.golden_no_three_true ht hn
    refine ⟨1,by omega,?_⟩
    simp [hn,hnn,Nat.add_assoc]
  · exact ⟨0,by omega,by simpa using he⟩

private theorem replicated_period_length_bound (k : ℕ) (hk : 0 < k)
    (u : ℕ → Bool) (B C : ℕ) (hC : 1 ≤ C)
    (hB : ∀ a, ∃ r < B, u (a+r) ≠ u (a+(r+1)))
    (hbound : ∀ a p L, HasPeriod ((rayPrefix (fun index => u (a + index)) L)) p → L ≤ C*p)
    (a L p : ℕ) (hp : HasPeriod ((rayPrefix (fun index => (replicated k u) (a + index)) L)) p) :
    L ≤ C*p+k*(B+2) := by
  rcases period_aligned_or_short_overlap k hk u B hB a L p hp with hd | hs
  · obtain ⟨q,hq⟩ := hd
    have hqpos : 0 < q := by
      have hppos := hp.1
      rw [hq] at hppos
      exact Nat.pos_of_mul_pos_left hppos
    have hdecode := period_decode k hk u a L q hqpos (by simpa [hq] using hp)
    have hsource := hbound (a/k+1) q ((a+L)/k-(a/k+1)) hdecode
    have hmul := Nat.mul_le_mul_left k hsource
    have hloss := decode_length_loss k hk a L
    have hconst : 2*k ≤ k*(B+2) := by
      rw [Nat.mul_add,Nat.mul_two]
      omega
    rw [hq]
    calc
      L ≤ k*((a+L)/k-(a/k+1))+2*k := hloss
      _ ≤ k*(C*q)+k*(B+2) := Nat.add_le_add hmul hconst
      _ = C*(k*q)+k*(B+2) := by ring
  · have hcp : p ≤ C*p := Nat.le_mul_of_pos_left p hC
    omega

private theorem golden_period_length_bound (a p L : ℕ)
    (hp : HasPeriod ((rayPrefix (fun index => D5.S1.Words.goldenWord (a + index)) L)) p) : L ≤ 4*p := by
  have hper := (hasPeriod_block_iff _ _ _ _).mp hp
  by_contra hn
  have hgold : D5.S1.Words.Powers.GoldenPeriodic a p L := by
    intro i hi hip
    have he := hper.2 (i-a) (by omega)
    have hia : a+(i-a) = i := Nat.add_sub_of_le hi
    simpa [← Nat.add_assoc,hia] using he
  exact D5.S1.Words.Powers.golden_no_periodic p hper.1 a L (by omega) hgold

private theorem vk_period_length_bound (k : ℕ) (hk : 0 < k) (a p L : ℕ)
    (hp : HasPeriod ((rayPrefix (fun index => (replicated k D5.S1.Words.goldenWord) (a + index)) L)) p) :
    L ≤ 4*p+4*k := by
  have hh := replicated_period_length_bound k hk _ 2 4 (by omega)
    golden_frequent_transition golden_period_length_bound a L p hp
  simpa [Nat.mul_comm] using hh

theorem per_is_period (w : List Bool) : HasPeriod w (per w) := by
  have hn : {p : ℕ | HasPeriod w p}.Nonempty := by
    exact ⟨w.length+1,
      (hasPeriod_iff_list w _).mpr ⟨Nat.zero_lt_succ _,
        List.hasPeriod_of_length_le w _ (Nat.le_succ _)⟩⟩
  exact Nat.sInf_mem hn

theorem per_le_of_period (w : List Bool) (p : ℕ) (hp : HasPeriod w p) :
    per w ≤ p := Nat.sInf_le hp

private theorem period_lift (k : ℕ) (hk : 0 < k) (u : ℕ → Bool)
    (a n p : ℕ) (hp : HasPeriod ((rayPrefix (fun index => u (a + index)) n)) p) :
    HasPeriod ((rayPrefix (fun index => (replicated k u) ((k*a) + index)) (k*n))) (k*p) := by
  rw [hasPeriod_block_iff] at hp ⊢
  refine ⟨Nat.mul_pos hk hp.1,?_⟩
  intro r hr
  have hr' : r/k+p < n := by
    have hdiv : (r+k*p)/k < n :=
      (Nat.div_lt_iff_lt_mul hk).mpr (by simpa [Nat.mul_comm] using hr)
    simpa only [Nat.add_mul_div_left _ _ hk, Nat.mul_comm k n] using hdiv
  change u ((k*a+r)/k) = u ((k*a+(r+k*p))/k)
  rw [Nat.mul_add_div hk,Nat.mul_add_div hk,Nat.add_mul_div_left _ _ hk]
  exact hp.2 (r/k) hr'

private theorem exponent_lift (k : ℕ) (hk : 0 < k) (u : ℕ → Bool) (a n : ℕ) :
    exponent ((rayPrefix (fun index => u (a + index)) n)) ≤ exponent ((rayPrefix (fun index => (replicated k u) ((k*a) + index)) (k*n))) := by
  have hper := period_lift k hk u a n (per ((rayPrefix (fun index => u (a + index)) n))) (per_is_period _)
  have hle := per_le_of_period _ _ hper
  have hcast : (per ((rayPrefix (fun index => (replicated k u) ((k*a) + index)) (k*n))) : ℝ≥0∞) ≤
      (k : ℝ≥0∞)*(per ((rayPrefix (fun index => u (a + index)) n)) : ℝ≥0∞) := by exact_mod_cast hle
  have hh := ENNReal.div_le_div_left hcast (k*n : ℕ)
  simp only [exponent,rayPrefix,List.length_ofFn,Nat.cast_mul]
  rwa [Nat.cast_mul,ENNReal.mul_div_mul_left _ _ (by exact_mod_cast hk.ne') (by simp)] at hh

private theorem indexAt_le_replicated (k : ℕ) (hk : 0 < k) (u : ℕ → Bool) (n : ℕ) :
    indexAt u n ≤ indexAt (replicated k u) (k*n) := by
  apply iSup_le
  rintro ⟨w,hw⟩
  obtain ⟨a, rfl⟩ := hw
  exact le_trans (exponent_lift k hk u a n)
    (le_iSup_of_le ⟨(rayPrefix (fun index => (replicated k u) ((k*a) + index)) (k*n)),⟨k*a, rfl⟩⟩ (le_refl _))

private theorem indStar_le_replicated (k : ℕ) (hk : 0 < k) (u : ℕ → Bool) :
    indStar u ≤ indStar (replicated k u) := by
  unfold indStar
  apply le_iInf
  intro N
  apply le_trans (iInf_le _ N)
  apply iSup_le
  intro n
  by_cases hn : N ≤ n
  · rw [if_pos hn]
    have hn' : N ≤ k*n := le_trans hn (Nat.le_mul_of_pos_left n hk)
    exact le_trans (indexAt_le_replicated k hk u n)
      (le_iSup_of_le (k*n) (by rw [if_pos hn']))
  · rw [if_neg hn]
    exact bot_le

theorem exponent_eq_ofReal (w : List Bool) :
    exponent w = ENNReal.ofReal ((w.length : ℝ)/(per w : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast (per_is_period w).1)]
  simp only [exponent,ENNReal.ofReal_natCast]

theorem block_exponent_le_tail (u : ℕ → Bool) (a m N : ℕ) (hm : N ≤ m) :
    exponent ((rayPrefix (fun index => u (a + index)) m)) ≤ ⨆ n : ℕ, if N ≤ n then indexAt u n else 0 := by
  have hi : exponent ((rayPrefix (fun index => u (a + index)) m)) ≤ indexAt u m :=
    le_iSup_of_le ⟨(rayPrefix (fun index => u (a + index)) m),⟨a, rfl⟩⟩ (le_refl _)
  exact hi.trans (le_iSup_of_le m (by rw [if_pos hm]))

private theorem one_le_real_exponent (u : ℕ → Bool) (a n : ℕ) (hn : 0 < n) :
    1 ≤ (n : ℝ)/(per ((rayPrefix (fun index => u (a + index)) n)) : ℝ) := by
  have hp := (per_is_period ((rayPrefix (fun index => u (a + index)) n))).1
  have hpn : per ((rayPrefix (fun index => u (a + index)) n)) ≤ n :=
    per_le_of_period _ _ ((hasPeriod_iff_list _ _).mpr
      ⟨hn, List.hasPeriod_of_length_le _ n (by simp [rayPrefix])⟩)
  apply (le_div_iff₀ (by exact_mod_cast hp)).mpr
  simpa only [one_mul] using (show (per ((rayPrefix (fun index => u (a + index)) n)) : ℝ) ≤ (n : ℝ) by exact_mod_cast hpn)

private theorem vk_real_exponent_transport (k : ℕ) (hk : 0 < k) (a L N : ℕ)
    (hL8 : 8*k ≤ L) (hLN : k*(N+2) ≤ L) :
    ∃ b m, N ≤ m ∧
      (L : ℝ)/(per ((rayPrefix (fun index => (replicated k D5.S1.Words.goldenWord) (a + index)) L)) : ℝ) ≤
        (m : ℝ)/(per ((rayPrefix (fun index => D5.S1.Words.goldenWord (b + index)) m)) : ℝ)+(32*k : ℕ)/(L : ℝ) := by
  let p := per ((rayPrefix (fun index => (replicated k D5.S1.Words.goldenWord) (a + index)) L))
  have hp := per_is_period ((rayPrefix (fun index => (replicated k D5.S1.Words.goldenWord) (a + index)) L))
  have hppos : 0 < p := hp.1
  have hbound : L ≤ 4*p+4*k := vk_period_length_bound k hk a p L hp
  have hLpos : 0 < L := by nlinarith
  have h8p : L ≤ 8*p := by omega
  have hpposR : (0 : ℝ) < p := Nat.cast_pos'.mpr hppos
  have hLposR : (0 : ℝ) < L := Nat.cast_pos'.mpr hLpos
  have h8pR : (L : ℝ) ≤ 8*(p : ℝ) := by exact_mod_cast h8p
  have herror : (4*k : ℕ)/(p : ℝ) ≤ (32*k : ℕ)/(L : ℝ) := by
    apply (div_le_div_iff₀ hpposR hLposR).mpr
    push_cast
    nlinarith
  rcases period_aligned_or_short_overlap k hk _ 2 golden_frequent_transition a L p hp with hd | hs
  · obtain ⟨q,hq⟩ := hd
    have hqpos : 0 < q := by rw [hq] at hppos; exact Nat.pos_of_mul_pos_left hppos
    let m := (a+L)/k-(a/k+1)
    have hdecode : HasPeriod ((rayPrefix (fun index => D5.S1.Words.goldenWord ((a/k+1) + index)) m)) q :=
      period_decode k hk _ a L q hqpos (by change HasPeriod _ p at hp; rwa [hq] at hp)
    have hloss : L ≤ k*m+2*k := decode_length_loss k hk a L
    have hmN : N ≤ m := by
      by_contra hn
      have hmul := Nat.mul_lt_mul_of_pos_left (show m < N by omega) hk
      have hsum : k*(N+2) = k*N+2*k := by ring
      omega
    have hper : per ((rayPrefix (fun index => D5.S1.Words.goldenWord ((a/k+1) + index)) m)) ≤ q :=
      per_le_of_period _ _ hdecode
    have hqposR : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hbase : (m : ℝ)/(q : ℝ) ≤
        (m : ℝ)/(per ((rayPrefix (fun index => D5.S1.Words.goldenWord ((a/k+1) + index)) m)) : ℝ) := by
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast (per_is_period _).1)
      exact_mod_cast hper
    have he : (L : ℝ)/(p : ℝ) ≤ (m : ℝ)/(q : ℝ)+(4*k : ℕ)/(p : ℝ) := by
      apply (div_le_iff₀ hpposR).mpr
      have hh : (L : ℝ) ≤ (k : ℝ)*(m : ℝ)+2*(k : ℝ) := by exact_mod_cast hloss
      have hpeq : (p : ℝ) = (k : ℝ)*(q : ℝ) := by exact_mod_cast hq
      rw [add_mul,div_mul_cancel₀ _ (ne_of_gt hpposR),hpeq]
      have hcancel : (m : ℝ)/(q : ℝ)*((k : ℝ)*(q : ℝ)) = (k : ℝ)*(m : ℝ) := by
        field_simp
      rw [hcancel]
      push_cast
      nlinarith
    exact ⟨a/k+1,m,hmN,he.trans (add_le_add hbase herror)⟩
  · have hs' : L ≤ p+4*k := by simpa [Nat.mul_comm] using hs
    have he : (L : ℝ)/(p : ℝ) ≤ 1+(4*k : ℕ)/(p : ℝ) := by
      apply (div_le_iff₀ hpposR).mpr
      rw [add_mul,one_mul,div_mul_cancel₀ _ (ne_of_gt hpposR)]
      exact_mod_cast hs'
    exact ⟨0,N+1,by omega,he.trans (add_le_add
      (one_le_real_exponent _ 0 (N+1) (Nat.zero_lt_succ _)) herror)⟩

private theorem vk_exponent_le_tail (k : ℕ) (hk : 0 < k) (a L N : ℕ)
    (hL8 : 8*k ≤ L) (hLN : k*(N+2) ≤ L) :
    exponent ((rayPrefix (fun index => (replicated k D5.S1.Words.goldenWord) (a + index)) L)) ≤
      (⨆ n : ℕ, if N ≤ n then indexAt D5.S1.Words.goldenWord n else 0)+
        (32*k : ℕ)/(L : ℝ≥0∞) := by
  obtain ⟨b,m,hm,he⟩ := vk_real_exponent_transport k hk a L N hL8 hLN
  have hLpos : 0 < L := by nlinarith
  have ho := ENNReal.ofReal_le_ofReal he
  rw [ENNReal.ofReal_add (by positivity) (by positivity)] at ho
  have hr : ENNReal.ofReal ((32*k : ℕ)/(L : ℝ)) = (32*k : ℕ)/(L : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hLpos)]
    simp only [ENNReal.ofReal_natCast]
  have hv : ENNReal.ofReal ((L : ℝ)/(per ((rayPrefix (fun index => (replicated k D5.S1.Words.goldenWord) (a + index)) L)) : ℝ)) =
      exponent ((rayPrefix (fun index => (replicated k D5.S1.Words.goldenWord) (a + index)) L)) := by
    rw [exponent_eq_ofReal,rayPrefix,List.length_ofFn]
  rw [hv,hr] at ho
  have hs : ENNReal.ofReal ((m : ℝ)/(per ((rayPrefix (fun index => D5.S1.Words.goldenWord (b + index)) m)) : ℝ)) =
      exponent ((rayPrefix (fun index => D5.S1.Words.goldenWord (b + index)) m)) := by
    rw [exponent_eq_ofReal,rayPrefix,List.length_ofFn]
  rw [hs] at ho
  exact ho.trans (add_le_add (block_exponent_le_tail _ b m N hm) (le_refl _))

private theorem vk_indexAt_le_tail (k : ℕ) (hk : 0 < k) (L N : ℕ)
    (hL8 : 8*k ≤ L) (hLN : k*(N+2) ≤ L) :
    indexAt (replicated k D5.S1.Words.goldenWord) L ≤
      (⨆ n : ℕ, if N ≤ n then indexAt D5.S1.Words.goldenWord n else 0)+
        (32*k : ℕ)/(L : ℝ≥0∞) := by
  apply iSup_le
  rintro ⟨w,hw⟩
  obtain ⟨a, rfl⟩ := hw
  exact vk_exponent_le_tail k hk a L N hL8 hLN

private theorem indStar_eq_limsup (u : ℕ → Bool) :
    indStar u = Filter.limsup (indexAt u) Filter.atTop := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  unfold indStar
  congr 1
  funext N
  apply le_antisymm
  · apply iSup_le
    intro n
    split_ifs with hn
    · exact le_iSup_of_le n (le_iSup_of_le hn (le_refl _))
    · exact bot_le
  · apply iSup_le
    intro n
    apply iSup_le
    intro hn
    exact le_iSup_of_le n (by rw [if_pos hn])

theorem golden_indStar_replicated (k : ℕ) (hk : 0 < k) :
    indStar (replicated k D5.S1.Words.goldenWord) = indStar D5.S1.Words.goldenWord := by
  apply le_antisymm ?_ (indStar_le_replicated k hk _)
  change indStar (replicated k D5.S1.Words.goldenWord) ≤ ⨅ N : ℕ,
    ⨆ n : ℕ, if N ≤ n then indexAt D5.S1.Words.goldenWord n else 0
  apply le_iInf
  intro N
  rw [indStar_eq_limsup]
  let C := ⨆ n : ℕ, if N ≤ n then indexAt D5.S1.Words.goldenWord n else 0
  let E : ℕ → ℝ≥0∞ := fun n => (32*k : ℕ)/(n : ℝ≥0∞)
  have hE : Filter.Tendsto E Filter.atTop (nhds 0) := by
    simpa [E,div_eq_mul_inv] using
      (ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
        (a := ((32*k : ℕ) : ℝ≥0∞)) (Or.inr (ENNReal.natCast_ne_top _)))
  have hbound : Filter.limsup (indexAt (replicated k D5.S1.Words.goldenWord)) Filter.atTop ≤
      Filter.limsup (fun n => C+E n) Filter.atTop := by
    apply Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [Filter.eventually_ge_atTop (max (8*k) (k*(N+2)))] with n hn
    exact vk_indexAt_le_tail k hk n N ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
  have hlim : Filter.limsup (fun n => C+E n) Filter.atTop = C := by
    have hh := ENNReal.limsup_add_of_right_tendsto_zero hE (fun _ => C)
    change Filter.limsup (fun n => C+E n) Filter.atTop = Filter.limsup (fun _ : ℕ => C) Filter.atTop at hh
    simpa using hh
  exact hbound.trans_eq hlim

end D5.S1.Words.Complexity.CassaigneIndexTransport
