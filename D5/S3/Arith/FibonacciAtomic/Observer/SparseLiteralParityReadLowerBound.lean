/- GID: D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every native parity run reads every independent original cone. -/

import D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralControlTable
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
import D5.S1.Words.AdmissibleWords.AdmissibleCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeDepthPatterns (Frontier fill frontierAddress frontier_geometry)
open NativePolynomialDescriptorObstruction (fullPattern)
open NativeSerialMachine (Op Event Trace Run reads)
open scoped BigOperators

/-- The original target is the parity bit of all selected independent labels. -/
def parity {h : Nat} (x : Fin h → Bool) : Bool :=
  decide ((∑ i, (x i).toNat) % 2 = 1)

/-- The numerical original bit is zero at every unselected skeleton leaf. -/
noncomputable def assigned {h depth : Nat} (slots : Fin h → Frontier (fullPattern depth))
    (x : Fin h → Bool) (j : Frontier (fullPattern depth)) : Bool :=
  if found : ∃ i, slots i = j then x found.choose else false

/-- All selected labels vary independently on the same complete original skeleton. -/
noncomputable def source {h depth : Nat} (slots : Fin h → Frontier (fullPattern depth))
    (x : Fin h → Bool) : Source :=
  fill (fullPattern depth) (fun j => .of (!(assigned slots x j)))

private theorem parity_flip {h : Nat} (x : Fin h → Bool) (i : Fin h) :
    parity (Function.update x i (!(x i))) ≠ parity x := by
  let base := ∑ j ∈ Finset.univ.erase i, (x j).toNat
  have old : (∑ j, (x j).toNat) = base + (x i).toNat :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  have new : (∑ j, ((Function.update x i (!(x i))) j).toNat) = base + (!(x i)).toNat := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hm := Nat.mod_lt base (by decide : 0 < 2)
  have cases_mod : base % 2 = 0 ∨ base % 2 = 1 := by omega
  unfold parity
  rw [new, old]
  rcases cases_mod with hm0 | hm1
  · have hs : (base+1)%2 = 1 := by omega
    cases x i <;> simp [hm0, hs]
  · have hs : (base+1)%2 = 0 := by omega
    cases x i <;> simp [hm1, hs]

private theorem assigned_off_slot {h depth : Nat}
    (slots : Fin h → Frontier (fullPattern depth)) (x : Fin h → Bool)
    (i : Fin h) (j : Frontier (fullPattern depth)) (ne : j ≠ slots i) :
    assigned slots (Function.update x i (!(x i))) j = assigned slots x j := by
  classical
  unfold assigned
  split_ifs with found
  · have choice_ne : found.choose ≠ i := by
      intro same
      exact ne (same ▸ found.choose_spec).symm
    exact Function.update_of_ne choice_ne _ _
  · rfl

private theorem full_readout_local (depth : Nat)
    (f g : Frontier (fullPattern depth) → Source) (a : Address) (epoch : Nat)
    (same : ∀ j, (frontierAddress (fullPattern depth) j).IsPrefix a → f j = g j) :
    readout a (substitution^[epoch] (fill (fullPattern depth) f)) =
      readout a (substitution^[epoch] (fill (fullPattern depth) g)) := by
  induction depth generalizing a with
  | zero =>
      have eq := same () (by simp [frontierAddress])
      simpa only [fullPattern, fill] using congrArg (fun z => readout a (substitution^[epoch] z)) eq
  | succ depth ih =>
      have rho (s t : Source) : substitution^[epoch] (.mul s t) =
          .mul (substitution^[epoch] s) (substitution^[epoch] t) :=
        Function.Semiconj₂.iterate
          (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
            fun s t => substitution.map_mul s t) epoch s t
      simp only [fullPattern, fill, rho]
      cases a with
      | nil => rfl
      | cons b a =>
          cases b
          · apply ih (fun j => f (.inl j)) (fun j => g (.inl j)) a
            intro j hj
            exact same (.inl j) (by simpa [fullPattern, frontierAddress] using hj)
          · apply ih (fun j => f (.inr j)) (fun j => g (.inr j)) a
            intro j hj
            exact same (.inr j) (by simpa [fullPattern, frontierAddress] using hj)

private theorem off_cone_reply {h depth : Nat}
    (slots : Fin h → Frontier (fullPattern depth)) (x : Fin h → Bool) (i : Fin h)
    (a : Address) (epoch : Nat)
    (outside : ¬ (frontierAddress (fullPattern depth) (slots i)).IsPrefix a) :
    readout a (substitution^[epoch] (source slots (Function.update x i (!(x i))))) =
      readout a (substitution^[epoch] (source slots x)) := by
  apply full_readout_local
  intro j hj
  have ne : j ≠ slots i := by
    intro eq
    exact outside (eq ▸ hj)
  rw [assigned_off_slot slots x i j ne]

private theorem replay_avoiding {C O : Type} {δ : C → Op C O}
    {c : C} {epoch : Nat} {u : Source} {trace : Trace} {out : O}
    (run : Run δ c epoch (substitution^[epoch] u) trace out)
    (v : Source)
    (same : ∀ e a r, Event.read e a r ∈ trace →
      readout a (substitution^[e] v) = readout a (substitution^[e] u)) :
    Run δ c epoch (substitution^[epoch] v) trace out := by
  obtain ⟨_, _, _, _, _, truth⟩ :=
    NativeSerialMachine.actual_register_execution δ run u rfl []
  exact NativeSerialDepth.transfer run u v rfl
    (fun e a r hr => (same e a r hr).trans (truth e a r hr))

private theorem cone_must_be_read {h depth : Nat} {C : Type}
    (slots : Fin h → Frontier (fullPattern depth)) (δ : C → Op C Bool) (start : C)
    (sound : ∀ x t out, Run δ start 0 (source slots x) t out → out = parity x)
    (x : Fin h → Bool) (trace : Trace) (out : Bool)
    (run : Run δ start 0 (source slots x) trace out) (i : Fin h) :
    ∃ e a r, Event.read e a r ∈ trace ∧
      (frontierAddress (fullPattern depth) (slots i)).IsPrefix a := by
  classical
  by_contra missing
  have avoid : ∀ e a r, Event.read e a r ∈ trace →
      ¬ (frontierAddress (fullPattern depth) (slots i)).IsPrefix a := by
    intro e a r hr hp
    exact missing ⟨e,a,r,hr,hp⟩
  have second : Run δ start 0 (source slots (Function.update x i (!(x i)))) trace out := by
    exact replay_avoiding (u := source slots x) run
      (source slots (Function.update x i (!(x i))))
      (fun e a r hr => off_cone_reply slots x i a e (avoid e a r hr))
  exact parity_flip x i ((sound _ _ _ second).symm.trans (sound _ _ _ run))

private theorem read_event_mem {trace : Trace} {e : Nat} {a : Address} {r : Reply}
    (mem : Event.read e a r ∈ trace) : (e,a,r) ∈ reads trace := by
  induction trace with
  | nil => simp at mem
  | cons event trace ih =>
      rcases List.mem_cons.mp mem with eq | later
      · subst event
        simp [reads]
      · cases event <;> simp only [reads]
        · exact ih later
        · exact ih later
        · exact List.mem_cons_of_mem _ (ih later)

/-- Every independent original cone has its own actual read occurrence. The
controller may perform arbitrary finite local computation, choose arbitrary
literal depths and update adaptively; only sound terminating runs are required. -/
theorem parity_read_lower_bound {h depth : Nat} {C : Type}
    (slots : Fin h → Frontier (fullPattern depth))
    (distinct : Function.Injective (fun i => frontierAddress (fullPattern depth) (slots i)))
    (δ : C → Op C Bool) (start : C)
    (sound : ∀ x t out, Run δ start 0 (source slots x) t out → out = parity x)
    (x : Fin h → Bool) (trace : Trace) (out : Bool)
    (run : Run δ start 0 (source slots x) trace out) :
    h ≤ (reads trace).length ∧
    ∀ i : Fin h, ∃ e a r, Event.read e a r ∈ trace ∧
      (frontierAddress (fullPattern depth) (slots i)).IsPrefix a := by
  classical
  have cover := cone_must_be_read slots δ start sound x trace out run
  have witness (i : Fin h) : ∃ j : Fin (reads trace).length,
      (frontierAddress (fullPattern depth) (slots i)).IsPrefix ((reads trace).get j).2.1 := by
    obtain ⟨e,a,r,hr,hp⟩ := cover i
    obtain ⟨j,hj⟩ := List.get_of_mem (read_event_mem hr)
    exact ⟨j, by rw [hj]; exact hp⟩
  choose select selected using witness
  have inj : Function.Injective select := by
    intro i j eq
    apply distinct
    have hi := selected i
    have hj := selected j
    rw [eq] at hi
    have lengths := (frontier_geometry depth (fullPattern depth)).1
    exact (List.prefix_of_prefix_length_le hi hj (by rw [lengths, lengths])).eq_of_length
      (by rw [lengths, lengths])
  exact ⟨by simpa using Fintype.card_le_of_injective select inj, cover⟩


private theorem read_row {C O : Type} {δ : C → Op C O}
    {c : C} {epoch : Nat} {u : Source} {trace : Trace} {out : O}
    (run : Run δ c epoch u trace out) {e : Nat} {a : Address} {r : Reply}
    (mem : Event.read e a r ∈ trace) : ∃ state k, δ state = .read a k := by
  induction run with
  | stop row => simp at mem
  | localStep row tail ih => exact ih (by simpa using mem)
  | update row tail ih => exact ih (by simpa using mem)
  | @read c e u b k y t o row reply tail ih =>
      rcases List.mem_cons.mp mem with eq | later
      · cases eq
        exact ⟨c,k,row⟩
      · exact ih later

/-- The fixed literal and fixed output rows require h different query states and
both parity halts, irrespective of adaptive epochs and repeated visits. -/
private theorem parity_control_lower_bound {h depth : Nat} {C : Type} [Fintype C]
    (positive : 0 < h) (slots : Fin h → Frontier (fullPattern depth))
    (distinct : Function.Injective (fun i => frontierAddress (fullPattern depth) (slots i)))
    (δ : C → Op C Bool) (start : C)
    (sound : ∀ x t out, Run δ start 0 (source slots x) t out → out = parity x)
    (total : ∀ x, ∃ t out, Run δ start 0 (source slots x) t out) :
    h + 2 ≤ Fintype.card C ∧
    (∀ x trace out, Run δ start 0 (source slots x) trace out → h ≤ (reads trace).length) ∧
    ∀ (width : Nat) (encode : C → {w : Fin width → Bool //
      D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm width w}),
      Function.Injective encode → h + 2 ≤ Nat.fib (width + 2) := by
  classical
  obtain ⟨trace,out,run⟩ := total (fun _ => false)
  have covered := (parity_read_lower_bound slots distinct δ start sound _ trace out run).2
  have queries (i : Fin h) : ∃ c a k, δ c = .read a k ∧
      (frontierAddress (fullPattern depth) (slots i)).IsPrefix a := by
    obtain ⟨e,a,r,hr,hp⟩ := covered i
    obtain ⟨c,k,row⟩ := read_row run hr
    exact ⟨c,a,k,row,hp⟩
  choose query address continuation rows cones using queries
  have query_inj : Function.Injective query := by
    intro i j eq
    have ae : address i = address j :=
      (Op.read.inj ((rows i).symm.trans ((congrArg δ eq).trans (rows j)))).1
    apply distinct
    have hi := cones i
    rw [ae] at hi
    have lengths := (frontier_geometry depth (fullPattern depth)).1
    exact (List.prefix_of_prefix_length_le hi (cones j) (by rw [lengths, lengths])).eq_of_length
      (by rw [lengths, lengths])
  have target (b : Bool) : ∃ x : Fin h → Bool, parity x = b := by
    cases b
    · exact ⟨fun _ => false, by simp [parity]⟩
    · let zero : Fin h → Bool := fun _ => false
      have flipped := parity_flip zero ⟨0,positive⟩
      have pzero : parity zero = false := by simp [parity, zero]
      refine ⟨Function.update zero ⟨0,positive⟩ true, ?_⟩
      rw [pzero] at flipped
      change parity (Function.update zero ⟨0,positive⟩ true) ≠ false at flipped
      cases he : parity (Function.update zero ⟨0,positive⟩ true) <;> simp_all
  have halted (b : Bool) : ∃ c, δ c = .stop b := by
    obtain ⟨x,hx⟩ := target b
    obtain ⟨t,o,execution⟩ := total x
    obtain ⟨c,e,_,_,row,_⟩ := NativeSerialMachine.actual_register_execution δ execution
      (source slots x) (by simp) []
    exact ⟨c, by simpa [sound x t o execution, hx] using row⟩
  choose halt halt_row using halted
  let inject : Fin h ⊕ Bool → C := Sum.elim query halt
  have inj : Function.Injective inject := by
    intro a b eq
    cases a with
    | inl i => cases b with
      | inl j => exact congrArg Sum.inl (query_inj eq)
      | inr b =>
        have bad := (rows i).symm.trans ((congrArg δ eq).trans (halt_row b))
        cases bad
    | inr a => cases b with
      | inl j =>
        have bad := (halt_row a).symm.trans ((congrArg δ eq).trans (rows j))
        cases bad
      | inr b =>
        exact congrArg Sum.inr (Op.stop.inj
          ((halt_row a).symm.trans ((congrArg δ eq).trans (halt_row b))))
  have card_bound : h + 2 ≤ Fintype.card C := by
    simpa using Fintype.card_le_of_injective inject inj
  refine ⟨card_bound, (fun x t o execution =>
    (parity_read_lower_bound slots distinct δ start sound x t o execution).1), ?_⟩
  intro width encode faithful
  have capacity := Fintype.card_le_of_injective encode faithful
  rw [D5.S1.Words.AdmissibleWords.AdmissibleCount.admissibleWord_card_eq_fib] at capacity
  exact card_bound.trans capacity


/-- The prescribed distinct length-d literals, in their given order. -/
def sourceSlots {h : Nat} (depth : Nat) (q : Fin h → Address)
    (lengths : ∀ i, (q i).length = depth) : Fin h → Frontier (fullPattern depth) :=
  fun i => SparseLiteralControlTable.fullIndex depth (q i) (lengths i)

/-- Original sources with free labels at exactly the prescribed literals. -/
noncomputable def originalSource {h : Nat} (depth : Nat) (q : Fin h → Address)
    (lengths : ∀ i, (q i).length = depth) (x : Fin h → Bool) : Source :=
  source (sourceSlots depth q lengths) x

/-- Theorem 8.2's acquisition and complete-memory lower bounds, with the original
literal family and arbitrary adaptive serial controllers. Every selected
original label is realized; every nonselected skeleton leaf is alpha. -/
theorem literal_parity_lower_bounds {h depth : Nat} {C : Type} [Fintype C]
    (positive : 0 < h) (q : Fin h → Address) (lengths : ∀ i, (q i).length = depth)
    (distinct : Function.Injective q) (δ : C → Op C Bool) (start : C)
    (sound : ∀ x t out, Run δ start 0 (originalSource depth q lengths x) t out → out = parity x)
    (total : ∀ x, ∃ t out, Run δ start 0 (originalSource depth q lengths x) t out) :
    (∀ x i, ActualLeafHistoryRigidity.subtree (q i) (originalSource depth q lengths x) =
      some (.of (!(x i)))) ∧
    (∀ x j, (∀ i, frontierAddress (fullPattern depth) j ≠ q i) →
      ActualLeafHistoryRigidity.subtree (frontierAddress (fullPattern depth) j)
        (originalSource depth q lengths x) = some (.of true)) ∧
    h + 2 ≤ Fintype.card C ∧
    (∀ x trace out, Run δ start 0 (originalSource depth q lengths x) trace out →
      h ≤ (reads trace).length) ∧
    ∀ (width : Nat) (encode : C → {w : Fin width → Bool //
      D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm width w}),
      Function.Injective encode → h + 2 ≤ Nat.fib (width + 2) := by
  classical
  let slots := sourceSlots depth q lengths
  have addresses (i : Fin h) : frontierAddress (fullPattern depth) (slots i) = q i :=
    SparseLiteralControlTable.full_index_address depth (q i) (lengths i)
  have slot_inj : Function.Injective slots := by
    intro i j eq
    apply distinct
    rw [← addresses i, ← addresses j, eq]
  have address_inj : Function.Injective
      (fun i => frontierAddress (fullPattern depth) (slots i)) := by
    simpa only [addresses] using distinct
  refine ⟨?_, ?_, parity_control_lower_bound positive slots address_inj δ start sound total⟩
  · intro x i
    have found : ∃ j, slots j = slots i := ⟨i,rfl⟩
    have chosen : found.choose = i := slot_inj found.choose_spec
    change ActualLeafHistoryRigidity.subtree (q i)
      (fill (fullPattern depth) (fun j => .of (!(assigned slots x j)))) = _
    rw [← addresses i, (frontier_geometry depth (fullPattern depth)).2.1]
    simp only [assigned, dif_pos found, chosen]
  · intro x j missing
    have none : ¬ ∃ i, slots i = j := by
      rintro ⟨i,hi⟩
      apply missing i
      rw [← hi, addresses]
    change ActualLeafHistoryRigidity.subtree (frontierAddress (fullPattern depth) j)
      (fill (fullPattern depth) (fun j => .of (!(assigned slots x j)))) = _
    rw [(frontier_geometry depth (fullPattern depth)).2.1]
    simp only [assigned, dif_neg none, Bool.not_false]

end D5.S3.Arith.FibonacciAtomic.Observer.SparseLiteralParityReadLowerBound
