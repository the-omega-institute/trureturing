/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerFrontier
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerFrontier
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Joint complete-entry capacity and finite-state minima on the actual repeated-partner origin fiber. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerControllers

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier
open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualCutPartitionRecovery (LiteralRow canonicalRow)
open NativeSixSourceCones
open NativeSixSourceMoore
open NativeRepeatedPartnerControllers
universe u v

/-- The export is the entire recoverable entry state. A finite cover of its
realized range expresses an upper capacity budget, with no retained payload. -/
def Solves {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (M : Controller Q H) (entry : Fiber → Q ⊕ H) (r q : Nat) : Prop :=
  (∃ E : Finset (Q ⊕ H), E.card ≤ r ∧ ∀ x, entry x ∈ E) ∧
  ∀ x : Fiber, ∃ h tr, Run M (substitution x.val) (entry x) tr h ∧
    M.out h = canonicalRow P x.val ∧ tr.length ≤ q

private def select : Fin 5 → Fin 6 := ![0,2,3,4,5]
private theorem selected_labels : ∀ j : Fin 5, label (select j) = j := by decide +kernel

private def factor (a : Address) : Bool → Reply := (all_address_factor a).choose
private theorem factor_eq (a : Address) (z : Fin 6) :
    readout a (current z) = factor a (question a z) := (all_address_factor a).choose_spec z
private def nextBit {Q : Type u} {H : Type v} (M : Controller Q H) (s : Q) (b : Bool) : Q ⊕ H :=
  M.next s (factor (M.addr s) b)

private def possible {Q : Type u} {H : Type v} [DecidableEq H]
    (M : Controller Q H) : Nat → Q ⊕ H → Finset H
  | 0, .inl _ => ∅
  | 0, .inr h => {h}
  | n+1, .inl s => possible M n (nextBit M s false) ∪ possible M n (nextBit M s true)
  | _+1, .inr h => {h}

private theorem possible_card {Q : Type u} {H : Type v} [DecidableEq H]
    (M : Controller Q H) (q : Nat) (k : Q ⊕ H) : (possible M q k).card ≤ 2^q := by
  induction q generalizing k with
  | zero => cases k <;> simp [possible]
  | succ q ih =>
      cases k with
      | inr h =>
          simp only [possible,Finset.card_singleton]
          exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
      | inl s =>
          exact (Finset.card_union_le _ _).trans (by
            have a := ih (nextBit M s false)
            have b := ih (nextBit M s true)
            rw [Nat.pow_succ]
            omega)

private theorem run_possible {Q : Type u} {H : Type v} [DecidableEq H]
    (M : Controller Q H) (z : Fin 6) {k : Q ⊕ H} {tr : List Q} {h : H}
    (run : Run M (current z) k tr h) (q : Nat) (budget : tr.length ≤ q) :
    h ∈ possible M q k := by
  induction run generalizing q with
  | halt h => cases q <;> simp [possible]
  | @read s tr h tail ih =>
      cases q with
      | zero => simp at budget
      | succ q =>
          have mem := ih q (by simpa using budget)
          rw [factor_eq] at mem
          cases bit : question (M.addr s) z
          · exact Finset.mem_union_left _ (by simpa [nextBit,bit] using mem)
          · exact Finset.mem_union_right _ (by simpa [nextBit,bit] using mem)

private theorem run_support {Q : Type u} {H : Type v} (M : Controller Q H)
    {t : Source} {k : Q ⊕ H} {tr : List Q} {h : H} (run : Run M t k tr h)
    (w : Q ⊕ H) (mem : w ∈ tr.map Sum.inl ++ [Sum.inr h]) :
    w = k ∨ ∃ s ∈ tr, M.next s (readout (M.addr s) t) = w := by
  induction run with
  | halt h => simpa using mem
  | @read s tr h tail ih =>
      simp only [List.map_cons,List.cons_append,List.mem_cons] at mem
      rcases mem with eq | mem
      · exact Or.inl eq
      · rcases ih mem with eq | ⟨p,hp,step⟩
        · exact Or.inr ⟨s,List.mem_cons_self,eq.symm⟩
        · exact Or.inr ⟨p,List.mem_cons_of_mem _ hp,step⟩

/-- All finite controllers and all jointly chosen complete-entry encoders are
covered. Binary branching is proved only on the simultaneous actual sources;
the full native reply interface remains unrestricted. -/
theorem native_budget_lower {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (M : Controller Q H) (entry : Fiber → Q ⊕ H) (r q : Nat)
    (success : Solves M entry r q) :
    5 ≤ r * 2^q ∧ 5 ≤ Fintype.card H ∧
      max 5 (10-r) ≤ Fintype.card (Q ⊕ H) := by
  classical
  obtain ⟨⟨E,cap,entries⟩,correct⟩ := success
  have six (z : Fin 6) : ∃ h tr,
      Run M (current z) (entry (actual z)) tr h ∧
      M.out h = predecessor (label z) ∧ tr.length ≤ q := by
    obtain ⟨h,tr,run,out,budget⟩ := correct (actual z)
    refine ⟨h,tr,?_,out.trans (six_source_realization.1 z).2.2,budget⟩
    simpa only [actual,(six_source_realization.1 z).1] using run
  choose h tr runs outputs budgets using six
  have haltInj : Function.Injective (fun j : Fin 5 => h (select j)) := by
    intro i j eq
    have targetEq := (outputs (select i)).symm.trans
      ((congrArg M.out eq).trans (outputs (select j)))
    simpa only [selected_labels] using six_source_realization.2 targetEq
  have halts : 5 ≤ Fintype.card H := by
    simpa using Fintype.card_le_of_injective _ haltInj
  have capacity : 5 ≤ r * 2^q := by
    have sub : Finset.univ.image (fun j : Fin 5 => h (select j)) ⊆
        E.biUnion (possible M q) := by
      intro k hk
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_biUnion.mpr ⟨entry (actual (select j)),entries _,
        run_possible M _ (runs _) q (budgets _)⟩
    have lo := Finset.card_le_card sub
    rw [Finset.card_image_of_injective _ haltInj] at lo
    have hi := Finset.card_biUnion_le (s := E) (t := possible M q)
    have bound : ∑ k ∈ E, (possible M q k).card ≤ E.card * 2^q := by
      calc
        _ ≤ ∑ _k ∈ E, 2^q := Finset.sum_le_sum (fun k _ => possible_card M q k)
        _ = _ := by simp [Nat.mul_comm]
    have bound' := Nat.mul_le_mul_right (2^q) cap
    simp only [Finset.card_univ,Fintype.card_fin] at lo
    omega
  let R : Finset Q := Finset.univ.biUnion (fun z : Fin 6 => (tr z).toFinset)
  let V : Finset (Q ⊕ H) := Finset.univ.biUnion (fun z : Fin 6 =>
    (tr z).toFinset.image Sum.inl ∪ {Sum.inr (h z)})
  let T : Finset (Q ⊕ H) := Finset.univ.image (fun j : Fin 5 => Sum.inr (h (select j)))
  have rsub : R.image Sum.inl ⊆ V := by
    intro w hw
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨z,_,hz⟩ := Finset.mem_biUnion.mp hs
    exact Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨s,hz,rfl⟩)⟩
  have tsub : T ⊆ V := by
    intro w hw
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_biUnion.mpr ⟨select j,Finset.mem_univ _,Finset.mem_union_right _
      (Finset.mem_singleton_self _)⟩
  have dis : Disjoint (R.image Sum.inl) T := by
    apply Finset.disjoint_left.mpr
    intro w hw ht
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp ht
    cases eq
  have tinj : Function.Injective (fun j : Fin 5 => (Sum.inr (h (select j)) : Q ⊕ H)) :=
    Sum.inr_injective.comp haltInj
  have lo : R.card + 5 ≤ V.card := by
    have bound := Finset.card_le_card (Finset.union_subset rsub tsub)
    rw [Finset.card_union_of_disjoint dis,
      Finset.card_image_of_injective _ Sum.inl_injective] at bound
    have tc : T.card = 5 := by
      dsimp only [T]
      rw [Finset.card_image_of_injective _ tinj]
      simp
    omega
  have sub : V ⊆ E ∪ (R.image (fun s => nextBit M s false) ∪
      R.image (fun s => nextBit M s true)) := by
    intro w hw
    obtain ⟨z,_,hz⟩ := Finset.mem_biUnion.mp hw
    have mem : w ∈ (tr z).map Sum.inl ++ [Sum.inr (h z)] := by
      rcases Finset.mem_union.mp hz with hm | hm
      · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hm
        exact List.mem_append_left _ (List.mem_map.mpr ⟨s,List.mem_toFinset.mp hs,rfl⟩)
      · exact List.mem_append_right _ (by simpa using hm)
    rcases run_support M (runs z) w mem with eq | ⟨s,hs,step⟩
    · exact Finset.mem_union_left _ (eq ▸ entries (actual z))
    · have sr : s ∈ R := Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr hs⟩
      rw [factor_eq] at step
      apply Finset.mem_union_right
      cases bit : question (M.addr s) z
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨s,sr,by simpa [nextBit,bit] using step⟩
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨s,sr,by simpa [nextBit,bit] using step⟩
  have hi : V.card ≤ r + 2 * R.card := by
    have a := Finset.card_le_card sub
    have b := Finset.card_union_le E
      (R.image (fun s => nextBit M s false) ∪ R.image (fun s => nextBit M s true))
    have c := Finset.card_union_le (R.image (fun s => nextBit M s false))
      (R.image (fun s => nextBit M s true))
    have d := Finset.card_image_le (s := R) (f := fun s => nextBit M s false)
    have e := Finset.card_image_le (s := R) (f := fun s => nextBit M s true)
    omega
  have rcard : R.card ≤ Fintype.card Q := Finset.card_le_univ R
  refine ⟨capacity,halts,?_⟩
  rw [Fintype.card_sum]
  omega

/-- The exceptional three-call value and the ordinary finite-state bound. -/
def minimum (r q : Nat) : Nat := if r = 1 ∧ q = 3 then 10 else max 5 (10-r)

private theorem normalized_constant {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (M : Controller Q H) (entry : Fiber → Q ⊕ H) (q : Nat)
    (success : Solves M entry 1 q) : ∀ x, entry x = entry (actual 0) := by
  classical
  obtain ⟨⟨E,cap,mem⟩,_⟩ := success
  exact fun x => Finset.card_le_one.mp cap (entry x) (mem x) (entry (actual 0)) (mem _)

private theorem attained_solves {n : Nat} (T : Table n)
    (entry : Fin 5 → Fin n ⊕ Fin 5) (r q : Nat) (att : Attains T entry r q) :
    Solves (installed T) (fun x => entry (acquiredLabel (profile x))) r q := by
  classical
  obtain ⟨E,card,range⟩ := att.1
  refine ⟨⟨E,card.le,?_⟩,att.2.1⟩
  intro x
  have mem : entry (acquiredLabel (profile x)) ∈
      Set.range (fun x : Fiber => entry (acquiredLabel (profile x))) := ⟨x,rfl⟩
  rw [range] at mem
  exact mem

private theorem solves_mono {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
    (M : Controller Q H) (entry : Fiber → Q ⊕ H) {r q r' q' : Nat}
    (success : Solves M entry r q) (hr : r ≤ r') (hq : q ≤ q') : Solves M entry r' q' := by
  obtain ⟨⟨E,card,mem⟩,correct⟩ := success
  refine ⟨⟨E,card.trans hr,mem⟩,?_⟩
  intro x
  obtain ⟨h,tr,run,out,budget⟩ := correct x
  exact ⟨h,tr,run,out,budget.trans hq⟩

/-- Exact full-fiber frontier: infeasible budgets admit no controller; every
feasible upper budget has the stated universal minimum and a matching common
controller with five fixed complete-row halts. The entry encoder is optimized
jointly with the common tables, rather than fixed in advance. -/
theorem exact_frontier (r q : Nat) (positive : 1 ≤ r) :
    (∀ {Q : Type u} {H : Type v} [Fintype Q] [Fintype H]
      (M : Controller Q H) (entry : Fiber → Q ⊕ H), Solves M entry r q →
      5 ≤ r * 2^q ∧ minimum r q ≤ Fintype.card (Q ⊕ H)) ∧
    (5 ≤ r * 2^q → ∃ (n : Nat) (M : Controller (Fin n) (Fin 5))
      (entry : Fiber → Fin n ⊕ Fin 5), Solves M entry r q ∧ n+5 = minimum r q) := by
  constructor
  · intro Q H _ _ M entry success
    have lower := native_budget_lower M entry r q success
    refine ⟨lower.1,?_⟩
    by_cases special : r = 1 ∧ q = 3
    · obtain ⟨rfl,rfl⟩ := special
      have constant := normalized_constant M entry 3 success
      have correct : ∀ x : Fiber, ∃ h tr,
          Run M (substitution x.val) (entry (actual 0)) tr h ∧
          M.out h = canonicalRow P x.val ∧ tr.length ≤ 3 := by
        intro x
        simpa only [constant x] using success.2 x
      simpa [minimum] using (three_call_state_obstruction M (entry (actual 0)) correct).2.2
    · simpa [minimum,special] using lower.2.2
  · intro feasible
    obtain ⟨a,b,c,d,e,f⟩ := matching_controllers
    have qa : r = 1 → 3 ≤ q := by
      intro eq
      subst r
      by_contra hn
      have hq : q ≤ 2 := by omega
      interval_cases q <;> norm_num at feasible
    have qb : r = 2 → 2 ≤ q := by
      intro eq
      subst r
      by_contra hn
      have hq : q ≤ 1 := by omega
      interval_cases q <;> norm_num at feasible
    have qc : r ≤ 4 → 1 ≤ q := by
      intro small
      by_contra hn
      have eq : q = 0 := by omega
      subst q
      simp only [pow_zero,Nat.mul_one] at feasible
      omega
    by_cases one : r = 1
    · subst r
      by_cases three : q = 3
      · subst q
        exact ⟨5,installed ten,_,attained_solves ten _ _ _ a,by decide⟩
      · have qfour : 4 ≤ q := by have := qa rfl; omega
        refine ⟨4,installed nine,_,solves_mono _ _ (attained_solves nine _ _ _ b) (by omega) qfour,?_⟩
        simp [minimum,three]
    · by_cases two : r = 2
      · subst r
        exact ⟨3,installed eight,_,solves_mono _ _ (attained_solves eight _ _ _ c) (by omega) (qb rfl),by simp [minimum]⟩
      · by_cases three : r = 3
        · subst r
          exact ⟨2,installed seven,_,solves_mono _ _ (attained_solves seven _ _ _ d) (by omega) (qc (by omega)),by simp [minimum]⟩
        · by_cases four : r = 4
          · subst r
            exact ⟨1,installed six,_,solves_mono _ _ (attained_solves six _ _ _ e) (by omega) (qc (by omega)),by simp [minimum]⟩
          · have large : 5 ≤ r := by omega
            refine ⟨0,installed five,_,solves_mono _ _ (attained_solves five _ _ _ f) large (Nat.zero_le q),?_⟩
            have bound : 10-r ≤ 5 := by omega
            simp [minimum,one,max_eq_left bound]

#print axioms native_budget_lower
#print axioms exact_frontier
end D5.S3.Arith.FibonacciAtomic.Observer.NativeRepeatedPartnerFrontier
