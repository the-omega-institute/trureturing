import D5.S3.Geometry.Hyperideal.EdgeStarTransitions
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceCycleCandidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions
open private Pairing Pairing.mk Pairing.exists_reversed
  from D5.S3.Geometry.Hyperideal.EdgeStarTransitions
variable {T : Type*}

-- Temporary bindings and interface adaptation, with no canonical content claim.
structure Orientation (P : RawFacePairing T) where
  reversed : Occurrence T → Bool
  entersFace : ∀ i : Occurrence T,
    incomingFace reversed (rawNext P.facePair P.faceMap reversed i) =
      (P.facePair (i.1, outgoingFace reversed i)).2

def chooseOrientation [Fintype T] (P : RawFacePairing T) : Orientation P := by
  let p : Pairing T := Pairing.mk P.facePair P.faceMap
    P.pairInvolutive P.pairFixedFree P.mapInverse
  let h := Pairing.exists_reversed p
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

noncomputable def Orientation.next [Fintype T] {P : RawFacePairing T}
    (s : Orientation P) : Equiv.Perm (Occurrence T) := by
  let f := rawNext P.facePair P.faceMap s.reversed
  have hslotTable (j : Fin 6) (b : Bool) :
      faceEdge (if b then (edgeFaces j).1 else (edgeFaces j).2)
        (if b then (edgeFaceSlots j).1 else (edgeFaceSlots j).2) = j := by
    cases b <;> fin_cases j <;> decide
  have hslot (i : Occurrence T) :
      faceEdge (outgoingFace s.reversed i) (outgoingSlot s.reversed i) = i.2 := by
    simpa [outgoingFace, outgoingSlot] using hslotTable i.2 (s.reversed i)
  have hfaceInjective (a : Fin 4) : Function.Injective (faceEdge a) := by
    fin_cases a <;> decide
  have hinj : Function.Injective f := by
    intro i j hij
    have hpaired :
        P.facePair (i.1, outgoingFace s.reversed i) =
          P.facePair (j.1, outgoingFace s.reversed j) := by
      apply Prod.ext
      · simpa [f, rawNext] using congrArg (fun x : Occurrence T => x.1) hij
      · calc
          (P.facePair (i.1, outgoingFace s.reversed i)).2 =
              incomingFace s.reversed (f i) := (s.entersFace i).symm
          _ = incomingFace s.reversed (f j) := congrArg _ hij
          _ = (P.facePair (j.1, outgoingFace s.reversed j)).2 := s.entersFace j
    have hsource := P.facePair.injective hpaired
    have hmapped :
        P.faceMap (i.1, outgoingFace s.reversed i) (outgoingSlot s.reversed i) =
          P.faceMap (i.1, outgoingFace s.reversed i) (outgoingSlot s.reversed j) := by
      apply hfaceInjective (P.facePair (i.1, outgoingFace s.reversed i)).2
      have hedge := congrArg Prod.snd hij
      dsimp [f, rawNext] at hedge
      rw [← hsource] at hedge
      exact hedge
    have hslots := (P.faceMap (i.1, outgoingFace s.reversed i)).injective hmapped
    apply Prod.ext
    · exact congrArg (fun x : T × Fin 4 => x.1) hsource
    · calc
        i.2 = faceEdge (outgoingFace s.reversed i) (outgoingSlot s.reversed i) :=
          (hslot i).symm
        _ = faceEdge (outgoingFace s.reversed j) (outgoingSlot s.reversed j) := by
          have hf := congrArg (fun x : T × Fin 4 => x.2) hsource
          exact congrArg₂ faceEdge hf hslots
        _ = j.2 := hslot j
  exact Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩

def incomingSlot (r : Occurrence T → Bool) (i : Occurrence T) : Fin 3 :=
  if r i then (edgeFaceSlots i.2).2 else (edgeFaceSlots i.2).1

private theorem outgoing_slot (s : Occurrence T → Bool) (i : Occurrence T) :
    faceEdge (outgoingFace s i) (outgoingSlot s i) = i.2 := by
  have h (e : Fin 6) (b : Bool) :
      faceEdge (if b then (edgeFaces e).1 else (edgeFaces e).2)
        (if b then (edgeFaceSlots e).1 else (edgeFaceSlots e).2) = e := by
    cases b <;> fin_cases e <;> decide
  simpa [outgoingFace, outgoingSlot] using h i.2 (s i)

private theorem incoming_slot (s : Occurrence T → Bool) (i : Occurrence T) :
    faceEdge (incomingFace s i) (incomingSlot s i) = i.2 := by
  have h (e : Fin 6) (b : Bool) :
      faceEdge (if b then (edgeFaces e).2 else (edgeFaces e).1)
        (if b then (edgeFaceSlots e).2 else (edgeFaceSlots e).1) = e := by
    cases b <;> fin_cases e <;> decide
  simpa [incomingFace, incomingSlot] using h i.2 (s i)

private theorem face_injective (f : Fin 4) : Function.Injective (faceEdge f) := by
  fin_cases f <;> decide

private theorem slot_cases (r : Occurrence T → Bool) (x : T × Fin 4) (n : Fin 3) :
    let i : Occurrence T := (x.1, faceEdge x.2 n)
    (x.2 = outgoingFace r i ∧ n = outgoingSlot r i) ∨
      (x.2 = incomingFace r i ∧ n = incomingSlot r i) := by
  dsimp
  rcases x with ⟨t, f⟩
  cases hr : r (t, faceEdge f n) <;>
    fin_cases f <;> fin_cases n <;>
    simp [outgoingFace, incomingFace, outgoingSlot, incomingSlot,
      edgeFaces, edgeFaceSlots, faceEdge]

-- The actual face and actual slot of every generator are retained in this law.
theorem port_next_or_prev [Fintype T] (P : RawFacePairing T) (s : Orientation P)
    (x : T × Fin 4) (n : Fin 3) :
    let i : Occurrence T := (x.1, faceEdge x.2 n)
    let j : Occurrence T :=
      ((P.facePair x).1, faceEdge (P.facePair x).2 (P.faceMap x n))
    ((x.2 = outgoingFace s.reversed i ∧ n = outgoingSlot s.reversed i) ∧
      j = s.next i ∧
      P.facePair x = (j.1, incomingFace s.reversed j) ∧
      P.faceMap x n = incomingSlot s.reversed j) ∨
    ((x.2 = incomingFace s.reversed i ∧ n = incomingSlot s.reversed i) ∧
      j = s.next.symm i ∧
      P.facePair x = ((s.next.symm i).1, outgoingFace s.reversed (s.next.symm i)) ∧
      P.faceMap x n = outgoingSlot s.reversed (s.next.symm i)) := by
  let i : Occurrence T := (x.1, faceEdge x.2 n)
  let j : Occurrence T :=
    ((P.facePair x).1, faceEdge (P.facePair x).2 (P.faceMap x n))
  have hpair (x : T × Fin 4) : P.facePair (P.facePair x) = x := by
    have h := congrArg (fun f : Equiv.Perm (T × Fin 4) => f x) P.pairInvolutive
    simpa using h
  rcases slot_cases s.reversed x n with hout | hin
  · have hjnext : j = s.next i := by
      change j = rawNext P.facePair P.faceMap s.reversed i
      symm
      simp only [rawNext, i, j]
      rw [← hout.1, ← hout.2]
    have hsource : (i.1, outgoingFace s.reversed i) = x :=
      Prod.ext rfl hout.1.symm
    have hface : (P.facePair x).2 = incomingFace s.reversed j := by
      have h := s.entersFace i
      change incomingFace s.reversed (s.next i) =
        (P.facePair (i.1, outgoingFace s.reversed i)).2 at h
      rw [← hjnext, hsource] at h
      exact h.symm
    have hslot : P.faceMap x n = incomingSlot s.reversed j := by
      apply face_injective (P.facePair x).2
      calc
        faceEdge (P.facePair x).2 (P.faceMap x n) = j.2 := rfl
        _ = faceEdge (P.facePair x).2 (incomingSlot s.reversed j) := by
          rw [hface]
          exact (incoming_slot s.reversed j).symm
    exact Or.inl ⟨hout, hjnext, Prod.ext rfl hface, hslot⟩
  · let k : Occurrence T := s.next.symm i
    have hki : s.next k = i := s.next.apply_symm_apply i
    let source : T × Fin 4 := (k.1, outgoingFace s.reversed k)
    have hpaired : P.facePair source = (i.1, incomingFace s.reversed i) := by
      apply Prod.ext
      · have h := congrArg (fun z : Occurrence T => z.1) hki
        change (P.facePair source).1 = i.1 at h
        exact h
      · have h := s.entersFace k
        change incomingFace s.reversed (s.next k) =
          (P.facePair (k.1, outgoingFace s.reversed k)).2 at h
        rw [hki] at h
        exact h.symm
    have hx : x = P.facePair source := by
      apply Prod.ext
      · exact (congrArg Prod.fst hpaired).symm
      · exact hin.1.trans (congrArg Prod.snd hpaired).symm
    have hedge :
        faceEdge (P.facePair source).2
          (P.faceMap source (outgoingSlot s.reversed k)) = i.2 := by
      have h := congrArg (fun z : Occurrence T => z.2) hki
      change faceEdge (P.facePair source).2
        (P.faceMap source (outgoingSlot s.reversed k)) = i.2 at h
      exact h
    have hn : P.faceMap source (outgoingSlot s.reversed k) = n := by
      apply face_injective x.2
      calc
        faceEdge x.2 (P.faceMap source (outgoingSlot s.reversed k)) =
            faceEdge (P.facePair source).2
              (P.faceMap source (outgoingSlot s.reversed k)) := by rw [hx]
        _ = i.2 := hedge
        _ = faceEdge x.2 n := rfl
    have hback : P.faceMap x n = outgoingSlot s.reversed k := by
      rw [hx, ← hn]
      exact P.mapInverse source (outgoingSlot s.reversed k)
    have hjk : j = k := by
      apply Prod.ext
      · change (P.facePair x).1 = k.1
        rw [hx, hpair]
      · change faceEdge (P.facePair x).2 (P.faceMap x n) = k.2
        rw [hback, hx, hpair]
        exact outgoing_slot s.reversed k
    refine Or.inr ⟨hin, hjk, ?_, hback⟩
    change P.facePair x = source
    rw [hx, hpair]

theorem next_edgeStep [Fintype T] (P : RawFacePairing T) (s : Orientation P)
    (i : Occurrence T) : P.edgeStep i (s.next i) := by
  refine ⟨(i.1, outgoingFace s.reversed i), outgoingSlot s.reversed i, ?_, rfl⟩
  exact Prod.ext rfl (outgoing_slot s.reversed i).symm

theorem next_preserves_label [Fintype T] (P : RawFacePairing T) (s : Orientation P)
    (i : Occurrence T) :
    P.edgeLabel (s.next i).1 (s.next i).2 = P.edgeLabel i.1 i.2 := by
  apply Eq.symm
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ (next_edgeStep P s i)

theorem edgeStep_sameCycle [Fintype T] (P : RawFacePairing T) (s : Orientation P)
    (i j : Occurrence T) (h : P.edgeStep i j) : s.next.SameCycle i j := by
  rcases h with ⟨x, n, rfl, rfl⟩
  rcases port_next_or_prev P s x n with ⟨_, hj, _, _⟩ | ⟨_, hj, _, _⟩
  · rw [hj]
    exact (Equiv.Perm.sameCycle_apply_right).mpr (Equiv.Perm.SameCycle.refl s.next _)
  · rw [hj]
    have h : s.next.SameCycle (s.next.symm (x.1, faceEdge x.2 n))
        (s.next (s.next.symm (x.1, faceEdge x.2 n))) :=
      (Equiv.Perm.sameCycle_apply_right).mpr (Equiv.Perm.SameCycle.refl s.next _)
    simpa using h.symm

theorem eqvGen_sameCycle [Fintype T] (P : RawFacePairing T) (s : Orientation P)
    (i j : Occurrence T) :
    Relation.EqvGen P.edgeStep i j ↔ s.next.SameCycle i j := by
  constructor
  · intro h
    induction h with
    | rel a b h => exact edgeStep_sameCycle P s a b h
    | refl a => exact Equiv.Perm.SameCycle.refl s.next a
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ hab hbc => exact hab.trans hbc
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hpow (n : ℕ) : ∀ z : Occurrence T,
        P.edgeLabel ((s.next ^ n) z).1 ((s.next ^ n) z).2 = P.edgeLabel z.1 z.2 := by
      induction n with
      | zero => intro z; simp
      | succ n ih =>
          intro z
          rw [pow_succ, Equiv.Perm.mul_apply, ih (s.next z), next_preserves_label P s z]
    apply Quotient.exact (s := Relation.EqvGen.setoid P.edgeStep) (a := i) (b := j)
    change P.edgeLabel i.1 i.2 = P.edgeLabel j.1 j.2
    rw [← hn]
    exact (hpow n i).symm

theorem sameCycle_iff_label [Fintype T] (P : RawFacePairing T) (s : Orientation P)
    (i j : Occurrence T) :
    s.next.SameCycle i j ↔ P.edgeLabel i.1 i.2 = P.edgeLabel j.1 j.2 := by
  rw [← eqvGen_sameCycle P s i j]
  constructor
  · intro h
    change Quotient.mk (Relation.EqvGen.setoid P.edgeStep) i =
      Quotient.mk (Relation.EqvGen.setoid P.edgeStep) j
    exact Quotient.sound (s := Relation.EqvGen.setoid P.edgeStep) h
  · intro h
    change Quotient.mk (Relation.EqvGen.setoid P.edgeStep) i =
      Quotient.mk (Relation.EqvGen.setoid P.edgeStep) j at h
    exact Quotient.exact (s := Relation.EqvGen.setoid P.edgeStep) h

def fiber (P : RawFacePairing T) (e : P.GlobalEdge) : Set (Occurrence T) :=
  {i | P.edgeLabel i.1 i.2 = e}

theorem whole_fiber_one_cycle [Fintype T] (P : RawFacePairing T)
    (s : Orientation P) (e : P.GlobalEdge) : s.next.IsCycleOn (fiber P e) := by
  refine ⟨⟨?_, s.next.injective.injOn, ?_⟩, ?_⟩
  · intro i hi
    exact (next_preserves_label P s i).trans hi
  · intro i hi
    refine ⟨s.next.symm i, ?_, s.next.apply_symm_apply i⟩
    have h := next_preserves_label P s (s.next.symm i)
    rw [s.next.apply_symm_apply] at h
    exact h.symm.trans hi
  · intro i hi j hj
    exact (sameCycle_iff_label P s i j).mpr (hi.trans hj.symm)

noncomputable def fiberFinset [Fintype T] (P : RawFacePairing T) (i : Occurrence T) :
    Finset (Occurrence T) := by
  classical
  exact Finset.univ.filter (fun j => P.edgeLabel j.1 j.2 = P.edgeLabel i.1 i.2)

theorem fiberFinset_cycle [Fintype T] (P : RawFacePairing T) (s : Orientation P)
    (i : Occurrence T) : s.next.IsCycleOn (fiberFinset P i : Set (Occurrence T)) := by
  classical
  simpa [fiberFinset, fiber] using whole_fiber_one_cycle P s (P.edgeLabel i.1 i.2)

theorem base_mem_fiberFinset [Fintype T] (P : RawFacePairing T) (i : Occurrence T) :
    i ∈ fiberFinset P i := by
  classical
  simp [fiberFinset]

noncomputable def powerEnumeration [Fintype T] (P : RawFacePairing T)
    (s : Orientation P) (i : Occurrence T) :
    Fin (fiberFinset P i).card ≃ fiber P (P.edgeLabel i.1 i.2) := by
  classical
  let f : Fin (fiberFinset P i).card → fiber P (P.edgeLabel i.1 i.2) := fun n =>
    ⟨(s.next ^ n.val) i, by
      have h := (sameCycle_iff_label P s i ((s.next ^ n.val) i)).mp
        ((Equiv.Perm.sameCycle_pow_right).mpr
          (Equiv.Perm.SameCycle.refl s.next i))
      exact h.symm⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Fin.ext
    exact (fiberFinset_cycle P s i).injOn_pow_apply (base_mem_fiberFinset P i)
      a.isLt b.isLt (congrArg Subtype.val hab)
  · intro j
    have hj' : P.edgeLabel j.val.1 j.val.2 = P.edgeLabel i.1 i.2 := j.property
    have hj : j.val ∈ fiberFinset P i := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩
    obtain ⟨n, hn, hnj⟩ :=
      (fiberFinset_cycle P s i).exists_pow_eq (base_mem_fiberFinset P i) hj
    exact ⟨⟨n, hn⟩, Subtype.ext hnj⟩

theorem powerEnumeration_apply [Fintype T] (P : RawFacePairing T)
    (s : Orientation P) (i : Occurrence T) (n : Fin (fiberFinset P i).card) :
    (powerEnumeration P s i n).val = (s.next ^ n.val) i := rfl

theorem power_card_returns [Fintype T] (P : RawFacePairing T)
    (s : Orientation P) (i : Occurrence T) :
    (s.next ^ (fiberFinset P i).card) i = i :=
  (fiberFinset_cycle P s i).pow_card_apply (base_mem_fiberFinset P i)

theorem powerEnumeration_next [Fintype T] (P : RawFacePairing T)
    (s : Orientation P) (i : Occurrence T) (n : Fin (fiberFinset P i).card) :
    s.next (powerEnumeration P s i n).val =
      (powerEnumeration P s i
        ⟨(n.val + 1) % (fiberFinset P i).card,
          Nat.mod_lt _ (Finset.card_pos.mpr ⟨i, base_mem_fiberFinset P i⟩)⟩).val := by
  rw [powerEnumeration_apply, powerEnumeration_apply]
  have h : s.next ((s.next ^ n.val) i) = (s.next ^ (n.val + 1)) i := by
    rw [pow_succ', Equiv.Perm.mul_apply]
  rw [h]
  exact ((fiberFinset_cycle P s i).pow_apply_eq_pow_apply
    (base_mem_fiberFinset P i)).mpr (Nat.mod_modEq _ _).symm

theorem period_iff_card_dvd [Fintype T] (P : RawFacePairing T)
    (s : Orientation P) (i : Occurrence T) (n : ℕ) :
    (s.next ^ n) i = i ↔ (fiberFinset P i).card ∣ n :=
  (fiberFinset_cycle P s i).pow_apply_eq (base_mem_fiberFinset P i)

theorem singleton_successor_fixed [Fintype T] (P : RawFacePairing T)
    (s : Orientation P) (i : Occurrence T) (hm : (fiberFinset P i).card = 1) :
    s.next i = i := by
  have h := power_card_returns P s i
  simpa [hm] using h

theorem two_successor_returns [Fintype T] (P : RawFacePairing T)
    (s : Orientation P) (i : Occurrence T) (hm : (fiberFinset P i).card = 2) :
    s.next (s.next i) = i ∧ s.next i ≠ i := by
  constructor
  · have h := power_card_returns P s i
    simpa [hm, pow_succ, Equiv.Perm.mul_apply] using h
  · intro h
    have hdiv : (fiberFinset P i).card ∣ 1 :=
      (period_iff_card_dvd P s i 1).mp (by simpa using h)
    norm_num [hm] at hdiv

end D5.S3.Geometry.Gluing.RawFaceCycleCandidate
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.chooseOrientation,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.port_next_or_prev,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.next_edgeStep,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.next_preserves_label,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.edgeStep_sameCycle,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.eqvGen_sameCycle,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.sameCycle_iff_label,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.whole_fiber_one_cycle,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.fiberFinset_cycle,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.powerEnumeration,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.powerEnumeration_apply,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.power_card_returns,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.powerEnumeration_next,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.period_iff_card_dvd,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.singleton_successor_fixed,
      ``D5.S3.Geometry.Gluing.RawFaceCycleCandidate.two_successor_returns] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1181 uncolored cycle target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1181 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1181 CHECKED {name} axioms={axioms}"
