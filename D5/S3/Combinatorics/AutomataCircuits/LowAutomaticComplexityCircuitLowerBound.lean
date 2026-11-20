/- GID: D5/S3/Combinatorics/AutomataCircuits/LowAutomaticComplexityCircuitLowerBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/AutomataCircuits/LowAutomaticComplexityCircuitLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Low automatic complexity and its complement defeat bounded-depth circuits. -/

/-
proof_shape: per-declaration rows below; definitions carry no theorem novelty claim.
escape_witness: none; admission rests on the settling result.
admission_basis: open-problem-resolution (#26742; Proved)
Direct frozen dependencies: B = D5/S3/Observer/Separation/BooleanRankThreeK4.bit2; statement_id = sha256:53632b1f9446d59ef22ddbbb7d61d5c3f0f40af1c067d7b9c67e6b47379da9cb.
Each row gives name | proof_shape | frozen dependencies | escape_witness | consumers.
B denotes that exact declaration identity; none denotes no frozen D5 dependency.
Definition rows describe constructions, not additional mathematical content.
claim | bind-only | none | none | claimOfSparse, result
constantNFA | bind-only | none | none | constantNFAPathMem, constantNFAReplicatePath, realizesConstantWord
constantNFAPathMem | content | none | constantNFAPathMem | realizesConstantWord
constantNFAReplicatePath | content | none | constantNFAReplicatePath | realizesConstantWord
realizesConstantWord | content | none | realizesConstantWord | constantWordMemLq
ANeLeOfRealizes | bind-only | none | none | constantWordMemLq
constantWordMemLq | content | none | constantWordMemLq | lowLanguageSparse
pathState | bind-only | none | none | pathStateZero, pathStateLength, pathSegment, exactLoopsCommute, loopTripleShort, exactEqualLoopPump, closeEqualLoops, noRepeatsStateBound
pathStateZero | bind-only | none | none | pathSegment, exactLoopsCommute, exactEqualLoopPump
pathStateLength | content | none | pathStateLength | exactLoopsCommute, exactEqualLoopPump
pathAppend | bind-only | none | none | exactLoopsCommute, exactEqualLoopPump
pathSegment | content | none | pathSegment | exactLoopsCommute, exactEqualLoopPump
repeatedFactor | bind-only | none | none | repeatedOfCommuting, loopTripleShort, repeatedOfOverlap, closeEqualLoops, noRepeatsStateBound, lowImpliesRepeat, repeatedCount, lowLanguageSparse
segmentLength | bind-only | none | none | loopTripleShort, exactEqualLoopPump, closeEqualLoops
segmentAppend | bind-only | none | none | segmentFour, exactEqualLoopPump, closeEqualLoops
segmentFull | bind-only | none | none | segmentFour, exactEqualLoopPump, closeEqualLoops
segmentFour | bind-only | none | none | exactLoopsCommute, loopTripleShort
exactLoopsCommute | content | none | exactLoopsCommute | loopTripleShort
repeatedOfCommuting | bind-only | none | none | loopTripleShort
loopTripleShort | content | none | loopTripleShort | noRepeatsStateBound
exactEqualLoopPump | content | none | exactEqualLoopPump | closeEqualLoops
repeatedOfOverlap | bind-only | none | none | closeEqualLoops
closeEqualLoops | content | none | closeEqualLoops | noRepeatsStateBound
diameterCardLe | bind-only | none | none | sequenceBound
sequenceBound | content | none | sequenceBound | noRepeatsStateBound
noRepeatsStateBound | content | none | noRepeatsStateBound | lowImpliesRepeat
lowImpliesRepeat | content | none | lowImpliesRepeat | lowLanguageSparse
deleteBlockIndex | bind-only | none | none | deleteBlockInjective, fixedRepeatCount
repeatedCoordinates | bind-only | none | none | deleteBlockInjective
deleteBlockInjective | content | none | deleteBlockInjective | fixedRepeatCount
fixedRepeatCount | content | none | fixedRepeatCount | repeatedCount
repeatedCount | content | none | repeatedCount | lowLanguageSparse
existsSparseScale | bind-only | none | none | lowLanguageSparse
lowLanguageSparse | content | none | lowLanguageSparse | result
claimOfSparse | content | B | claimOfSparse | result
result | content | B | result | terminal settling result
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30628
-/

import D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

/-! Arbitrary-alphabet lower bounds for low exact automatic complexity. -/

open D5.S3.Combinatorics.AutomataCircuits.ExactNFACircuitInfrastructure

namespace D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound


def claim : Prop :=
  ∀ (Alphabet : Type) (_ : Fintype Alphabet), 2 ≤ Fintype.card Alphabet →
    complexityTotal Alphabet ∧
    ∀ q : ℚ, 0 < q → q < (1 : ℚ) / 2 →
      (∀ (p : ℕ), p.Prime → ∀ e : Alphabet → ZMod p, Function.Injective e →
        ¬ arithmeticRecognizable p e (Lq (Alphabet := Alphabet) q) ∧
        ¬ arithmeticRecognizable p e ((Lq (Alphabet := Alphabet) q)ᶜ)) ∧
      (∀ (t : ℕ) (e : Alphabet → Fin t → Bool), Function.Injective e →
        ¬ booleanRecognizable t e (Lq (Alphabet := Alphabet) q) ∧
        ¬ booleanRecognizable t e ((Lq (Alphabet := Alphabet) q)ᶜ))

private def constantNFA {Alphabet : Type} (a : Alphabet) : NFA Alphabet (Fin 1) where
  step _ b := {t | b = a}
  start := {0}
  accept := {0}

private theorem constantNFAPathMem {Alphabet : Type} (a : Alphabet) {y : List Alphabet}
    {s t : Fin 1} (p : (constantNFA a).Path s t y) : ∀ b ∈ y, b = a := by
  induction p with
  | nil => simp
  | cons u s t b y h p ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h
    · exact ih c hc

private theorem constantNFAReplicatePath {Alphabet : Type} (a : Alphabet) (n : ℕ) :
    Nonempty ((constantNFA a).Path 0 0 (List.replicate n a)) := by
  induction n with
  | zero => exact ⟨.nil 0⟩
  | succ n ih =>
    obtain ⟨p⟩ := ih
    exact ⟨.cons 0 0 0 a _ rfl p⟩

private theorem realizesConstantWord {Alphabet : Type} (a : Alphabet) (n : ℕ) :
    realizesStateCount (List.replicate n a) 1 := by
  refine ⟨constantNFA a, 0, rfl, ?_, ?_⟩
  · exact NFA.accepts_iff_exists_path.mpr
      ⟨0, rfl, 0, rfl, constantNFAReplicatePath a n⟩
  · intro y hlen hy
    obtain ⟨s, hs, t, ht, ⟨p⟩⟩ := NFA.accepts_iff_exists_path.mp hy
    have h := List.eq_replicate_length.mpr (constantNFAPathMem a p)
    simpa only [hlen, List.length_replicate] using h

private theorem ANeLeOfRealizes {Alphabet : Type} (w : List Alphabet) (k : ℕ)
    (hk : realizesStateCount w k) : A_Ne w ≤ (k : ℕ∞) :=
  sInf_le ⟨k, rfl, hk⟩

private theorem constantWordMemLq {Alphabet : Type} (a : Alphabet) (n : ℕ) (q : ℚ)
    (hq : 1 < q * (n : ℚ)) : List.replicate n a ∈ Lq q := by
  classical
  obtain ⟨k, hk, hmin⟩ := minimumAttained (List.replicate n a) ⟨1, realizesConstantWord a n⟩
  have hkone : k ≤ 1 := by
    have hle := ANeLeOfRealizes (List.replicate n a) 1 (realizesConstantWord a n)
    rw [hmin] at hle
    exact_mod_cast hle
  refine ⟨k, hmin, ?_⟩
  simp only [List.length_replicate]
  exact lt_of_le_of_lt (by exact_mod_cast hkone) hq

end D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound

namespace D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound
variable {A Q : Type} {M : NFA A Q}

private def pathState {s t : Q} {w : List A} (p : M.Path s t w) : ℕ → Q :=
  match p with
  | .nil s => fun _ => s
  | .cons _ s _ _ _ _ p => fun i => match i with | 0 => s | i+1 => pathState p i

@[simp] private theorem pathStateZero {s t : Q} {w : List A} (p : M.Path s t w) :
    pathState p 0 = s := by cases p <;> rfl

@[simp] private theorem pathStateLength {s t : Q} {w : List A} (p : M.Path s t w) :
    pathState p w.length = t := by
  induction p with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => exact ih

private noncomputable def pathAppend {s t u : Q} {v w : List A}
    (p : M.Path s t v) (r : M.Path t u w) : M.Path s u (v ++ w) :=
  match p with
  | .nil _ => r
  | .cons t s v a x h p => .cons t s _ a _ h (pathAppend p r)

private theorem pathSegment {s t : Q} {w : List A} (p : M.Path s t w)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ w.length) :
    Nonempty (M.Path (pathState p i) (pathState p j) ((w.drop i).take (j-i))) := by
  induction p generalizing i j with
  | nil s =>
    have hi : i = 0 := by simpa using (hij.trans hj)
    have hzero : j = 0 := by exact Nat.eq_zero_of_le_zero hj
    subst i; subst j
    exact ⟨.nil s⟩
  | cons u s t a w h p ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact ⟨.nil s⟩
      | succ j =>
        obtain ⟨r⟩ := ih 0 j (Nat.zero_le _) (by simpa using hj)
        change Nonempty (M.Path s (pathState p j) (a :: w.take j))
        exact ⟨.cons u s _ a _ h (by simpa using r)⟩
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simpa [pathState] using ih i j (by omega) (by simpa using hj)

private def repeatedFactor (m : ℕ) (w : List A) : Prop :=
  ∃ i j : ℕ, i < j ∧ j + m ≤ w.length ∧ (w.drop i).take m = (w.drop j).take m

end D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound

namespace D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound
variable {A Q : Type} {M : NFA A Q}

@[simp] private theorem segmentLength (w : List A) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ w.length) :
    (List.extract w i j).length = j-i := by
  simp only [List.extract, List.length_take, List.length_drop]
  omega

private theorem segmentAppend (w : List A) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    List.extract w i j ++ List.extract w j k = List.extract w i k := by
  unfold List.extract
  have hsplit : k-i = (j-i)+(k-j) := by omega
  rw [hsplit, List.take_add, List.drop_drop, Nat.add_sub_of_le hij]

@[simp] private theorem segmentFull (w : List A) : List.extract w 0 w.length = w := by
  simp [List.extract]

private theorem segmentFour (w : List A) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hk : k ≤ w.length) :
    List.extract w 0 i ++ List.extract w i j ++ List.extract w j k ++ List.extract w k w.length = w := by
  rw [segmentAppend w (Nat.zero_le _) hij,
    segmentAppend w (Nat.zero_le _) hjk,
    segmentAppend w (Nat.zero_le _) hk, segmentFull]

private theorem exactLoopsCommute {k : ℕ} {M : NFA A (Fin k)} {w : List A}
    (hex : exactlyAccepts M w) {s t : Fin k} (hs : s ∈ M.start) (ht : t ∈ M.accept)
    (p : M.Path s t w) {i j l : ℕ} (hij : i < j) (hjl : j < l) (hl : l ≤ w.length)
    (hijq : pathState p i = pathState p j) (hjlq : pathState p j = pathState p l) :
    List.extract w i j ++ List.extract w j l = List.extract w j l ++ List.extract w i j := by
  obtain ⟨pa⟩ := pathSegment p 0 i (Nat.zero_le _) (by omega)
  obtain ⟨pu⟩ := pathSegment p i j (by omega) (by omega)
  obtain ⟨pv⟩ := pathSegment p j l (by omega) hl
  obtain ⟨pz⟩ := pathSegment p l w.length hl le_rfl
  let a := List.extract w 0 i
  let u := List.extract w i j
  let v := List.extract w j l
  let z := List.extract w l w.length
  have hpv : M.Path (pathState p i) (pathState p i) v := by
    simpa only [v, List.extract, ← hijq, ← hjlq] using pv
  have hpu : M.Path (pathState p i) (pathState p i) u := by
    simpa only [u, List.extract, ← hijq] using pu
  have hpz : M.Path (pathState p i) t z := by
    simpa only [z, List.extract, pathStateLength, ← hjlq, ← hijq] using pz
  have hpa : M.Path s (pathState p i) a := by simpa only [a, List.extract, pathStateZero] using pa
  have hw : a ++ u ++ v ++ z = w := segmentFour w (by omega) (by omega) hl
  have hacc : a ++ v ++ u ++ z ∈ M.accepts := by
    apply NFA.accepts_iff_exists_path.mpr
    refine ⟨s, hs, t, ht, ?_⟩
    exact ⟨by simpa only [List.append_assoc] using pathAppend hpa (pathAppend hpv (pathAppend hpu hpz))⟩
  have heq := hex.2 (a ++ v ++ u ++ z) (by simpa only [← hw, List.length_append] using (show a.length+v.length+u.length+z.length=a.length+u.length+v.length+z.length by omega)) hacc
  have heq' : a ++ (v ++ u) ++ z = a ++ (u ++ v) ++ z := by
    simpa only [List.append_assoc] using heq.trans hw.symm
  exact (List.append_cancel_left (List.append_cancel_right heq')).symm

private theorem repeatedOfCommuting {m : ℕ} (a u v z : List A)
    (hu : 0 < u.length) (hv : 0 < v.length) (hc : u ++ v = v ++ u)
    (hm : m ≤ max u.length v.length) : repeatedFactor m (a ++ u ++ v ++ z) := by
  have aux (u v : List A) (hu : 0 < u.length) (hc : u ++ v = v ++ u)
      (hm : m ≤ v.length) : repeatedFactor m (a ++ u ++ v ++ z) := by
    refine ⟨a.length, a.length+u.length, by omega, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · have hw : a ++ u ++ v ++ z = a ++ v ++ u ++ z := by rw [List.append_assoc a, hc]; simp [List.append_assoc]
      conv_lhs => rw [hw]
      simp only [List.append_assoc, List.drop_append_length]
      rw [← List.drop_drop]
      simp only [List.drop_append_length]
      simp only [List.take_append_of_le_length hm]
  by_cases huv : u.length ≤ v.length
  · exact aux u v hu hc (by simpa [max_eq_right huv] using hm)
  · have h := aux v u hv hc.symm (by simpa [max_eq_left (by omega : v.length ≤ u.length)] using hm)
    have hw : a ++ v ++ u ++ z = a ++ u ++ v ++ z := by rw [List.append_assoc a, ← hc]; simp [List.append_assoc]
    rwa [hw] at h

end D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound

namespace D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound
variable {A : Type}

private theorem loopTripleShort {m k : ℕ} {M : NFA A (Fin k)} {w : List A}
    (hex : exactlyAccepts M w) {s t : Fin k} (hs : s ∈ M.start) (ht : t ∈ M.accept)
    (p : M.Path s t w) (hfree : ¬ repeatedFactor m w)
    {i j l : ℕ} (hij : i < j) (hjl : j < l) (hl : l ≤ w.length)
    (hijq : pathState p i = pathState p j) (hjlq : pathState p j = pathState p l) :
    j-i < m ∧ l-j < m := by
  have hc := exactLoopsCommute hex hs ht p hij hjl hl hijq hjlq
  have hi : i ≤ j := by exact Nat.le_of_succ_le hij
  have hj : j ≤ l := by exact Nat.le_of_succ_le hjl
  have hijlen := segmentLength w hi (hj.trans hl)
  have hjllen := segmentLength w hj hl
  by_contra h
  have hm : m ≤ max (List.extract w i j).length (List.extract w j l).length := by
    rw [hijlen, hjllen]; omega
  have hr := repeatedOfCommuting (List.extract w 0 i) (List.extract w i j)
    (List.extract w j l) (List.extract w l w.length) (by rw [hijlen]; omega)
    (by rw [hjllen]; omega) hc hm
  rw [segmentFour w hi hj hl] at hr
  exact hfree hr

private theorem exactEqualLoopPump {k : ℕ} {M : NFA A (Fin k)} {w : List A}
    (hex : exactlyAccepts M w) {s t : Fin k} (hs : s ∈ M.start) (ht : t ∈ M.accept)
    (p : M.Path s t w) {i j l r : ℕ} (hij : i < j) (hjl : j ≤ l)
    (hlr : l < r) (hr : r ≤ w.length)
    (hijq : pathState p i = pathState p j) (hlrq : pathState p l = pathState p r)
    (hlen : j-i = r-l) :
    List.extract w j l ++ List.extract w l r = List.extract w i j ++ List.extract w j l := by
  obtain ⟨pa⟩ := pathSegment p 0 i (Nat.zero_le _) (by omega)
  obtain ⟨pu⟩ := pathSegment p i j (by omega) (by omega)
  obtain ⟨py⟩ := pathSegment p j l hjl (by omega)
  obtain ⟨pz⟩ := pathSegment p r w.length hr le_rfl
  let a := List.extract w 0 i
  let u := List.extract w i j
  let y := List.extract w j l
  let v := List.extract w l r
  let z := List.extract w r w.length
  have hpU : M.Path (pathState p j) (pathState p j) u := by
    simpa only [u, List.extract, hijq] using pu
  have hpA : M.Path s (pathState p j) a := by
    simpa only [a, List.extract, pathStateZero, hijq] using pa
  have hpY : M.Path (pathState p j) (pathState p r) y := by
    simpa only [y, List.extract, hlrq] using py
  have hpZ : M.Path (pathState p r) t z := by
    simpa only [z, List.extract, pathStateLength] using pz
  have hw : a ++ u ++ y ++ v ++ z = w := by
    dsimp only [a, u, y, v, z]
    rw [segmentAppend w (i := 0) (j := i) (k := j) (by omega) (by omega),
      segmentAppend w (i := 0) (j := j) (k := l) (by omega) hjl,
      segmentAppend w (i := 0) (j := l) (k := r) (by omega) (by omega),
      segmentAppend w (i := 0) (j := r) (k := w.length) (by omega) hr, segmentFull]
  have huv : u.length = v.length := by
    dsimp [u, v]
    rw [segmentLength w (by omega) (by omega), segmentLength w (by omega) hr]
    exact hlen
  have hacc : a ++ u ++ u ++ y ++ z ∈ M.accepts := by
    apply NFA.accepts_iff_exists_path.mpr
    refine ⟨s, hs, t, ht, ?_⟩
    exact ⟨by simpa only [List.append_assoc] using pathAppend hpA (pathAppend hpU (pathAppend hpU (pathAppend hpY hpZ)))⟩
  have heq := hex.2 (a ++ u ++ u ++ y ++ z) (by
    rw [← hw]; simp only [List.length_append]; omega) hacc
  have heq' : (a ++ u) ++ (u ++ y) ++ z = (a ++ u) ++ (y ++ v) ++ z := by
    simpa only [List.append_assoc] using heq.trans hw.symm
  exact (List.append_cancel_left (List.append_cancel_right heq')).symm

private theorem repeatedOfOverlap {m : ℕ} (a u y v z : List A) (hu : 0 < u.length)
    (hlen : u.length = v.length) (hc : y ++ v = u ++ y)
    (hm : m ≤ u.length + y.length) : repeatedFactor m (a ++ u ++ y ++ v ++ z) := by
  refine ⟨a.length, a.length+u.length, by omega, ?_, ?_⟩
  · simp only [List.length_append]; omega
  · have hl : m ≤ (u ++ y).length := by simpa using hm
    have hr : m ≤ (y ++ v).length := by exact le_of_le_of_eq hl (congrArg List.length (id (Eq.symm hc)))
    simp only [List.append_assoc, List.drop_append_length]
    rw [← List.drop_drop]
    simp only [List.drop_append_length]
    have h1 : (u ++ (y ++ (v ++ z))).take m = (u ++ y).take m := by
      simpa only [List.append_assoc] using List.take_append_of_le_length (l₂ := v ++ z) hl
    have h2 : (y ++ (v ++ z)).take m = (y ++ v).take m := by
      simpa only [List.append_assoc] using List.take_append_of_le_length (l₂ := z) hr
    rw [h1, h2, hc]

end D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound

namespace D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound
open Finset

private theorem closeEqualLoops {A : Type} {m k : ℕ} {M : NFA A (Fin k)} {w : List A}
    (hex : exactlyAccepts M w) {s t : Fin k} (hs : s ∈ M.start) (ht : t ∈ M.accept)
    (p : M.Path s t w) (hfree : ¬ repeatedFactor m w)
    {i j l r : ℕ} (hij : i < j) (hlr : l < r) (hjr : j < r) (hr : r ≤ w.length)
    (hijq : pathState p i = pathState p j) (hlrq : pathState p l = pathState p r)
    (hlen : j-i = r-l) (hshort : j-i < m) : r-j < m := by
  by_contra h
  have hjl : j ≤ l := by omega
  have hc := exactEqualLoopPump hex hs ht p hij hjl hlr hr hijq hlrq hlen
  have hi : i ≤ j := by exact Nat.le_of_succ_le hij
  have hl : l ≤ r := by exact Nat.le_of_succ_le hlr
  have h := repeatedOfOverlap (m := m) (List.extract w 0 i) (List.extract w i j) (List.extract w j l)
    (List.extract w l r) (List.extract w r w.length)
    (by rw [segmentLength w hi (by omega)]; omega)
    (by rw [segmentLength w hi (by omega), segmentLength w hl hr]; exact hlen)
    hc (by rw [segmentLength w hi (by omega), segmentLength w hjl (by omega)]; omega)
  have hw : List.extract w 0 i ++ List.extract w i j ++ List.extract w j l ++ List.extract w l r ++ List.extract w r w.length = w := by
    rw [segmentAppend w (by omega) hi, segmentAppend w (by omega) hjl,
      segmentAppend w (by omega) hl, segmentAppend w (by omega) hr, segmentFull]
  rw [hw] at h
  exact hfree h

private theorem diameterCardLe (S : Finset ℕ) (m : ℕ)
    (hclose : ∀ i ∈ S, ∀ j ∈ S, i < j → j-i < m) (hm : 0 < m) : S.card ≤ m := by
  classical
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    have ha : a ∈ S := S.min'_mem hS
    have hsub : S ⊆ Finset.Ico a (a+m) := by
      intro j hj
      have haj : a ≤ j := S.min'_le _ hj
      have hlt : j < a+m := by
        by_cases heq : a=j
        · omega
        · have := hclose a ha j hj (by omega); omega
      exact Finset.mem_Ico.mpr ⟨haj,hlt⟩
    simpa using (Finset.card_le_card hsub)
  · simp_all [Finset.not_nonempty_iff_eq_empty]

private theorem sequenceBound {n k m : ℕ} (q : ℕ → Fin k) (hm : 0 < m)
    (htriple : ∀ i j l, i < j → j < l → l ≤ n → q i = q j → q j = q l → l-j < m)
    (hclose : ∀ i j l r, i < j → l < r → j < r → r ≤ n →
      q i = q j → q l = q r → j-i = r-l → j-i < m → r-j < m) :
    n+1 ≤ 2*k + m*m := by
  classical
  let late : ℕ → Prop := fun l => ∃ i j, i < j ∧ j < l ∧ q i=q j ∧ q j=q l
  let E := (Finset.range (n+1)).filter late
  let B := (Finset.range (n+1)).filter (fun j => ¬late j)
  have hB : B.card ≤ 2*k := by
    let f : ℕ → Fin k × Bool := fun j => (q j, decide (∃ i, i < j ∧ q i=q j))
    have hinj : Set.InjOn f B := by
      intro j hj l hl heq
      have hjnot : ¬late j := (Finset.mem_filter.mp hj).2
      have hlnot : ¬late l := (Finset.mem_filter.mp hl).2
      have hq : q j=q l := congrArg Prod.fst heq
      have hb : (∃ i, i < j ∧ q i=q j) ↔ (∃ i, i < l ∧ q i=q l) := by
        simpa only [f, Prod.mk.injEq, decide_eq_decide] using (congrArg Prod.snd heq)
      by_contra hne
      rcases lt_or_gt_of_ne hne with hjl | hlj
      · obtain ⟨i,hij,hiq⟩ := hb.mpr ⟨j,hjl,hq⟩
        exact hlnot ⟨i,j,hij,hjl,hiq,hq⟩
      · obtain ⟨i,hil,hiq⟩ := hb.mp ⟨l,hlj,hq.symm⟩
        exact hjnot ⟨i,l,hil,hlj,hiq,hq.symm⟩
    have hh := Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
    simpa [Nat.mul_comm] using hh
  have hchoose : ∀ l ∈ E, ∃ j, j < l ∧ q j=q l ∧ l-j < m := by
    intro l hl
    obtain ⟨i,j,hij,hjl,hijq,hjlq⟩ := (Finset.mem_filter.mp hl).2
    exact ⟨j,hjl,hjlq,htriple i j l hij hjl (by have := (Finset.mem_filter.mp hl).1; simpa using this) hijq hjlq⟩
  let prev : ℕ → ℕ := fun l => if hl : l ∈ E then Classical.choose (hchoose l hl) else 0
  have hprev (l : ℕ) (hl : l ∈ E) : prev l < l ∧ q (prev l)=q l ∧ l-prev l < m := by
    simpa only [prev, dif_pos hl] using Classical.choose_spec (hchoose l hl)
  let color : ℕ → ℕ := fun l => l-prev l
  have hE : E.card ≤ m*m := by
    have hmap : ∀ l ∈ E, color l ∈ Finset.range m := by
      intro l hl; exact Finset.mem_range.mpr (hprev l hl).2.2
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      ∑ c ∈ Finset.range m, (E.filter (fun l => color l=c)).card ≤ ∑ _c ∈ Finset.range m, m := by
        apply Finset.sum_le_sum
        intro c hc
        apply diameterCardLe _ m _ hm
        intro j hj r hr hjr
        have hjE := (Finset.mem_filter.mp hj).1
        have hrE := (Finset.mem_filter.mp hr).1
        have hjc := (Finset.mem_filter.mp hj).2
        have hrc := (Finset.mem_filter.mp hr).2
        have hjp := hprev j hjE
        have hrp := hprev r hrE
        exact hclose (prev j) j (prev r) r hjp.1 hrp.1 hjr
          (by have := (Finset.mem_filter.mp hrE).1; simpa using this)
          hjp.2.1 hrp.2.1 (by dsimp [color] at hjc hrc; omega) hjp.2.2
      _ = m*m := by simp
  have hsum : E.card+B.card=n+1 := by
    simpa only [E, B, Finset.card_range] using Finset.card_filter_add_card_filter_not (s := Finset.range (n+1)) late
  omega

end D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound

namespace D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound
open Finset
attribute [local instance] Classical.propDecidable
variable {A : Type}

private theorem noRepeatsStateBound {m k : ℕ} (hm : 0 < m) {w : List A}
    (hreal : realizesStateCount w k) (hfree : ¬ repeatedFactor m w) :
    w.length+1 ≤ 2*k+m*m := by
  obtain ⟨M,initial,hstart,hex⟩ := hreal
  obtain ⟨s,hs,t,ht,⟨p⟩⟩ := NFA.accepts_iff_exists_path.mp hex.1
  apply sequenceBound (pathState p) hm
  · intro i j l hij hjl hl hijq hjlq
    exact (loopTripleShort hex hs ht p hfree hij hjl hl hijq hjlq).2
  · intro i j l r hij hlr hjr hr hijq hlrq hlen hshort
    exact closeEqualLoops hex hs ht p hfree hij hlr hjr hr hijq hlrq hlen hshort

private theorem lowImpliesRepeat {m : ℕ} (hm : 0 < m) {q : ℚ} {w : List A}
    (hw : w ∈ Lq q) (hsize : (m*m : ℕ) ≤ (1-2*q)*(w.length : ℚ)) :
    repeatedFactor m w := by
  obtain ⟨k,hk,hkq⟩ := hw
  obtain ⟨l,hl,hlmin⟩ := minimumAttained w ⟨w.length+1,realizesWordLengthSucc w⟩
  have hlk : l=k := by exact_mod_cast (hlmin.symm.trans hk)
  subst l
  by_contra hfree
  have hbound := noRepeatsStateBound hm hl hfree
  have hboundQ : (w.length : ℚ)+1 ≤ 2*(k : ℚ)+(m*m : ℕ) := by exact_mod_cast hbound
  nlinarith

private def deleteBlockIndex {n m : ℕ} (j : ℕ) (hj : j+m ≤ n) (i : Fin (n-m)) : Fin n :=
  ⟨if i.val < j then i.val else i.val+m, by split <;> omega⟩

private theorem repeatedCoordinates {n m i j : ℕ} (x : Fin n → A)
    (hij : i < j) (hjm : j+m ≤ n)
    (hrep : ((List.ofFn x).drop i).take m = ((List.ofFn x).drop j).take m)
    (a : ℕ) (ha : a < m) :
    x ⟨i+a,by omega⟩ = x ⟨j+a,by omega⟩ := by
  have h := congrArg (fun w : List A => w[a]?) hrep
  simp only [List.getElem?_take, if_pos ha, List.getElem?_drop] at h
  simpa only [List.getElem?_ofFn, dif_pos (show i+a < n by omega), dif_pos (show j+a < n by omega), Option.some.injEq] using h

private theorem deleteBlockInjective {n m i j : ℕ} (hij : i < j) (hjm : j+m ≤ n) :
    Set.InjOn (fun x : Fin n → A => x ∘ deleteBlockIndex j hjm)
      {x | ((List.ofFn x).drop i).take m = ((List.ofFn x).drop j).take m} := by
  intro x hx y hy hxy
  have hall : ∀ a : ℕ, ∀ ha : a < n, x ⟨a,ha⟩=y ⟨a,ha⟩ := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro ha
      by_cases hb : j ≤ a ∧ a < j+m
      · have hx' := repeatedCoordinates x hij hjm hx (a-j) (by omega)
        have hy' := repeatedCoordinates y hij hjm hy (a-j) (by omega)
        have haa : j+(a-j)=a := by omega
        simp only [haa] at hx' hy'
        exact hx'.symm.trans ((ih (i+(a-j)) (by omega) (by omega)).trans hy')
      · by_cases haj : a < j
        · have h := congrFun hxy (⟨a,by omega⟩ : Fin (n-m))
          simpa only [Function.comp_apply, deleteBlockIndex, if_pos haj] using h
        · have ham : j+m ≤ a := by omega
          have h := congrFun hxy (⟨a-m,by omega⟩ : Fin (n-m))
          simpa only [Function.comp_apply, deleteBlockIndex, if_neg (show ¬a-m < j by omega),
            Nat.sub_add_cancel (show m ≤ a by omega)] using h
  funext a
  exact hall a.val a.isLt

private theorem fixedRepeatCount [Fintype A] {n m : ℕ} (i j : ℕ) (hij : i < j) (hjm : j+m ≤ n) :
    (Finset.univ.filter (fun x : Fin n → A =>
      ((List.ofFn x).drop i).take m = ((List.ofFn x).drop j).take m)).card ≤ Fintype.card A ^ (n-m) := by
  classical
  have hh := Finset.card_le_card_of_injOn (fun x : Fin n → A => x ∘ deleteBlockIndex j hjm)
    (s := Finset.univ.filter (fun x : Fin n → A => ((List.ofFn x).drop i).take m = ((List.ofFn x).drop j).take m))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _) (by
      intro x hx y hy hxy
      exact deleteBlockInjective hij hjm (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy)
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using hh

private theorem repeatedCount [Fintype A] (n m : ℕ) :
    (Finset.univ.filter (fun x : Fin n → A => repeatedFactor m (List.ofFn x))).card ≤
      (n+1)*(n+1)*Fintype.card A ^ (n-m) := by
  classical
  let R := fun p : Fin (n+1) × Fin (n+1) =>
    Finset.univ.filter (fun x : Fin n → A => p.1.val < p.2.val ∧ p.2.val+m ≤ n ∧
      ((List.ofFn x).drop p.1.val).take m = ((List.ofFn x).drop p.2.val).take m)
  have hsub : (Finset.univ.filter (fun x : Fin n → A => repeatedFactor m (List.ofFn x))) ⊆
      Finset.univ.biUnion R := by
    intro x hx
    obtain ⟨i,j,hij,hjm,hrep⟩ := (Finset.mem_filter.mp hx).2
    simp only [List.length_ofFn] at hjm
    apply Finset.mem_biUnion.mpr
    exact ⟨(⟨i,by omega⟩,⟨j,by omega⟩),Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij,hjm,hrep⟩⟩
  calc
    _ ≤ (Finset.univ.biUnion R).card := Finset.card_le_card hsub
    _ ≤ ∑ p : Fin (n+1) × Fin (n+1), (R p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : Fin (n+1) × Fin (n+1), Fintype.card A ^ (n-m) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hvalid : p.1.val < p.2.val ∧ p.2.val+m ≤ n
      · have hsub' : R p ⊆ Finset.univ.filter (fun x : Fin n → A =>
            ((List.ofFn x).drop p.1.val).take m = ((List.ofFn x).drop p.2.val).take m) := by
          intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2.2.2⟩
        exact (Finset.card_le_card hsub').trans (fixedRepeatCount _ _ hvalid.1 hvalid.2)
      · have hempty : R p = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx h
          exact hvalid ⟨h.1,h.2.1⟩
        simp [hempty]
    _ = _ := by simp [Nat.mul_assoc]

end D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound

namespace D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound
open Filter Topology

private theorem existsSparseScale (r C D : ℕ) (hr : 2 ≤ r) :
    ∃ m : ℕ, 1 ≤ m ∧ (C*m*m+1)*(C*m*m+1)*r^D < r^m := by
  have hrR : (1 : ℝ) < r := by exact Nat.one_lt_cast.mpr hr
  let K : ℝ := (C+1 : ℕ)^2 * (r : ℝ)^D
  have hK : 0 < K := by dsimp [K]; positivity
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt 4 hrR).const_mul K
  have hevent : ∀ᶠ m : ℕ in atTop, K*((m : ℝ)^4/(r : ℝ)^m) < 1 := by
    exact hlim.eventually (gt_mem_nhds (by simpa using (zero_lt_one : (0:ℝ) < 1)))
  obtain ⟨m,hm,hsmall⟩ := ((eventually_ge_atTop 1).and hevent).exists
  refine ⟨m,hm,?_⟩
  have hmR : (1 : ℝ) ≤ m := by exact Nat.one_le_cast.mpr hm
  have hbound : ((C*m*m+1 : ℕ) : ℝ)^2 ≤ ((C+1 : ℕ) : ℝ)^2 * (m : ℝ)^4 := by
    push_cast
    have hb : (C : ℝ)*m*m+1 ≤ ((C : ℝ)+1)*(m : ℝ)^2 := by nlinarith
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (C : ℝ)*m*m+1) hb 2
    nlinarith only [hh]
  have hpow : (0:ℝ) < (r : ℝ)^m := pow_pos (by positivity) _
  have hsmall' : K*(m : ℝ)^4 < (r : ℝ)^m := by
    rwa [← mul_div_assoc, div_lt_iff₀ hpow, one_mul] at hsmall
  have hh : ((C*m*m+1 : ℕ) : ℝ)^2 * (r : ℝ)^D < (r : ℝ)^m := by
    calc
      _ ≤ (((C+1 : ℕ) : ℝ)^2 * (m : ℝ)^4) * (r : ℝ)^D :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = K*(m : ℝ)^4 := by dsimp [K]; ring
      _ < _ := hsmall'
  have hhNat : (C*m*m+1)^2*r^D < r^m := by exact_mod_cast hh
  simpa only [pow_two] using hhNat

end D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound

namespace D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound

private theorem lowLanguageSparse {A : Type} [Fintype A] (hA : 2 ≤ Fintype.card A)
    (q : ℚ) (hq : 0 < q) (hqhalf : q < (1:ℚ)/2) : sparseNonempty (Lq (Alphabet := A) q) := by
  classical
  have hgap : 0 < 1-2*q := by linarith
  obtain ⟨C,hC⟩ := exists_nat_gt (max (max (1/q) (1/(1-2*q))) 1)
  have hCq : 1 < q*(C:ℚ) := by
    have hh : 1/q < (C:ℚ) := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hC)
    have := (div_lt_iff₀ hq).mp hh
    linarith
  have hCg : 1 < (1-2*q)*(C:ℚ) := by
    have hh : 1/(1-2*q) < (C:ℚ) := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hC)
    have := (div_lt_iff₀ hgap).mp hh
    linarith
  have hCone : 1 ≤ C := by
    have hh : (1:ℚ) < C := (le_max_right _ _).trans_lt hC
    exact_mod_cast hh.le
  intro D
  obtain ⟨m,hm,hscale⟩ := existsSparseScale (Fintype.card A) C D hA
  let n := C*m*m
  have hCm : m ≤ C*m := by simpa using Nat.mul_le_mul_right m hCone
  have hCm' : C ≤ C*m := by simpa using Nat.mul_le_mul_left C hm
  have hmul : C*m ≤ C*m*m := by simpa using Nat.mul_le_mul_left (C*m) hm
  have hmn : m ≤ n := hCm.trans hmul
  have hCn : C ≤ n := hCm'.trans hmul
  have hsize : (m*m : ℕ) ≤ (1-2*q)*(n:ℚ) := by
    dsimp [n]
    push_cast
    have hmm : (0:ℚ) ≤ (m:ℚ)*(m:ℚ) := by positivity
    nlinarith only [mul_le_mul_of_nonneg_right hCg.le hmm]
  have hqn : 1 < q*(n:ℚ) := by
    have hCnQ : (C:ℚ) ≤ n := by exact Rat.natCast_le_natCast.mpr hCn
    nlinarith
  refine ⟨n,?_,?_⟩
  · haveI : Nonempty A := Fintype.card_pos_iff.mp (by omega)
    let a : A := Classical.choice inferInstance
    refine ⟨fun _ => a,?_⟩
    simpa only [List.ofFn_const] using constantWordMemLq a n q hqn
  · have hcount : languageCount (Lq (Alphabet := A) q) n ≤
        (n+1)*(n+1)*Fintype.card A^(n-m) := by
      apply le_trans (b := (Finset.univ.filter (fun x : Fin n → A => repeatedFactor m (List.ofFn x))).card)
      · apply Finset.card_le_card
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lowImpliesRepeat (by omega)
          (Finset.mem_filter.mp hx).2 (by simpa only [List.length_ofFn] using hsize)⟩
      · exact repeatedCount n m
    have hrpos : 0 < Fintype.card A^(n-m) := pow_pos (by omega) _
    calc
      languageCount (Lq q) n * Fintype.card A^D ≤
          ((n+1)*(n+1)*Fintype.card A^(n-m))*Fintype.card A^D := Nat.mul_le_mul_right _ hcount
      _ = ((n+1)*(n+1)*Fintype.card A^D)*Fintype.card A^(n-m) := by ring
      _ < Fintype.card A^m*Fintype.card A^(n-m) := Nat.mul_lt_mul_of_pos_right hscale hrpos
      _ = Fintype.card A^n := by rw [← pow_add, Nat.add_sub_of_le hmn]

end D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound

namespace D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound

private theorem claimOfSparse
    (hsparse : ∀ (A : Type) (_ : Fintype A), 2 ≤ Fintype.card A →
      ∀ q : ℚ, 0 < q → q < (1 : ℚ) / 2 → sparseNonempty (Lq (Alphabet := A) q)) :
    claim := by
  intro A inst hA
  refine ⟨complexityTotalProof A, ?_⟩
  intro q hq hqhalf
  refine ⟨?_, ?_⟩
  · intro p hp e he
    exact ⟨sparseArithmeticNotRecognizable hA (Lq q) (hsparse A inst hA q hq hqhalf) p hp e he,
      sparseArithmeticComplementNotRecognizable hA (Lq q) (hsparse A inst hA q hq hqhalf) p hp e he⟩
  · intro t e he
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
    let labels : Bool → A := fun z => if z then b else a
    have hlabels : Function.Injective labels := by exact Bool.injective_iff.mpr hab
    have hset : {w : List Bool | w.map labels ∈ Lq q} = Lq q := by
      ext w
      exact memLqMapIff labels hlabels q w
    have hsparseBool : sparseNonempty {w : List Bool | w.map labels ∈ Lq q} := by
      rw [hset]
      exact hsparse Bool inferInstance (by simp) q hq hqhalf
    exact ⟨sparseBooleanNotRecognizable e (Lq q) labels hsparseBool,
      sparseBooleanComplementNotRecognizable e (Lq q) labels hsparseBool⟩

theorem result : claim := by
  apply claimOfSparse
  intro A inst hA q hq hqhalf
  exact lowLanguageSparse hA q hq hqhalf

end D5.S3.Combinatorics.AutomataCircuits.LowAutomaticComplexityCircuitLowerBound
