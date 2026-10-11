/- GID: D5/S3/Quantum/SpinChains/TwoWallMarked
   generality: G
   mirror-B: D5/B/S3/Quantum/SpinChains/TwoWallMarked
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marking either wall gives a free double cover of literal two-wall words. -/

import D5.S3.Quantum.SpinChains.TwoWallWords
import D5.S3.Quantum.SpinChains.BinaryBinBaseChange
import Mathlib.Data.Finset.Card

open scoped BigOperators

namespace D5.S3.Quantum.SpinChains.TwoWallMarked

open TwoWallWords

/-- A literal word together with one of its wall positions. -/
abbrev MarkedWord (a b : ℕ) := {x : Word a b × Pos a b // x.1.1 x.2 = wall}

private theorem other_exists {a b : ℕ} (x : MarkedWord a b) :
    ∃ q : Pos a b, q ≠ x.1.2 ∧ x.1.1.1 q = wall ∧
      ∀ r, x.1.1.1 r = wall → r = x.1.2 ∨ r = q := by
  classical
  let s := Finset.univ.filter (fun p => x.1.1.1 p = wall)
  have hs : s.card = 2 := by
    simpa [s, count, Finset.sum_boole] using x.1.1.2.2.2
  obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp hs
  have mem (r : Pos a b) : x.1.1.1 r = wall ↔ r = p ∨ r = q := by
    have h : r ∈ s ↔ r = p ∨ r = q := by rw [hs]; simp
    simpa [s] using h
  rcases (mem x.1.2).mp x.2 with h | h
  · refine ⟨q, ?_, (mem q).mpr (Or.inr rfl), ?_⟩
    · simpa [h] using hpq.symm
    · intro r hr
      simpa [h] using (mem r).mp hr
  · refine ⟨p, ?_, (mem p).mpr (Or.inl rfl), ?_⟩
    · simpa [h] using hpq
    · intro r hr
      simpa [h, or_comm] using (mem r).mp hr

/-- The unique wall different from the distinguished wall. -/
noncomputable def otherWall {a b : ℕ} (x : MarkedWord a b) : Pos a b :=
  Classical.choose (other_exists x)

private theorem other_spec {a b : ℕ} (x : MarkedWord a b) :
    otherWall x ≠ x.1.2 ∧ x.1.1.1 (otherWall x) = wall ∧
      ∀ r, x.1.1.1 r = wall → r = x.1.2 ∨ r = otherWall x :=
  Classical.choose_spec (other_exists x)

/-- Exchange the distinguished wall while retaining the literal word. -/
noncomputable def J {a b : ℕ} (x : MarkedWord a b) : MarkedWord a b :=
  ⟨(x.1.1, otherWall x), (other_spec x).2.1⟩

private theorem J_word {a b : ℕ} (x : MarkedWord a b) : (J x).1.1 = x.1.1 := rfl

private theorem J_involutive {a b : ℕ} : Function.Involutive (@J a b) := by
  intro x
  apply Subtype.ext
  refine Prod.ext (by rfl) ?_
  change otherWall (J x) = x.1.2
  rcases (other_spec x).2.2 (otherWall (J x)) (other_spec (J x)).2.1 with h | h
  · exact h
  · exact ((other_spec (J x)).1 h).elim

private theorem J_ne {a b : ℕ} (x : MarkedWord a b) : J x ≠ x := by
  intro h
  exact (other_spec x).1 (congrArg (fun z => z.1.2) h)

/-- Translation sends the distinguished position p to p+t. -/
def markedRotate {a b : ℕ} (t : Pos a b) : Equiv.Perm (MarkedWord a b) where
  toFun x := ⟨(rotate t x.1.1, x.1.2 + t), by
    change x.1.1.1 (x.1.2 + t + -t) = wall
    simpa using x.2⟩
  invFun x := ⟨((rotate t).symm x.1.1, x.1.2 - t), by
    change x.1.1.1 (x.1.2 - t + t) = wall
    simpa using x.2⟩
  left_inv x := by apply Subtype.ext; apply Prod.ext <;> simp
  right_inv x := by apply Subtype.ext; apply Prod.ext <;> simp

private theorem rotate_J {a b : ℕ} (t : Pos a b) (x : MarkedWord a b) :
    markedRotate t (J x) = J (markedRotate t x) := by
  apply Subtype.ext
  refine Prod.ext (by rfl) ?_
  change otherWall x + t = otherWall (markedRotate t x)
  have hw : (markedRotate t x).1.1.1 (otherWall x + t) = wall := by
    change x.1.1.1 (otherWall x + t + -t) = wall
    simpa using (other_spec x).2.1
  rcases (other_spec (markedRotate t x)).2.2 _ hw with h | h
  · exact ((other_spec x).1 (add_right_cancel h)).elim
  · exact h

/-- Linear combinations of marked literal words. -/
abbrev MarkedSpace (K : Type*) [Zero K] (a b : ℕ) := MarkedWord a b →₀ K

noncomputable def markedDelta (K : Type*) [Field K] {a b : ℕ} (x : MarkedWord a b) :
    MarkedSpace K a b := Finsupp.single x 1

/-- Forget the distinguished wall. -/
noncomputable def Q (K : Type*) [Field K] (a b : ℕ) :
    MarkedSpace K a b →ₗ[K] Space K a b := Finsupp.lmapDomain K K (fun x => x.1.1)

/-- Sum the two lifts, once for each wall of the literal word. -/
noncomputable def S (K : Type*) [Field K] (a b : ℕ) :
    Space K a b →ₗ[K] MarkedSpace K a b :=
  Finsupp.linearCombination K (fun w =>
    ∑ p : {p : Pos a b // w.1 p = wall}, markedDelta K ⟨(w, p.1), p.2⟩)

/-- Linear action of exchanging the distinguished wall. -/
noncomputable def Jstar (K : Type*) [Field K] (a b : ℕ) :
    Module.End K (MarkedSpace K a b) := Finsupp.lmapDomain K K J

/-- Linear translation on the marked cover. -/
noncomputable def markedTranslation (K : Type*) [Field K] {a b : ℕ} (t : Pos a b) :
    Module.End K (MarkedSpace K a b) := Finsupp.lmapDomain K K (markedRotate t)

noncomputable def markedU (K : Type*) [Field K] (a b : ℕ) :
    Module.End K (MarkedSpace K a b) := markedTranslation K 1

private theorem lifts {a b : ℕ} (x : MarkedWord a b) :
    (Finset.univ : Finset {p : Pos a b // x.1.1.1 p = wall}) =
      {⟨x.1.2, x.2⟩, ⟨otherWall x, (other_spec x).2.1⟩} := by
  classical
  ext p
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  rcases (other_spec x).2.2 p.1 p.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

private theorem S_single {a b : ℕ} (K : Type*) [Field K]
    (x : MarkedWord a b) (z : K) :
    S K a b (Finsupp.single x.1.1 z) =
      Finsupp.single x z + Finsupp.single (J x) z := by
  classical
  have hne : (⟨x.1.2, x.2⟩ : {p : Pos a b // x.1.1.1 p = wall}) ≠
      ⟨otherWall x, (other_spec x).2.1⟩ := by
    intro h
    exact (other_spec x).1 (congrArg Subtype.val h).symm
  rw [S, Finsupp.linearCombination_single, lifts x, Finset.sum_pair hne]
  simp only [markedDelta, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

/-- The mark exchange is free, translation compatible, and gives the two descent identities. -/
theorem marked_descent (K : Type*) [Field K] (a b : ℕ) :
    Function.Involutive (@J a b) ∧
    (∀ x : MarkedWord a b, J x ≠ x) ∧
    (∀ (t : Pos a b) (x : MarkedWord a b),
      markedRotate t (J x) = J (markedRotate t x)) ∧
    (Q K a b).comp (S K a b) = (2 : K) • LinearMap.id ∧
    (S K a b).comp (Q K a b) = LinearMap.id + Jstar K a b ∧
    (∀ t : Pos a b, (markedTranslation K t).comp (S K a b) =
      (S K a b).comp (translation K t)) ∧
    (∀ t : Pos a b, (Q K a b).comp (markedTranslation K t) =
      (translation K t).comp (Q K a b)) ∧
    (markedU K a b).comp (S K a b) = (S K a b).comp (U K a b) ∧
    (Q K a b).comp (markedU K a b) = (U K a b).comp (Q K a b) := by
  classical
  have hQ (x : MarkedWord a b) (z : K) :
      Q K a b (Finsupp.single x z) = Finsupp.single x.1.1 z := by simp [Q]
  have ht (t : Pos a b) (x : MarkedWord a b) (z : K) :
      markedTranslation K t (Finsupp.single x z) =
        Finsupp.single (markedRotate t x) z := by simp [markedTranslation]
  have hR (t : Pos a b) :
      (markedTranslation K t).comp (S K a b) =
        (S K a b).comp (translation K t) := by
    apply Finsupp.lhom_ext
    intro w z
    have hw : ∃ p, w.1 p = wall := by
      have hc := w.2.2.2
      by_contra hn
      push Not at hn
      simp [count, hn] at hc
    obtain ⟨p, hp⟩ := hw
    let x : MarkedWord a b := ⟨(w,p),hp⟩
    change markedTranslation K t (S K a b (Finsupp.single x.1.1 z)) =
      S K a b (translation K t (Finsupp.single x.1.1 z))
    rw [S_single, map_add, ht, ht]
    simp only [translation, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [← show (markedRotate t x).1.1 = rotate t x.1.1 from rfl, S_single, rotate_J]
  have hforget (t : Pos a b) :
      (Q K a b).comp (markedTranslation K t) =
        (translation K t).comp (Q K a b) := by
    apply Finsupp.lhom_ext
    intro x z
    simp [LinearMap.comp_apply, ht, hQ, translation, markedRotate]
  refine ⟨J_involutive, J_ne, rotate_J, ?_, ?_, hR, hforget, hR 1, hforget 1⟩
  · apply Finsupp.lhom_ext
    intro w z
    have hw : ∃ p, w.1 p = wall := by
      by_contra hn
      push Not at hn
      have hc := w.2.2.2
      simp [count, hn] at hc
    obtain ⟨p,hp⟩ := hw
    let x : MarkedWord a b := ⟨(w,p),hp⟩
    change Q K a b (S K a b (Finsupp.single x.1.1 z)) = _
    rw [S_single, map_add, hQ, hQ, J_word]
    simp [two_smul, x]
  · apply Finsupp.lhom_ext
    intro x z
    simp [LinearMap.comp_apply, hQ, S_single, Jstar]


open D5.S1.Words.ParityCode.OddTopWeight (ones)

/-- Two ordered binary arcs. The redundant length n is uniquely determined by m. -/
structure Coordinates (a b : ℕ) where
  p : Pos a b
  m : ℕ
  n : ℕ
  u : Fin m → Bool
  v : Fin n → Bool
  length : m + n = a + b
  filling : ones u + ones v = b

private def arcLetter (s : Bool) : Letter := if s then two else one

private def arcVector (m n : ℕ) (u : Fin m → Bool) (v : Fin n → Bool) :
    Fin ((m + 1) + (n + 1)) → Letter :=
  Fin.append (Fin.cons wall (fun i => arcLetter (u i)))
    (Fin.cons wall (fun i => arcLetter (v i)))

private def siteEquiv {a b : ℕ} (p : Pos a b) (m n : ℕ) (h : m + n = a + b) :
    Fin ((m + 1) + (n + 1)) ≃ Pos a b :=
  (finCongr (by omega)).trans ((ZMod.finEquiv (a + b + 2)).toEquiv.trans (Equiv.addRight p))

private theorem siteEquiv_apply {a b : ℕ} (p : Pos a b) (m n : ℕ)
    (h : m + n = a + b) (i : Fin ((m + 1) + (n + 1))) :
    siteEquiv p m n h i = p + (i.val : Pos a b) := by
  change (ZMod.finEquiv (a + b + 2)) (Fin.cast (by omega) i) + p = _
  have hcast : (ZMod.finEquiv (a + b + 2)) (Fin.cast (by omega) i) =
      (i.val : Pos a b) := by
    apply ZMod.val_injective
    rw [ZMod.val_natCast_of_lt (by omega)]
    rfl
  exact (congrArg (fun z : Pos a b => z + p) hcast).trans (add_comm _ _)

private def rawEncode {a b : ℕ} (p : Pos a b) (m n : ℕ) (h : m + n = a + b)
    (u : Fin m → Bool) (v : Fin n → Bool) : Pos a b → Letter :=
  fun r => arcVector m n u v ((siteEquiv p m n h).symm r)

private theorem raw_at {a b : ℕ} (p : Pos a b) (m n : ℕ) (h : m + n = a + b)
    (u : Fin m → Bool) (v : Fin n → Bool) (i : Fin ((m + 1) + (n + 1))) :
    rawEncode p m n h u v (p + (i.val : Pos a b)) = arcVector m n u v i := by
  rw [← siteEquiv_apply p m n h i]
  simp [rawEncode]

private theorem raw_count {a b : ℕ} (p : Pos a b) (m n : ℕ) (h : m + n = a + b)
    (u : Fin m → Bool) (v : Fin n → Bool) (c : Letter) :
    count c (rawEncode p m n h u v) =
      (if wall = c then 1 else 0) + (∑ i, if arcLetter (u i) = c then 1 else 0) +
      ((if wall = c then 1 else 0) + ∑ i, if arcLetter (v i) = c then 1 else 0) := by
  rw [count]
  change (∑ r, (fun i => if arcVector m n u v i = c then 1 else 0)
    ((siteEquiv p m n h).symm r)) = _
  rw [(siteEquiv p m n h).symm.sum_comp
    (fun i => if arcVector m n u v i = c then 1 else 0), Fin.sum_univ_add]
  simp only [arcVector, Fin.append_left, Fin.append_right, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]

private theorem arc_counts (m : ℕ) (u : Fin m → Bool) :
    (∑ i, if arcLetter (u i) = wall then 1 else 0 : ℕ) = 0 ∧
    (∑ i, if arcLetter (u i) = two then 1 else 0 : ℕ) = ones u ∧
    (∑ i, if arcLetter (u i) = one then 1 else 0 : ℕ) + ones u = m := by
  have hw (i : Fin m) : (if arcLetter (u i) = wall then 1 else 0 : ℕ) = 0 := by
    cases u i <;> decide
  have ht (i : Fin m) : (if arcLetter (u i) = two then 1 else 0 : ℕ) =
      (if u i then 1 else 0) := by cases u i <;> decide
  have hs (i : Fin m) : (if arcLetter (u i) = one then 1 else 0 : ℕ) +
      (if u i then 1 else 0) = 1 := by cases u i <;> decide
  refine ⟨by simp_rw [hw]; simp, by simp_rw [ht]; rfl, ?_⟩
  rw [ones, ← Finset.sum_add_distrib]
  simp_rw [hs]
  simp

private theorem raw_counts {a b : ℕ} (p : Pos a b) (m n : ℕ) (h : m + n = a + b)
    (u : Fin m → Bool) (v : Fin n → Bool) :
    count wall (rawEncode p m n h u v) = 2 ∧
    count two (rawEncode p m n h u v) = ones u + ones v ∧
    count one (rawEncode p m n h u v) + (ones u + ones v) = a + b := by
  have hu := arc_counts m u
  have hv := arc_counts n v
  refine ⟨?_, ?_, ?_⟩
  · simp [raw_count, hu.1, hv.1]
  · simp only [raw_count, show wall ≠ two by decide, if_false, zero_add, hu.2.1, hv.2.1]
  · simp only [raw_count, show wall ≠ one by decide, if_false, zero_add]
    omega

/-- Place wall,u,wall,v at their consecutive offsets from p. -/
def encode {a b : ℕ} (c : Coordinates a b) : MarkedWord a b :=
  ⟨(⟨rawEncode c.p c.m c.n c.length c.u c.v, by
      have hc := raw_counts c.p c.m c.n c.length c.u c.v
      refine ⟨?_, by simpa only [c.filling] using hc.2.1, hc.1⟩
      rw [c.filling] at hc
      omega⟩, c.p), by
    have h := raw_at c.p c.m c.n c.length c.u c.v
      ((0 : Fin (c.m + 1)).castAdd (c.n + 1))
    simpa [arcVector] using h⟩


private theorem arcLetter_read (c : Letter) (h : c ≠ wall) :
    arcLetter (decide (c = two)) = c := by
  fin_cases c <;> simp_all [arcLetter, one, two, wall]

private theorem offset_injective {a b : ℕ} {i j : ℕ}
    (hi : i < a + b + 2) (hj : j < a + b + 2)
    (h : (i : Pos a b) = (j : Pos a b)) : i = j := by
  have := congrArg ZMod.val h
  simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using this

private theorem arcVector_walls (m n : ℕ) (u : Fin m → Bool) (v : Fin n → Bool)
    (i : Fin ((m + 1) + (n + 1))) :
    arcVector m n u v i = wall ↔ i.val = 0 ∨ i.val = m + 1 := by
  cases i using Fin.addCases with
  | left i =>
    cases i using Fin.cases with
    | zero => simp [arcVector]
    | succ i =>
      have hn : arcLetter (u i) ≠ wall := by cases u i <;> decide
      simp only [arcVector, Fin.append_left, Fin.cons_succ, Fin.val_castAdd, Fin.val_succ]
      simp only [hn, false_iff]
      omega
  | right i =>
    cases i using Fin.cases with
    | zero => simp [arcVector]
    | succ i =>
      have hn : arcLetter (v i) ≠ wall := by cases v i <;> decide
      simp only [arcVector, Fin.append_right, Fin.cons_succ, Fin.val_natAdd, Fin.val_succ]
      simp only [hn, false_iff]
      omega

private theorem raw_walls {a b : ℕ} (p : Pos a b) (m n : ℕ) (h : m + n = a + b)
    (u : Fin m → Bool) (v : Fin n → Bool) (r : Pos a b) :
    rawEncode p m n h u v r = wall ↔ r = p ∨ r = p + ((m + 1 : ℕ) : Pos a b) := by
  obtain ⟨i, rfl⟩ := (siteEquiv p m n h).surjective r
  rw [siteEquiv_apply, raw_at, arcVector_walls]
  constructor
  · rintro (hi | hi) <;> simp [hi]
  · rintro (hr | hr)
    · left
      have hz : (i.val : Pos a b) = (0 : ℕ) := by simpa only [add_eq_left, Nat.cast_zero] using hr
      exact offset_injective (by omega) (by omega) hz
    · right
      exact offset_injective (by omega) (by omega) (add_left_cancel hr)

private theorem encode_other {a b : ℕ} (c : Coordinates a b) :
    otherWall (encode c) = c.p + ((c.m + 1 : ℕ) : Pos a b) := by
  have hw := (other_spec (encode c)).2.1
  rcases (raw_walls c.p c.m c.n c.length c.u c.v _).mp hw with h | h
  · exact ((other_spec (encode c)).1 h).elim
  · exact h

private theorem raw_reconstruction {a b : ℕ} (w : Word a b) (p : Pos a b)
    (m n : ℕ) (hlen : m + n = a + b) (hp : w.1 p = wall)
    (hq : w.1 (p + ((m + 1 : ℕ) : Pos a b)) = wall)
    (hw : ∀ r, w.1 r = wall → r = p ∨ r = p + ((m + 1 : ℕ) : Pos a b)) :
    rawEncode p m n hlen
      (fun i => decide (w.1 (p + ((i.val + 1 : ℕ) : Pos a b)) = two))
      (fun i => decide (w.1 (p + ((m + 2 + i.val : ℕ) : Pos a b)) = two)) = w.1 := by
  funext r
  obtain ⟨i, rfl⟩ := (siteEquiv p m n hlen).surjective r
  rw [siteEquiv_apply, raw_at]
  cases i using Fin.addCases with
  | left i =>
    cases i using Fin.cases with
    | zero => simpa [arcVector] using hp.symm
    | succ i =>
      simp only [arcVector, Fin.append_left, Fin.cons_succ, Fin.val_castAdd, Fin.val_succ]
      apply arcLetter_read
      intro h
      rcases hw _ h with h | h
      · have he := offset_injective (a := a) (b := b) (i := i.val + 1) (j := 0)
          (by omega) (by omega) (by simpa only [add_eq_left, Nat.cast_zero] using h)
        omega
      · have he := offset_injective (a := a) (b := b) (i := i.val + 1) (j := m + 1)
          (by omega) (by omega) (add_left_cancel h)
        omega
  | right i =>
    cases i using Fin.cases with
    | zero => simpa [arcVector] using hq.symm
    | succ i =>
      simp only [arcVector, Fin.append_right, Fin.cons_succ, Fin.val_natAdd, Fin.val_succ]
      have he : m + 1 + (i.val + 1) = m + 2 + i.val := by omega
      rw [he]
      apply arcLetter_read
      intro h
      rcases hw _ h with h | h
      · have he := offset_injective (a := a) (b := b) (i := m + 2 + i.val) (j := 0)
          (by omega) (by omega) (by simpa only [add_eq_left, Nat.cast_zero] using h)
        omega
      · have he := offset_injective (a := a) (b := b) (i := m + 2 + i.val) (j := m + 1)
          (by omega) (by omega) (add_left_cancel h)
        omega

private noncomputable def distance {a b : ℕ} (x : MarkedWord a b) : ℕ :=
  (otherWall x - x.1.2).val

private theorem distance_bounds {a b : ℕ} (x : MarkedWord a b) :
    1 ≤ distance x ∧ distance x ≤ a + b + 1 := by
  have hlt := ZMod.val_lt (otherWall x - x.1.2)
  have hn : (otherWall x - x.1.2).val ≠ 0 := by
    intro h
    exact (other_spec x).1 (sub_eq_zero.mp ((ZMod.val_eq_zero _).mp h))
  dsimp [distance]
  omega

private theorem distance_wall {a b : ℕ} (x : MarkedWord a b) :
    x.1.2 + ((distance x : ℕ) : Pos a b) = otherWall x := by
  simp only [distance, ZMod.natCast_zmod_val]
  abel

/-- Read the arcs between the marked wall and the unique other wall. -/
noncomputable def decode {a b : ℕ} (x : MarkedWord a b) : Coordinates a b := by
  let m := distance x - 1
  let n := a + b - m
  have hlen : m + n = a + b := by have := distance_bounds x; dsimp [m, n]; omega
  let u : Fin m → Bool := fun i => decide (x.1.1.1 (x.1.2 + ((i.val + 1 : ℕ) : Pos a b)) = two)
  let v : Fin n → Bool := fun i => decide (x.1.1.1 (x.1.2 + ((m + 2 + i.val : ℕ) : Pos a b)) = two)
  have hm : m + 1 = distance x := by have := distance_bounds x; dsimp [m]; omega
  have hq : x.1.2 + ((m + 1 : ℕ) : Pos a b) = otherWall x := by rw [hm]; exact distance_wall x
  have hr : rawEncode x.1.2 m n hlen u v = x.1.1.1 :=
    raw_reconstruction x.1.1 x.1.2 m n hlen x.2 (by rw [hq]; exact (other_spec x).2.1)
      (by simpa only [hq] using (other_spec x).2.2)
  refine ⟨x.1.2, m, n, u, v, hlen, ?_⟩
  have hc := (raw_counts x.1.2 m n hlen u v).2.1
  rw [hr, x.1.1.2.2.1] at hc
  exact hc.symm

private theorem encode_decode {a b : ℕ} (x : MarkedWord a b) : encode (decode x) = x := by
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  apply Subtype.ext
  change rawEncode x.1.2 (distance x - 1) (a + b - (distance x - 1)) _ _ _ = x.1.1.1
  apply raw_reconstruction
  · exact x.2
  · have hm : distance x - 1 + 1 = distance x := by have := distance_bounds x; omega
    rw [hm, distance_wall]
    exact (other_spec x).2.1
  · have hm : distance x - 1 + 1 = distance x := by have := distance_bounds x; omega
    simpa only [hm, distance_wall] using (other_spec x).2.2

private theorem decode_encode {a b : ℕ} (c : Coordinates a b) : decode (encode c) = c := by
  have hd : distance (encode c) = c.m + 1 := by
    dsimp [distance]
    rw [encode_other]
    change (c.p + ((c.m + 1 : ℕ) : Pos a b) - c.p).val = c.m + 1
    rw [add_sub_cancel_left, ZMod.val_natCast_of_lt (by have := c.length; omega)]
  have hm : (decode (encode c)).m = c.m := by change distance (encode c) - 1 = _; omega
  have hn : (decode (encode c)).n = c.n := by
    change a + b - (distance (encode c) - 1) = _
    have := c.length
    omega
  have hu : ∀ i : Fin c.m,
      (decode (encode c)).u (Fin.cast hm.symm i) = c.u i := by
    intro i
    change decide (rawEncode c.p c.m c.n c.length c.u c.v
      (c.p + ((i.val + 1 : ℕ) : Pos a b)) = two) = c.u i
    have ht := raw_at c.p c.m c.n c.length c.u c.v (i.succ.castAdd (c.n + 1))
    simp only [Fin.val_castAdd, Fin.val_succ, arcVector, Fin.append_left, Fin.cons_succ] at ht
    rw [ht]
    cases c.u i <;> decide
  have hv : ∀ i : Fin c.n,
      (decode (encode c)).v (Fin.cast hn.symm i) = c.v i := by
    intro i
    change decide (rawEncode c.p c.m c.n c.length c.u c.v
      (c.p + (((decode (encode c)).m + 2 + i.val : ℕ) : Pos a b)) = two) = c.v i
    rw [hm]
    have ht := raw_at c.p c.m c.n c.length c.u c.v (i.succ.natAdd (c.m + 1))
    simp only [Fin.val_natAdd, Fin.val_succ, arcVector, Fin.append_right, Fin.cons_succ] at ht
    have he : c.m + 1 + (i.val + 1) = c.m + 2 + i.val := by omega
    rw [he] at ht
    rw [ht]
    cases c.v i <;> decide
  cases c with
  | mk p m n u v hlen hfill =>
    generalize hz : decode (encode ⟨p,m,n,u,v,hlen,hfill⟩) = z at *
    cases z with
    | mk p' m' n' u' v' hlen' hfill' =>
      dsimp at hm hn hu hv
      subst m'
      subst n'
      have hp : p' = p := by
        have := congrArg Coordinates.p hz
        exact this.symm
      subst p'
      have huu : u' = u := funext hu
      have hvv : v' = v := funext hv
      subst u'
      subst v'
      rfl

/-- The literal marked words and their ordered binary-arc coordinates. -/
noncomputable def coordinateEquiv (a b : ℕ) : Coordinates a b ≃ MarkedWord a b where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode


/-- Exchange the two arcs and move the mark to the second wall. -/
def coordinateSwap {a b : ℕ} (c : Coordinates a b) : Coordinates a b :=
  ⟨c.p + ((c.m + 1 : ℕ) : Pos a b), c.n, c.m, c.v, c.u,
    (Nat.add_comm _ _).trans c.length, (Nat.add_comm _ _).trans c.filling⟩

/-- Translation changes the starting position and retains both binary arcs. -/
def coordinateRotate {a b : ℕ} (t : Pos a b) (c : Coordinates a b) : Coordinates a b :=
  { c with p := c.p + t }

private theorem raw_swap {a b : ℕ} (c : Coordinates a b) :
    rawEncode (coordinateSwap c).p (coordinateSwap c).m (coordinateSwap c).n
      (coordinateSwap c).length (coordinateSwap c).u (coordinateSwap c).v =
      rawEncode c.p c.m c.n c.length c.u c.v := by
  have hwrap : ((c.m + 1 : ℕ) : Pos a b) + ((c.n + 1 : ℕ) : Pos a b) = 0 := by
    rw [← Nat.cast_add, show c.m + 1 + (c.n + 1) = a + b + 2 by have := c.length; omega]
    exact ZMod.natCast_self _
  funext r
  obtain ⟨i, rfl⟩ := (siteEquiv (coordinateSwap c).p (coordinateSwap c).m
    (coordinateSwap c).n (coordinateSwap c).length).surjective r
  rw [siteEquiv_apply, raw_at]
  change Fin ((c.n + 1) + (c.m + 1)) at i
  change arcVector c.n c.m c.v c.u i =
    rawEncode c.p c.m c.n c.length c.u c.v
      (c.p + ((c.m + 1 : ℕ) : Pos a b) + (i.val : Pos a b))
  cases i using Fin.addCases with
  | left i =>
    cases i using Fin.cases with
    | zero =>
      have ht := raw_at c.p c.m c.n c.length c.u c.v
        ((0 : Fin (c.n + 1)).natAdd (c.m + 1))
      simpa [arcVector, Fin.append_left, Fin.append_right] using ht.symm
    | succ i =>
      have ht := raw_at c.p c.m c.n c.length c.u c.v (i.succ.natAdd (c.m + 1))
      simpa [arcVector, Fin.append_left, Fin.append_right, Nat.cast_add, add_assoc] using ht.symm
  | right i =>
    cases i using Fin.cases with
    | zero =>
      have ht := raw_at c.p c.m c.n c.length c.u c.v
        ((0 : Fin (c.m + 1)).castAdd (c.n + 1))
      simpa only [arcVector, Fin.append_left, Fin.append_right, Fin.cons_zero,
        Fin.val_natAdd, Fin.val_zero, Nat.add_zero, add_assoc, hwrap, add_zero,
        Fin.val_castAdd, Nat.cast_zero] using ht.symm
    | succ i =>
      have ht := raw_at c.p c.m c.n c.length c.u c.v (i.succ.castAdd (c.n + 1))
      have hp : c.p + ((c.m + 1 : ℕ) : Pos a b) +
          (((c.n + 1) + (i.val + 1) : ℕ) : Pos a b) =
          c.p + ((i.val + 1 : ℕ) : Pos a b) := by
        calc
          _ = c.p + (((c.m + 1 : ℕ) : Pos a b) + ((c.n + 1 : ℕ) : Pos a b)) +
              ((i.val + 1 : ℕ) : Pos a b) := by push_cast; abel
          _ = _ := by rw [hwrap, add_zero]
      simpa only [arcVector, Fin.append_right, Fin.cons_succ, Fin.val_natAdd,
        Fin.val_succ, hp, Fin.append_left, Fin.val_castAdd] using ht.symm

private theorem encode_swap {a b : ℕ} (c : Coordinates a b) :
    encode (coordinateSwap c) = J (encode c) := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    exact raw_swap c
  · exact (encode_other c).symm

private theorem encode_rotate {a b : ℕ} (t : Pos a b) (c : Coordinates a b) :
    encode (coordinateRotate t c) = markedRotate t (encode c) := by
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  apply Subtype.ext
  funext r
  obtain ⟨i, rfl⟩ := (siteEquiv (c.p + t) c.m c.n c.length).surjective r
  rw [siteEquiv_apply]
  change rawEncode (c.p + t) c.m c.n c.length c.u c.v (c.p + t + (i.val : Pos a b)) =
    rawEncode c.p c.m c.n c.length c.u c.v (c.p + t + (i.val : Pos a b) + -t)
  rw [raw_at, show c.p + t + (i.val : Pos a b) + -t = c.p + (i.val : Pos a b) by abel,
    raw_at]

/-- Encoding, decoding, mark exchange and rotation agree on every arc, including empty arcs. -/
theorem marked_coordinates (a b : ℕ) :
    (∀ c : Coordinates a b, decode (encode c) = c) ∧
    (∀ x : MarkedWord a b, encode (decode x) = x) ∧
    (∀ c : Coordinates a b, c.m < a + b + 1 ∧ c.n = a + b - c.m) ∧
    (∀ c : Coordinates a b,
      (encode c).1.1.1 c.p = wall ∧
      (encode c).1.1.1 (c.p + ((c.m + 1 : ℕ) : Pos a b)) = wall ∧
      (∀ i : Fin c.m, (encode c).1.1.1 (c.p + ((i.val + 1 : ℕ) : Pos a b)) =
        if c.u i then two else one) ∧
      (∀ i : Fin c.n, (encode c).1.1.1 (c.p + ((c.m + 2 + i.val : ℕ) : Pos a b)) =
        if c.v i then two else one)) ∧
    (∀ c : Coordinates a b, encode (coordinateSwap c) = J (encode c)) ∧
    Function.Involutive (@coordinateSwap a b) ∧
    (∀ c : Coordinates a b, coordinateSwap c ≠ c) ∧
    (∀ (t : Pos a b) (c : Coordinates a b),
      encode (coordinateRotate t c) = markedRotate t (encode c)) ∧
    (∀ (t : Pos a b) (c : Coordinates a b),
      coordinateRotate t (coordinateSwap c) = coordinateSwap (coordinateRotate t c)) := by
  refine ⟨decode_encode, encode_decode, ?_, ?_, encode_swap, ?_, ?_, encode_rotate, ?_⟩
  · intro c
    have := c.length
    omega
  · intro c
    refine ⟨(encode c).2, ?_, ?_, ?_⟩
    · exact (encode_other c) ▸ (other_spec (encode c)).2.1
    · intro i
      have ht := raw_at c.p c.m c.n c.length c.u c.v (i.succ.castAdd (c.n + 1))
      simpa only [arcVector, Fin.append_left, Fin.cons_succ, Fin.val_castAdd,
        Fin.val_succ, arcLetter, encode] using ht
    · intro i
      have ht := raw_at c.p c.m c.n c.length c.u c.v (i.succ.natAdd (c.m + 1))
      have he : c.m + 1 + (i.val + 1) = c.m + 2 + i.val := by omega
      simpa only [arcVector, Fin.append_right, Fin.cons_succ, Fin.val_natAdd,
        Fin.val_succ, he, arcLetter, encode] using ht
  · intro c
    apply (coordinateEquiv a b).injective
    change encode (coordinateSwap (coordinateSwap c)) = encode c
    rw [encode_swap, encode_swap, (marked_descent ℚ a b).1]
  · intro c h
    have he := congrArg encode h
    rw [encode_swap] at he
    exact (marked_descent ℚ a b).2.1 _ he
  · intro t c
    apply (coordinateEquiv a b).injective
    change encode (coordinateRotate t (coordinateSwap c)) =
      encode (coordinateSwap (coordinateRotate t c))
    rw [encode_rotate, encode_swap, encode_swap, encode_rotate,
      (marked_descent ℚ a b).2.2.1]

#print axioms coordinateEquiv
#print axioms marked_coordinates
#print axioms marked_descent

end D5.S3.Quantum.SpinChains.TwoWallMarked
