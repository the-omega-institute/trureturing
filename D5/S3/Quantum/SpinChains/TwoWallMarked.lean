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

#print axioms marked_descent

end D5.S3.Quantum.SpinChains.TwoWallMarked
