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

#print axioms marked_descent

end D5.S3.Quantum.SpinChains.TwoWallMarked
