/- GID: D5/S3/StatisticalMechanics/FccPointGroupShells
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/FccPointGroupShells
   mirror-E: none(waiver:noncomputational-symbolic-identity)
   anchors: []
   utility: none
   digest: Signed permutation orbits on contact graph shells of the face centered cubic lattice. -/

import D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! Point-group orbit counting in the face centered cubic contact graph. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.StatisticalMechanics.FccPointGroupShells

/-- The even-sum integer lattice in three dimensions. -/
abbrev L := {x : Fin 3 → ℤ // (∑ i, x i) % 2 = 0}

/-- The twelve contact steps: two coordinates change by a unit and the third is fixed. -/
def contactGraph : SimpleGraph L where
  Adj x y :=
    (|(y.1 0 - x.1 0)| = 1 ∧ |(y.1 1 - x.1 1)| = 1 ∧ y.1 2 = x.1 2) ∨
    (|(y.1 0 - x.1 0)| = 1 ∧ y.1 1 = x.1 1 ∧ |(y.1 2 - x.1 2)| = 1) ∨
    (y.1 0 = x.1 0 ∧ |(y.1 1 - x.1 1)| = 1 ∧ |(y.1 2 - x.1 2)| = 1)
  symm := ⟨by
    intro x y h
    simpa only [abs_sub_comm, eq_comm] using h⟩
  loopless := ⟨by intro x h; simp at h⟩

/-- The origin of the lattice. -/
def origin : L := ⟨0, by simp⟩

/-- Genuine shortest-walk distance in the contact graph. -/
def d (x : L) : ℕ := contactGraph.dist origin x

/-- All signed coordinate permutations, represented faithfully as permutations of integer triples. -/
def W : Subgroup (Equiv.Perm (Fin 3 → ℤ)) where
  carrier := {w | ∃ (p : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) ∧ ∀ x i, w x i = s i * x (p i)}
  one_mem' := ⟨1, fun _ => 1, fun _ => Or.inl rfl, by intros; simp⟩
  mul_mem' := by
    rintro w v ⟨p, s, hs, hw⟩ ⟨q, t, ht, hv⟩
    refine ⟨p.trans q, fun i => s i * t (p i), ?_, ?_⟩
    · intro i
      rcases hs i with h | h <;> rcases ht (p i) with h' | h' <;> simp [h, h']
    · intro x i
      change w (v x) i = _
      rw [hw, hv]
      simp [mul_assoc]
  inv_mem' := by
    rintro w ⟨p, s, hs, hw⟩
    refine ⟨p.symm, fun i => s (p.symm i), fun i => hs _, ?_⟩
    intro x i
    have h := hw (w.symm x) (p.symm i)
    simp only [Equiv.apply_symm_apply] at h
    change w.symm x i = _
    rcases hs (p.symm i) with he | he <;> simp_all

private def norm (x : Fin 3 → ℤ) (i : Fin 3) : ℕ := (x i).natAbs

private lemma norm_signed (w : W) : ∃ p : Equiv.Perm (Fin 3),
    ∀ x, norm (w.1 x) = norm x ∘ p := by
  obtain ⟨p, s, hs, hw⟩ := w.2
  refine ⟨p, fun x => funext fun i => ?_⟩
  dsimp only [norm, Function.comp_apply]
  rw [hw]
  rcases hs i with h | h <;> simp [h]

private lemma parity_norm (x : Fin 3 → ℤ) :
    (∑ i, x i) % 2 = ((∑ i, norm x i : ℕ) : ℤ) % 2 := by
  simp only [Fin.sum_univ_three, Nat.cast_add, norm, Int.natCast_natAbs]
  rcases le_total 0 (x 0) with h0 | h0 <;>
    rcases le_total 0 (x 1) with h1 | h1 <;>
      rcases le_total 0 (x 2) with h2 | h2 <;>
        simp only [abs_of_nonneg, abs_of_nonpos, h0, h1, h2] <;> omega

private lemma signed_preserves (w : W) (x : L) : (∑ i, w.1 x.1 i) % 2 = 0 := by
  obtain ⟨p, hp⟩ := norm_signed w
  rw [parity_norm, hp]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp, ← parity_norm]
  exact x.2

/-- The literal signed permutation action restricted to the lattice. -/
instance latticeAction : MulAction W L where
  smul w x := ⟨w.1 x.1, signed_preserves w x⟩
  one_smul x := Subtype.ext (by rfl)
  mul_smul w v x := Subtype.ext (by rfl)

/-- The radius-n shell, including the origin shell at n=0. -/
def Shell (n : ℕ) := {x : L // d x = n}

/-- Number of signed permutation orbits on the shell, using the restricted orbit relation. -/
def A (n : ℕ) : ℕ :=
  Nat.card (Quotient ((MulAction.orbitRel W L).comap (Subtype.val : Shell n → L)))

private def potential (x : Fin 3 → ℤ) : ℕ :=
  max (Finset.univ.sup (norm x)) ((∑ i, norm x i) / 2)

private lemma potential_signed (w : W) (x : Fin 3 → ℤ) :
    potential (w.1 x) = potential x := by
  obtain ⟨p, hp⟩ := norm_signed w
  dsimp only [potential]
  rw [hp]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp]
  congr 1
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    exact Finset.le_sup (f := norm x) (Finset.mem_univ (p i))
  · apply Finset.sup_le
    intro i _
    simpa using Finset.le_sup (f := norm x ∘ p) (Finset.mem_univ (p.symm i))

private def signed (p : Equiv.Perm (Fin 3)) (s : Fin 3 → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) : W :=
  ⟨{ toFun := fun x i => s i * x (p i)
     invFun := fun x i => s (p.symm i) * x (p.symm i)
     left_inv := by
       intro x; funext i
       change s (p.symm i) * (s (p.symm i) * x (p (p.symm i))) = x i
       rcases hs (p.symm i) with h | h <;> simp [h]
     right_inv := by
       intro x; funext i
       change s i * (s (p.symm (p i)) * x (p.symm (p i))) = x i
       rcases hs i with h | h <;> simp [h] }, p, s, hs, by intros; rfl⟩

private def canonical (x : Fin 3 → ℤ) : Fin 3 → ℕ :=
  norm x ∘ Tuple.sort (norm x)

private lemma canonical_mono (x : Fin 3 → ℤ) : Monotone (canonical x) :=
  Tuple.monotone_sort _

private lemma canonical_signed (w : W) (x : Fin 3 → ℤ) :
    canonical (w.1 x) = canonical x := by
  obtain ⟨p, hp⟩ := norm_signed w
  dsimp only [canonical]
  rw [hp]
  exact Tuple.comp_perm_comp_sort_eq_comp_sort

private lemma to_canonical (x : Fin 3 → ℤ) :
    ∃ w : W, w.1 x = fun i => (canonical x i : ℤ) := by
  let p := Tuple.sort (norm x)
  let s : Fin 3 → ℤ := fun i => if 0 ≤ x (p i) then 1 else -1
  have hs : ∀ i, s i = 1 ∨ s i = -1 := by intro i; dsimp [s]; split <;> simp
  refine ⟨signed p s hs, ?_⟩
  funext i
  change s i * x (p i) = (x (p i)).natAbs
  rw [Int.natCast_natAbs]
  dsimp only [s]
  split <;> simp_all [abs_of_nonneg, abs_of_neg]

private lemma potential_three (x : Fin 3 → ℤ) :
    potential x = max (x 0).natAbs (max (x 1).natAbs
      (max (x 2).natAbs (((x 0).natAbs + (x 1).natAbs + (x 2).natAbs) / 2))) := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  simp [potential, norm, hu, Fin.sum_univ_three, max_assoc, add_assoc]

private lemma adj_iff (x y : L) : contactGraph.Adj x y ↔
    (∑ i, norm (y.1 - x.1) i) = 2 ∧ ∀ i, norm (y.1 - x.1) i ≤ 1 := by
  change (_ ∨ _ ∨ _) ↔ _
  have ha (z : ℤ) : |z| = 1 ↔ z.natAbs = 1 := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast Iff.rfl
  have hz (i : Fin 3) : y.1 i = x.1 i ↔ (y.1 i - x.1 i).natAbs = 0 := by
    simp only [Int.natAbs_eq_zero, sub_eq_zero]
  simp only [ha, hz, Fin.sum_univ_three, norm, Pi.sub_apply]
  constructor
  · intro h
    constructor
    · rcases h with h | h | h <;> omega
    · intro i
      fin_cases i
      · change (y.1 0 - x.1 0).natAbs ≤ 1
        rcases h with h | h | h <;> omega
      · change (y.1 1 - x.1 1).natAbs ≤ 1
        rcases h with h | h | h <;> omega
      · change (y.1 2 - x.1 2).natAbs ≤ 1
        rcases h with h | h | h <;> omega
  · intro ⟨h, hi⟩
    have h0 := hi 0
    have h1 := hi 1
    have h2 := hi 2
    omega

private lemma signed_adj (w : W) {x y : L} (h : contactGraph.Adj x y) :
    contactGraph.Adj (w • x) (w • y) := by
  rw [adj_iff] at h ⊢
  obtain ⟨p, s, hs, hw⟩ := w.2
  have he : (w • y).1 - (w • x).1 = w.1 (y.1 - x.1) := by
    funext i
    change w.1 y.1 i - w.1 x.1 i = _
    rw [hw, hw, hw]
    simp [mul_sub]
  obtain ⟨q, hq⟩ := norm_signed w
  rw [he, hq]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp]
  exact ⟨h.1, fun i => h.2 (q i)⟩

private lemma potential_step (x y : L) (h : contactGraph.Adj x y) :
    potential x.1 ≤ potential y.1 + 1 := by
  obtain ⟨he, hi⟩ := (adj_iff x y).mp h
  have ht (i : Fin 3) : norm x.1 i ≤ norm (y.1 - x.1) i + norm y.1 i := by
    have hh := Int.natAbs_add_le (x.1 i - y.1 i) (y.1 i)
    rw [sub_add_cancel] at hh
    simpa only [norm, Pi.sub_apply,
      show x.1 i - y.1 i = -(y.1 i - x.1 i) by omega, Int.natAbs_neg] using hh
  have ht0 := ht 0
  have ht1 := ht 1
  have ht2 := ht 2
  have hi0 := hi 0
  have hi1 := hi 1
  have hi2 := hi 2
  simp only [Fin.sum_univ_three] at he
  rw [potential_three, potential_three]
  dsimp only [norm] at *
  omega

private lemma nonnegative_descent (x : L) (h0 : 0 ≤ x.1 0)
    (h01 : x.1 0 ≤ x.1 1) (h12 : x.1 1 ≤ x.1 2) (hp : 0 < potential x.1) :
    ∃ y : L, contactGraph.Adj y x ∧ potential y.1 + 1 = potential x.1 := by
  have he := x.2
  simp only [Fin.sum_univ_three] at he
  by_cases hb : 0 < x.1 1
  · let y : L := ⟨![x.1 0, x.1 1 - 1, x.1 2 - 1], by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]; omega⟩
    refine ⟨y, ?_, ?_⟩
    · change _ ∨ _ ∨ _
      right; right
      dsimp [y]
      refine ⟨rfl, ?_, ?_⟩
      · rw [show x.1 1 - (x.1 1 - 1) = 1 by omega]; norm_num
      · rw [show x.1 2 - (x.1 2 - 1) = 1 by omega]; norm_num
    · rw [potential_three, potential_three]
      dsimp only [y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      omega
  · have hb0 : x.1 1 = 0 := by omega
    have hc0 : x.1 0 = 0 := by omega
    let y : L := ⟨![0, 1, x.1 2 - 1], by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]; omega⟩
    refine ⟨y, ?_, ?_⟩
    · change _ ∨ _ ∨ _
      right; right
      dsimp [y]
      simp [hc0, hb0, show x.1 2 - (x.1 2 - 1) = 1 by omega]
    · rw [potential_three] at hp
      rw [potential_three, potential_three]
      dsimp only [y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      simp only [hb0, hc0, Int.natAbs_zero, Int.natAbs_one] at hp ⊢
      omega

private lemma potential_descent (x : L) (h : 0 < potential x.1) :
    ∃ y : L, contactGraph.Adj y x ∧ potential y.1 + 1 = potential x.1 := by
  obtain ⟨w, hw⟩ := to_canonical x.1
  have hp : potential (w • x).1 = potential x.1 := potential_signed w x.1
  have hcoord (i : Fin 3) : (w • x).1 i = (canonical x.1 i : ℤ) := congrFun hw i
  have hm := canonical_mono x.1
  obtain ⟨y, hy, hpy⟩ := nonnegative_descent (w • x)
    (by rw [hcoord]; positivity)
    (by rw [hcoord, hcoord]; exact_mod_cast hm (show (0 : Fin 3) ≤ 1 by decide))
    (by rw [hcoord, hcoord]; exact_mod_cast hm (show (1 : Fin 3) ≤ 2 by decide))
    (by omega)
  refine ⟨w⁻¹ • y, ?_, ?_⟩
  · simpa only [inv_smul_smul] using signed_adj w⁻¹ hy
  · rw [show (w⁻¹ • y).1 = (w⁻¹).1 y.1 by rfl, potential_signed]
    omega

private lemma geodesic (x : L) :
    ∃ p : contactGraph.Walk origin x, p.length = potential x.1 := by
  generalize ht : potential x.1 = t
  induction t using Nat.strong_induction_on generalizing x with
  | h t ih =>
    by_cases hz : t = 0
    · have hx : x = origin := by
        apply Subtype.ext
        funext i
        have hi : norm x.1 i ≤ potential x.1 :=
          (Finset.le_sup (f := norm x.1) (Finset.mem_univ i)).trans (le_max_left _ _)
        change x.1 i = 0
        dsimp only [norm] at hi
        omega
      subst x
      exact ⟨.nil, by simp only [SimpleGraph.Walk.length_nil]; omega⟩
    · obtain ⟨y, hy, hpy⟩ := potential_descent x (by omega)
      obtain ⟨p, hl⟩ := ih (potential y.1) (by omega) y rfl
      refine ⟨p.append hy.toWalk, ?_⟩
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk, hl]
      omega

private lemma distance_formula (x : L) : d x = potential x.1 := by
  obtain ⟨p, hp⟩ := geodesic x
  apply le_antisymm
  · change contactGraph.dist origin x ≤ _
    simpa only [hp] using SimpleGraph.dist_le p
  · have hl :=
      D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation.potential_dist
        contactGraph (fun y => potential y.1) potential_step
          (SimpleGraph.Reachable.symm ⟨p⟩)
    have hzero : potential origin.1 = 0 := by rw [potential_three]; rfl
    rw [hzero, zero_add, SimpleGraph.dist_comm] at hl
    exact hl

private lemma monotone_three {α : Type*} [Preorder α] (z : Fin 3 → α) :
    Monotone z ↔ z 0 ≤ z 1 ∧ z 1 ≤ z 2 := by
  constructor
  · intro h; exact ⟨h (by decide), h (by decide)⟩
  · rintro ⟨h01, h12⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> exact le_trans h01 h12

private lemma canonical_section (z : Fin 3 → ℕ) (hz : Monotone z) :
    canonical (fun i => (z i : ℤ)) = z := by
  have hn : norm (fun i => (z i : ℤ)) = z := by funext i; simp [norm]
  dsimp only [canonical]
  rw [hn, (Tuple.sort_eq_refl_iff_monotone).mpr hz]
  rfl

private lemma potential_nat (z : Fin 3 → ℕ) (hz : Monotone z) :
    potential (fun i => (z i : ℤ)) = max (z 2) ((∑ i, z i) / 2) := by
  rw [potential_three]
  simp only [Int.natAbs_natCast, Fin.sum_univ_three]
  have hm := (monotone_three z).mp hz
  omega

private def Rep (n : ℕ) := {z : Fin 3 → ℕ //
  Monotone z ∧ (∑ i, z i) % 2 = 0 ∧ max (z 2) ((∑ i, z i) / 2) = n}

private def canonicalShell {n : ℕ} (x : Shell n) : Rep n := by
  refine ⟨canonical x.1.1, canonical_mono _, ?_, ?_⟩
  · have hs : ∑ i, canonical x.1.1 i = ∑ i, norm x.1.1 i := by
      dsimp only [canonical, Function.comp_apply]
      exact Equiv.sum_comp (Tuple.sort (norm x.1.1)) (norm x.1.1)
    rw [hs]
    have hp := parity_norm x.1.1
    have hx := x.1.2
    omega
  · obtain ⟨w, hw⟩ := to_canonical x.1.1
    have hp := potential_signed w x.1.1
    rw [hw, potential_nat _ (canonical_mono _), ← distance_formula x.1] at hp
    exact hp.trans x.2

private def repShell {n : ℕ} (z : Rep n) : Shell n := by
  have he : (∑ i, (z.1 i : ℤ)) % 2 = 0 := by
    have hz := z.2.2.1
    rw [← Nat.cast_sum]
    omega
  refine ⟨⟨fun i => (z.1 i : ℤ), he⟩, ?_⟩
  rw [distance_formula, potential_nat _ z.2.1]
  exact z.2.2.2

private lemma same_canonical (x y : L) :
    MulAction.orbitRel W L x y ↔ canonical x.1 = canonical y.1 := by
  constructor
  · rintro ⟨w, hw⟩
    have he : w.1 y.1 = x.1 := congrArg Subtype.val hw
    rw [← he, canonical_signed]
  · intro h
    obtain ⟨w, hw⟩ := to_canonical x.1
    obtain ⟨v, hv⟩ := to_canonical y.1
    have he : w • x = v • y := by
      apply Subtype.ext
      change w.1 x.1 = v.1 y.1
      rw [hw, hv, h]
    refine ⟨w⁻¹ * v, ?_⟩
    change (w⁻¹ * v) • y = x
    rw [mul_smul, ← he, inv_smul_smul]

private def orbitEquiv (n : ℕ) :
    Quotient ((MulAction.orbitRel W L).comap (Subtype.val : Shell n → L)) ≃ Rep n where
  toFun := Quotient.lift canonicalShell (by
    intro x y h
    apply Subtype.ext
    exact (same_canonical x.1 y.1).mp h)
  invFun := fun z => Quotient.mk _ (repShell z)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      apply Quotient.sound
      apply (same_canonical _ _).mpr
      change canonical (fun i => (canonical x.1.1 i : ℤ)) = canonical x.1.1
      exact canonical_section _ (canonical_mono _)
  right_inv := by
    intro z
    apply Subtype.ext
    change canonical (fun i => (z.1 i : ℤ)) = z.1
    exact canonical_section _ z.2.1

private def exteriorWeight (t : ℕ × ℕ × ℕ) : ℕ := 2*t.1 + t.2.1 + 2*t.2.2
private def interiorWeight (t : ℕ × ℕ × ℕ) : ℕ := 3*t.1 + 2*t.2.1 + t.2.2

private def exteriorRep {n : ℕ} (t : {t // exteriorWeight t = n}) : Rep n := by
  refine ⟨![t.1.1, t.1.1 + t.1.2.1, 2*t.1.1 + t.1.2.1 + 2*t.1.2.2], ?_, ?_, ?_⟩
  · rw [monotone_three]; dsimp; omega
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]; omega
  · have ht := t.2
    dsimp only [exteriorWeight] at ht
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]; omega

private def interiorRep {n : ℕ} (t : {t // 3 + interiorWeight t = n}) : Rep n := by
  refine ⟨![2 + 2*t.1.1 + t.1.2.1, 2 + 2*t.1.1 + t.1.2.1 + t.1.2.2,
    2 + 2*t.1.1 + 2*t.1.2.1 + t.1.2.2], ?_, ?_, ?_⟩
  · rw [monotone_three]; dsimp; omega
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]; omega
  · have ht := t.2
    dsimp only [interiorWeight] at ht
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]; omega

private def coneEquiv (n : ℕ) :
    {t // exteriorWeight t = n} ⊕ {t // 3 + interiorWeight t = n} ≃ Rep n := by
  let f : {t // exteriorWeight t = n} ⊕ {t // 3 + interiorWeight t = n} → Rep n :=
    Sum.elim exteriorRep interiorRep
  apply Equiv.ofBijective f
  constructor
  · intro t u h
    have h0 := congrFun (congrArg Subtype.val h) 0
    have h1 := congrFun (congrArg Subtype.val h) 1
    have h2 := congrFun (congrArg Subtype.val h) 2
    rcases t with t | t <;> rcases u with u | u
    · apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext
      · dsimp [f, exteriorRep] at h0; exact h0
      · apply Prod.ext <;> dsimp [f, exteriorRep] at h0 h1 h2 <;> omega
    · dsimp [f, exteriorRep, interiorRep] at h0 h1 h2
      omega
    · dsimp [f, exteriorRep, interiorRep] at h0 h1 h2
      omega
    · apply congrArg Sum.inr
      apply Subtype.ext
      apply Prod.ext
      · dsimp [f, interiorRep] at h0 h1 h2; omega
      · apply Prod.ext <;> dsimp [f, interiorRep] at h0 h1 h2 <;> omega
  · intro z
    obtain ⟨h01, h12⟩ := (monotone_three z.1).mp z.2.1
    have he := z.2.2.1
    have hn := z.2.2.2
    simp only [Fin.sum_univ_three] at he hn
    by_cases h : z.1 1 + z.1 0 ≤ z.1 2
    · let t : ℕ × ℕ × ℕ := (z.1 0, z.1 1 - z.1 0, (z.1 2 - z.1 1 - z.1 0) / 2)
      have ht : exteriorWeight t = n := by dsimp [exteriorWeight, t]; omega
      refine ⟨Sum.inl ⟨t, ht⟩, ?_⟩
      apply Subtype.ext
      funext i; fin_cases i <;> dsimp [f, exteriorRep, t] <;> omega
    · let p := (z.1 1 + z.1 0 - z.1 2) / 2
      let q := (z.1 2 + z.1 0 - z.1 1) / 2
      let r := (z.1 2 + z.1 1 - z.1 0) / 2
      have hp : 0 < p := by dsimp [p]; omega
      have hpq : p ≤ q := by dsimp [p, q]; omega
      have hqr : q ≤ r := by dsimp [q, r]; omega
      have hc : z.1 0 = p + q := by dsimp [p, q]; omega
      have hb : z.1 1 = p + r := by dsimp [p, r]; omega
      have ha : z.1 2 = q + r := by dsimp [q, r]; omega
      let t : ℕ × ℕ × ℕ := (p - 1, q - p, r - q)
      have ht : 3 + interiorWeight t = n := by dsimp [interiorWeight, t]; omega
      refine ⟨Sum.inr ⟨t, ht⟩, ?_⟩
      apply Subtype.ext
      funext i; fin_cases i <;> dsimp [f, interiorRep, t] <;> omega

private abbrev Fiber {α : Type} (f : α → ℕ) (n : ℕ) := {x // f x = n}

private def fiberAddEquiv {α β : Type} (f : α → ℕ) (g : β → ℕ) (n : ℕ) :
    Fiber (fun xy : α × β => f xy.1 + g xy.2) n ≃
      Σ ij : (Finset.antidiagonal n), Fiber f ij.1.1 × Fiber g ij.1.2 where
  toFun xy := ⟨⟨(f xy.1.1, g xy.1.2), by
    simpa only [Finset.mem_antidiagonal] using xy.2⟩,
    ⟨xy.1.1, rfl⟩, ⟨xy.1.2, rfl⟩⟩
  invFun z := ⟨(z.2.1.1, z.2.2.1), by
    change f z.2.1.1 + g z.2.2.1 = n
    rw [z.2.1.2, z.2.2.2]
    exact Finset.mem_antidiagonal.mp z.1.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟨i, j⟩, hij⟩, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩⟩
    dsimp only at hx hy
    subst i; subst j
    rfl

private lemma finite_add_fiber {α β : Type} (f : α → ℕ) (g : β → ℕ)
    (hf : ∀ n, Finite (Fiber f n)) (hg : ∀ n, Finite (Fiber g n)) (n : ℕ) :
    Finite (Fiber (fun xy : α × β => f xy.1 + g xy.2) n) := by
  letI := hf
  letI := hg
  exact Finite.of_equiv _ (fiberAddEquiv f g n).symm

private def countingSeries {α : Type} (f : α → ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (Nat.card (Fiber f n) : ℤ))

private lemma counting_mul {α β : Type} (f : α → ℕ) (g : β → ℕ)
    (hf : ∀ n, Finite (Fiber f n)) (hg : ∀ n, Finite (Fiber g n)) :
    countingSeries (fun xy : α × β => f xy.1 + g xy.2) =
      countingSeries f * countingSeries g := by
  letI := hf
  letI := hg
  ext n
  simp only [countingSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [Nat.card_congr (fiberAddEquiv f g n), Nat.card_sigma]
  simp only [Nat.card_prod, Nat.cast_sum, Nat.cast_mul]
  exact Finset.sum_coe_sort (Finset.antidiagonal n)
    (fun ij : ℕ × ℕ => (Nat.card (Fiber f ij.1) : ℤ) * (Nat.card (Fiber g ij.2) : ℤ))

private lemma finite_linear (w : ℕ) (hw : 0 < w) (n : ℕ) :
    Finite (Fiber (fun k => w*k) n) := by
  haveI : Subsingleton (Fiber (fun k => w*k) n) := ⟨by
    intro x y
    apply Subtype.ext
    exact Nat.eq_of_mul_eq_mul_left hw (x.2.trans y.2.symm)⟩
  infer_instance

private lemma linear_series (w : ℕ) (hw : 0 < w) :
    countingSeries (fun k => w*k) =
      PowerSeries.expand w (by omega) (PowerSeries.mk 1 : PowerSeries ℤ) := by
  ext n
  simp only [countingSeries, PowerSeries.coeff_mk, PowerSeries.coeff_expand,
    Pi.one_apply]
  haveI : Subsingleton (Fiber (fun k => w*k) n) := ⟨by
    intro x y
    apply Subtype.ext
    exact Nat.eq_of_mul_eq_mul_left hw (x.2.trans y.2.symm)⟩
  by_cases h : w ∣ n
  · obtain ⟨k, hk⟩ := h
    have hc : Nat.card (Fiber (fun k => w*k) n) = 1 :=
      Nat.card_of_subsingleton ⟨k, hk.symm⟩
    rw [hc, ite_eq_left ⟨k, hk⟩]
    rfl
  · haveI : IsEmpty (Fiber (fun k => w*k) n) := ⟨fun x => h ⟨x.1, x.2.symm⟩⟩
    simp [h]

private lemma linear_denominator (w : ℕ) (hw : 0 < w) :
    (1 - PowerSeries.X ^ w) * countingSeries (fun k => w*k) = 1 := by
  rw [linear_series w hw]
  have h := congrArg (PowerSeries.expand w (show w ≠ 0 by omega))
    (PowerSeries.mk_one_mul_one_sub_eq_one ℤ)
  simpa only [map_mul, map_sub, map_one, PowerSeries.expand_X, mul_comm] using h

private lemma counting_shift {α : Type} (f : α → ℕ) (k : ℕ) :
    countingSeries (fun x => k + f x) = PowerSeries.X ^ k * countingSeries f := by
  ext n
  simp only [countingSeries, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
  by_cases h : k ≤ n
  · rw [ite_eq_left h]
    exact_mod_cast Nat.card_congr (Equiv.subtypeEquivRight (fun x => by dsimp only; omega) :
      Fiber (fun x => k + f x) n ≃ Fiber f (n-k))
  · haveI : IsEmpty (Fiber (fun x => k + f x) n) := ⟨fun x => by
      have hx := x.2
      change k + f x.1 = n at hx
      omega⟩
    simp [h]

private lemma exterior_finite (n : ℕ) : Finite (Fiber exteriorWeight n) := by
  have hf := finite_add_fiber (fun j : ℕ => j) (fun k => 2*k)
    (fun m => by simpa only [one_mul] using finite_linear 1 (by decide) m)
    (finite_linear 2 (by decide))
  have hg := finite_add_fiber (fun i => 2*i) (fun t : ℕ × ℕ => t.1 + 2*t.2)
    (finite_linear 2 (by decide)) hf n
  letI := hg
  exact Finite.of_equiv _ (Equiv.subtypeEquivRight (fun _ => by
    dsimp [exteriorWeight]; omega) :
      Fiber (fun t : ℕ × ℕ × ℕ => 2*t.1 + (t.2.1 + 2*t.2.2)) n ≃
        Fiber exteriorWeight n)

private lemma interior_finite (n : ℕ) : Finite (Fiber (fun t => 3 + interiorWeight t) n) := by
  apply Finite.of_injective
    (fun t : Fiber (fun t => 3 + interiorWeight t) n =>
      ((⟨t.1.1, by have ht := t.2; dsimp [interiorWeight] at ht; omega⟩ : Fin (n+1)),
       (⟨t.1.2.1, by have ht := t.2; dsimp [interiorWeight] at ht; omega⟩ : Fin (n+1)),
       (⟨t.1.2.2, by have ht := t.2; dsimp [interiorWeight] at ht; omega⟩ : Fin (n+1))))
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z => z.1.val) h)
    (Prod.ext (congrArg (fun z => z.2.1.val) h) (congrArg (fun z => z.2.2.val) h))

private lemma orbit_count (n : ℕ) : A n =
    Nat.card (Fiber exteriorWeight n) + Nat.card (Fiber (fun t => 3 + interiorWeight t) n) := by
  letI := exterior_finite n
  letI := interior_finite n
  rw [A, Nat.card_congr (orbitEquiv n), ← Nat.card_congr (coneEquiv n), Nat.card_sum]

private lemma exterior_series : countingSeries exteriorWeight =
    countingSeries (fun k => 2*k) *
      (countingSeries (fun k : ℕ => k) * countingSeries (fun k => 2*k)) := by
  have h1 := counting_mul (fun j : ℕ => j) (fun k => 2*k)
    (fun m => by simpa only [one_mul] using finite_linear 1 (by decide) m)
    (finite_linear 2 (by decide))
  have hf := finite_add_fiber (fun j : ℕ => j) (fun k => 2*k)
    (fun m => by simpa only [one_mul] using finite_linear 1 (by decide) m)
    (finite_linear 2 (by decide))
  have h2 := counting_mul (fun i => 2*i) (fun t : ℕ × ℕ => t.1 + 2*t.2)
    (finite_linear 2 (by decide)) hf
  have he : exteriorWeight = fun t : ℕ × ℕ × ℕ => 2*t.1 + (t.2.1 + 2*t.2.2) := by
    funext t; dsimp [exteriorWeight]; omega
  rw [he, h2, h1]

private lemma interior_series : countingSeries interiorWeight =
    countingSeries (fun k => 3*k) *
      (countingSeries (fun k => 2*k) * countingSeries (fun k : ℕ => k)) := by
  have h1 := counting_mul (fun j => 2*j) (fun k : ℕ => k)
    (finite_linear 2 (by decide))
    (fun m => by simpa only [one_mul] using finite_linear 1 (by decide) m)
  have hf := finite_add_fiber (fun j => 2*j) (fun k : ℕ => k)
    (finite_linear 2 (by decide))
    (fun m => by simpa only [one_mul] using finite_linear 1 (by decide) m)
  have h2 := counting_mul (fun i => 3*i) (fun t : ℕ × ℕ => 2*t.1 + t.2)
    (finite_linear 3 (by decide)) hf
  have he : interiorWeight = fun t : ℕ × ℕ × ℕ => 3*t.1 + (2*t.2.1 + t.2.2) := by
    funext t; dsimp [interiorWeight]; omega
  rw [he, h2, h1]

/-- The shell-orbit generating function, as a formal power series over the integers. -/
theorem result :
    (1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2)^2 * (1 - PowerSeries.X ^ 3) *
      (PowerSeries.mk fun n => (A n : ℤ)) = 1 - PowerSeries.X ^ 5 := by
  have hs : (PowerSeries.mk fun n => (A n : ℤ)) =
      countingSeries exteriorWeight + PowerSeries.X^3 * countingSeries interiorWeight := by
    rw [← counting_shift]
    ext n
    simp only [PowerSeries.coeff_mk, map_add, countingSeries]
    exact_mod_cast orbit_count n
  rw [hs, exterior_series, interior_series]
  have h1 := linear_denominator 1 (by decide)
  have h2 := linear_denominator 2 (by decide)
  have h3 := linear_denominator 3 (by decide)
  simp only [pow_one, one_mul] at h1
  calc
    _ = (1 - PowerSeries.X ^ 3) *
          (((1 - PowerSeries.X) * countingSeries (fun k : ℕ => k)) *
           ((1 - PowerSeries.X ^ 2) * countingSeries (fun k => 2*k))^2) +
        PowerSeries.X ^ 3 * (1 - PowerSeries.X ^ 2) *
          (((1 - PowerSeries.X) * countingSeries (fun k : ℕ => k)) *
           ((1 - PowerSeries.X ^ 2) * countingSeries (fun k => 2*k)) *
           ((1 - PowerSeries.X ^ 3) * countingSeries (fun k => 3*k))) := by ring
    _ = 1 - PowerSeries.X ^ 5 := by rw [h1, h2, h3]; ring

end D5.S3.StatisticalMechanics.FccPointGroupShells
