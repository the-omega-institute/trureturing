/-
PRIVATE REPLACEMENT SOURCE — UNCOMPILED.
Replaces the probability layer of candidate
10698d58c2c5418955ac69bf2e045ac49cd69ac3406e46270dd93f6f51ebc4df.
The original cycle geometry is retained once, below. No rational laws or casts.
No compilation, axiom inspection, independent review, admission, or delivery
into the upstream repository has occurred. This is source for later validation.
-/

import D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
import D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope
import D5.S3.TotalVariation.Metric

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.CircularWords.PairedDeletionSharpness

open MeasureTheory
open scoped BigOperators
open CircularDeletionTransport CyclicInsertionGap
open D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope
open D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope
open D5.S3.TotalVariation.Pinsker

universe u v

variable {α : Type u} [DecidableEq α]

/-! The following geometry is reused from 10698d58, without a second copy. -/

/-- A finite linear prefix followed by the unchanged remainder, in the actual
quotient by rotation. Reversal is never quotiented out. -/
def word (P L : List α) : Cycle α := (P ++ L : List α)

/-- With a nonempty common remainder, a nodup prefix word remembers the entire
prefix. Rotate to the first element of the remainder and use the published
anchored injection. -/
theorem word_prefix_injective {P Q L : List α} (hL : L ≠ [])
    (hn : (P ++ L).Nodup) (he : word P L = word Q L) : P = Q := by
  cases L with
  | nil => exact (hL rfl).elim
  | cons r T =>
    have hP : word P (r :: T) = (r :: (T ++ P) : List α) :=
      Cycle.coe_eq_coe.mpr (List.isRotated_append (l := P) (l' := r :: T))
    have hQ : word Q (r :: T) = (r :: (T ++ Q) : List α) :=
      Cycle.coe_eq_coe.mpr (List.isRotated_append (l := Q) (l' := r :: T))
    have hn' : (r :: (T ++ P)).Nodup := by
      apply Cycle.nodup_coe_iff.mp
      rw [← hP]
      exact Cycle.nodup_coe_iff.mpr hn
    have ht : T ++ P = T ++ Q :=
      anchored_coe_injective hn' (hP.symm.trans (he.trans hQ))
    exact List.append_cancel_left ht

private theorem filter_of_not_mem (x : α) (L : List α) (hx : x ∉ L) :
    L.filter (fun y => decide (y ≠ x)) = L := by
  apply List.filter_eq_self.mpr
  intro y hy
  simp only [decide_eq_true_eq]
  exact fun he => hx (he ▸ hy)

theorem delete_word (x : α) (P L : List α) (hx : x ∉ L) :
    delete x (word P L) = word (P.filter (fun y => decide (y ≠ x))) L := by
  change (((P ++ L).filter (fun y => decide (y ≠ x))) : Cycle α) = _
  rw [List.filter_append, filter_of_not_mem x L hx]
  rfl

def prefixes (a b c : α) : Fin 6 → List α :=
  ![[a,b,c], [b,a,c], [a,c,b], [c,b,a], [c,a,b], [b,c,a]]

/-- Indices 0,1,2,3,4,5 are respectively C, CF, CG, E, EF, EG. -/
def six (a b c : α) (L : List α) (i : Fin 6) : Cycle α :=
  word (prefixes a b c i) L

def F (a b : α) (C : Cycle α) : Cycle α × Cycle α := (delete a C, delete b C)
def G (b c : α) (C : Cycle α) : Cycle α × Cycle α := (delete b C, delete c C)

theorem prefixes_nodup (a b c : α) (L : List α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hL : L.Nodup) (haL : a ∉ L) (hbL : b ∉ L) (hcL : c ∉ L)
    (i : Fin 6) : (prefixes a b c i ++ L).Nodup := by
  fin_cases i <;>
    simp [prefixes, hab, hac, hbc, hab.symm, hac.symm, hbc.symm, hL, haL, hbL, hcL]

theorem six_nodup (a b c : α) (L : List α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hL : L.Nodup) (haL : a ∉ L) (hbL : b ∉ L) (hcL : c ∉ L)
    (i : Fin 6) : (six a b c L i).Nodup :=
  Cycle.nodup_coe_iff.mpr (prefixes_nodup a b c L hab hac hbc hL haL hbL hcL i)

theorem six_toFinset (a b c : α) (L : List α) (i : Fin 6) :
    (six a b c L i).toFinset = insert a (insert b (insert c L.toFinset)) := by
  fin_cases i <;> ext x <;>
    simp [six, prefixes, word, or_left_comm, or_comm, or_assoc]

theorem six_injective (a b c : α) (L : List α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hL : L.Nodup) (hL0 : L ≠ []) (haL : a ∉ L) (hbL : b ∉ L) (hcL : c ∉ L) :
    Function.Injective (six a b c L) := by
  intro i j he
  have hp : prefixes a b c i = prefixes a b c j :=
    word_prefix_injective hL0
      (prefixes_nodup a b c L hab hac hbc hL haL hbL hcL i) he
  fin_cases i <;> fin_cases j <;>
    simp_all [prefixes, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]

theorem two_word_ne (x y : α) (L : List α) (hxy : x ≠ y)
    (hL : L.Nodup) (hL0 : L ≠ []) (hxL : x ∉ L) (hyL : y ∉ L) :
    word [x,y] L ≠ word [y,x] L := by
  intro he
  have hp : [x,y] = [y,x] :=
    word_prefix_injective hL0 (by simp [hxy, hL, hxL, hyL]) he
  exact hxy (List.cons.inj hp).1

/-- The four channel cancellations are equalities of actual ordered deletion
pairs, before any law or signed coefficient is introduced. -/
theorem actual_cancellations (a b c : α) (L : List α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haL : a ∉ L) (hbL : b ∉ L) (hcL : c ∉ L) :
    F a b (six a b c L 1) = F a b (six a b c L 0) ∧
    F a b (six a b c L 3) = F a b (six a b c L 4) ∧
    G b c (six a b c L 2) = G b c (six a b c L 0) ∧
    G b c (six a b c L 3) = G b c (six a b c L 5) := by
  simp [F, G, six, prefixes, delete_word, haL, hbL, hcL,
    hab, hac, hbc, hab.symm, hac.symm, hbc.symm]

theorem actual_survivors_ne (a b c : α) (L : List α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hL : L.Nodup) (hL0 : L ≠ []) (haL : a ∉ L) (hbL : b ∉ L) (hcL : c ∉ L) :
    F a b (six a b c L 2) ≠ F a b (six a b c L 5) ∧
    G b c (six a b c L 1) ≠ G b c (six a b c L 4) := by
  constructor
  · intro he
    have hd := congrArg Prod.fst he
    have hd' : word [c,b] L = word [b,c] L := by
      simpa [F, six, prefixes, delete_word, haL,
        hab, hac, hbc, hab.symm, hac.symm, hbc.symm] using hd
    exact two_word_ne c b L hbc.symm hL hL0 hcL hbL hd'
  · intro he
    have hd := congrArg Prod.fst he
    have hd' : word [a,c] L = word [c,a] L := by
      simpa [G, six, prefixes, delete_word, hbL,
        hab, hac, hbc, hab.symm, hac.symm, hbc.symm] using hd
    exact two_word_ne a c L hac hL hL0 haL hcL hd'

def remainder (A : Finset α) (a b c : α) : Finset α := ((A.erase a).erase b).erase c

theorem listing_properties (A : Finset α) (hA : 4 ≤ A.card) (a b c : α)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (L : List α) (hS : L.toFinset = remainder A a b c) :
    L ≠ [] ∧ a ∉ L ∧ b ∉ L ∧ c ∉ L ∧
      insert a (insert b (insert c L.toFinset)) = A := by
  have hb' : b ∈ A.erase a := by simp [hb, hab.symm]
  have hc' : c ∈ (A.erase a).erase b := by simp [hc, hac.symm, hbc.symm]
  have hca := Finset.card_erase_add_one ha
  have hcb := Finset.card_erase_add_one hb'
  have hcc := Finset.card_erase_add_one hc'
  have hpos : 0 < (remainder A a b c).card := by dsimp [remainder]; omega
  have hL0 : L ≠ [] := by
    intro he
    have hz : (remainder A a b c).card = 0 := by rw [← hS, he]; rfl
    omega
  have haL : a ∉ L := by
    intro he
    have hm := List.mem_toFinset.mpr he
    rw [hS] at hm
    simp [remainder] at hm
  have hbL : b ∉ L := by
    intro he
    have hm := List.mem_toFinset.mpr he
    rw [hS] at hm
    simp [remainder] at hm
  have hcL : c ∉ L := by
    intro he
    have hm := List.mem_toFinset.mpr he
    rw [hS] at hm
    simp [remainder] at hm
  refine ⟨hL0, haL, hbL, hcL, ?_⟩
  rw [hS, remainder, Finset.insert_erase hc', Finset.insert_erase hb', Finset.insert_erase ha]

/-! Native finite real coordinates. These helpers are used by the construction;
there is no coefficient-change or rational-to-measure layer. -/

section RealCoordinates
variable {W V : Type*} [Fintype W] [Fintype V]

def spike (x : W) (q : ℝ) : W → ℝ := by
  classical
  exact fun t => if x = t then q else 0

def thirds (x y z : W) : W → ℝ :=
  spike x (1 / 3) + spike y (1 / 3) + spike z (1 / 3)

private theorem thirds_mem_simplex (x y z : W) :
    thirds x y z ∈ stdSimplex ℝ W := by
  classical
  constructor
  · intro t
    simp only [thirds, Pi.add_apply, spike]
    split_ifs <;> norm_num
  · norm_num [thirds, spike, Finset.sum_add_distrib]

private theorem pushMass_spike (f : W → V) (x : W) (q : ℝ) :
    pushMass f (spike x q) = spike (f x) q := by
  classical
  funext v
  change (∑ w, if f w = v then (if x = w then q else 0) else 0) =
    if f x = v then q else 0
  have he (w : W) :
      (if f w = v then (if x = w then q else 0) else 0) =
        if x = w then (if f x = v then q else 0) else 0 := by
    by_cases h : x = w
    · subst w
      simp
    · simp [h]
  simp_rw [he]
  simp

private theorem pushMass_thirds (f : W → V) (x y z : W) :
    pushMass f (thirds x y z) = thirds (f x) (f y) (f z) := by
  simp only [thirds, map_add, pushMass_spike]

private theorem tv_disjoint_simplex (p q : W → ℝ)
    (hp : p ∈ stdSimplex ℝ W) (hq : q ∈ stdSimplex ℝ W)
    (hd : ∀ t, p t = 0 ∨ q t = 0) : totalVariation p q = 1 := by
  have hab (t : W) : |p t - q t| = p t + q t := by
    rcases hd t with h | h
    · simp [h, abs_of_nonneg (hq.1 t)]
    · simp [h, abs_of_nonneg (hp.1 t)]
  simp_rw [totalVariation, hab]
  rw [Finset.sum_add_distrib, hp.2, hq.2]
  norm_num

private theorem tv_dipole (p q : W → ℝ) (x y : W) (r : ℝ)
    (hxy : x ≠ y) (hr : 0 ≤ r)
    (hd : p - q = spike x r - spike y r) : totalVariation p q = r := by
  classical
  have hab (t : W) : |(spike x r - spike y r) t| =
      spike x r t + spike y r t := by
    by_cases hx : x = t
    · subst t
      simp [spike, hxy.symm, abs_of_nonneg hr]
    · by_cases hy : y = t
      · subst t
        simp [spike, hxy, abs_of_nonneg hr]
      · simp [spike, hx, hy]
  have hs : (∑ t, |p t - q t|) = r + r := by
    change (∑ t, |(p - q) t|) = r + r
    rw [hd]
    simp_rw [hab]
    simp [Finset.sum_add_distrib, spike]
  rw [totalVariation, hs]
  ring

private theorem thirds_zero (x y z t : W)
    (hx : x ≠ t) (hy : y ≠ t) (hz : z ≠ t) : thirds x y z t = 0 := by
  simp [thirds, spike, hx, hy, hz]

private theorem six_thirds_tv (s : Fin 6 → W) (hi : Function.Injective s) :
    totalVariation (thirds (s 1) (s 2) (s 3)) (thirds (s 0) (s 4) (s 5)) = 1 := by
  apply tv_disjoint_simplex _ _ (thirds_mem_simplex _ _ _) (thirds_mem_simplex _ _ _)
  intro t
  have hne (i j : Fin 6) (hij : i ≠ j) : s i ≠ s j :=
    fun h => hij (hi h)
  by_cases ht : s 1 = t ∨ s 2 = t ∨ s 3 = t
  · right
    rcases ht with ht | ht | ht
    all_goals
      subst t
      apply thirds_zero
      · exact hne _ _ (by decide)
      · exact hne _ _ (by decide)
      · exact hne _ _ (by decide)
  · left
    push_neg at ht
    exact thirds_zero _ _ _ _ ht.1 ht.2.1 ht.2.2

end RealCoordinates

/-! A finite carrier of actual cycles, and the exact realized ranges of the
actual paired deletions. The ambient label type is not required to be finite. -/

def sourceSet (a b c : α) (L : List α) : Finset (Cycle α) :=
  Finset.univ.image (six a b c L)

abbrev Source (a b c : α) (L : List α) := ↥(sourceSet a b c L)

def sourceCycle (a b c : α) (L : List α) (i : Fin 6) : Source a b c L :=
  ⟨six a b c L i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

def outputSet (a b c : α) (L : List α)
    (f : Cycle α → Cycle α × Cycle α) : Finset (Cycle α × Cycle α) :=
  (sourceSet a b c L).image f

abbrev Output (a b c : α) (L : List α)
    (f : Cycle α → Cycle α × Cycle α) := ↥(outputSet a b c L f)

def realized (a b c : α) (L : List α) (f : Cycle α → Cycle α × Cycle α)
    (C : Source a b c L) : Output a b c L f :=
  ⟨f C.val, Finset.mem_image.mpr ⟨C.val, C.property, rfl⟩⟩

/-- Equality in the realized range is precisely equality of the original pairs.
This consumed helper justifies every cancellation and non-cancellation below. -/
private theorem realized_eq_iff (a b c : α) (L : List α)
    (f : Cycle α → Cycle α × Cycle α) (C D : Source a b c L) :
    realized a b c L f C = realized a b c L f D ↔ f C.val = f D.val := by
  constructor
  · exact congrArg Subtype.val
  · exact Subtype.ext

def fChannel (a b c : α) (L : List α) :
    Source a b c L → Output a b c L (F a b) := realized a b c L (F a b)

def gChannel (a b c : α) (L : List α) :
    Source a b c L → Output a b c L (G b c) := realized a b c L (G b c)

instance sourceMeasurableSpace (a b c : α) (L : List α) :
    MeasurableSpace (Source a b c L) := ⊤

instance sourceMeasurableSingletonClass (a b c : α) (L : List α) :
    MeasurableSingletonClass (Source a b c L) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance outputMeasurableSpace (a b c : α) (L : List α)
    (f : Cycle α → Cycle α × Cycle α) : MeasurableSpace (Output a b c L f) := ⊤

instance outputMeasurableSingletonClass (a b c : α) (L : List α)
    (f : Cycle α → Cycle α × Cycle α) :
    MeasurableSingletonClass (Output a b c L f) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def muMass (a b c : α) (L : List α) : Source a b c L → ℝ :=
  thirds (sourceCycle a b c L 1) (sourceCycle a b c L 2) (sourceCycle a b c L 3)

def nuMass (a b c : α) (L : List α) : Source a b c L → ℝ :=
  thirds (sourceCycle a b c L 0) (sourceCycle a b c L 4) (sourceCycle a b c L 5)

def muLaw (a b c : α) (L : List α) : ProbabilityMeasure (Source a b c L) :=
  lawOfMass ⟨muMass a b c L, thirds_mem_simplex _ _ _⟩

def nuLaw (a b c : α) (L : List α) : ProbabilityMeasure (Source a b c L) :=
  lawOfMass ⟨nuMass a b c L, thirds_mem_simplex _ _ _⟩

private theorem sourceCycle_injective (a b c : α) (L : List α)
    (hi : Function.Injective (six a b c L)) :
    Function.Injective (sourceCycle a b c L) := by
  intro i j hij
  exact hi (congrArg Subtype.val hij)

private theorem source_legal (A : Finset α) (a b c : α) (L : List α)
    (hn : ∀ i, (six a b c L i).Nodup)
    (hs : ∀ i, (six a b c L i).toFinset = A) :
    ∀ C : Source a b c L, C.val.Nodup ∧ C.val.toFinset = A := by
  intro C
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp C.property
  rw [← hi]
  exact ⟨hn i, hs i⟩

private theorem signed_pushforwards (a b c : α) (L : List α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haL : a ∉ L) (hbL : b ∉ L) (hcL : c ∉ L) :
    pushMass (fChannel a b c L) (muMass a b c L) -
        pushMass (fChannel a b c L) (nuMass a b c L) =
      spike (fChannel a b c L (sourceCycle a b c L 2)) (1 / 3) -
        spike (fChannel a b c L (sourceCycle a b c L 5)) (1 / 3) ∧
    pushMass (gChannel a b c L) (muMass a b c L) -
        pushMass (gChannel a b c L) (nuMass a b c L) =
      spike (gChannel a b c L (sourceCycle a b c L 1)) (1 / 3) -
        spike (gChannel a b c L (sourceCycle a b c L 4)) (1 / 3) := by
  obtain ⟨hF1, hF3, hG2, hG3⟩ := actual_cancellations a b c L hab hac hbc haL hbL hcL
  have hF1' : fChannel a b c L (sourceCycle a b c L 1) =
      fChannel a b c L (sourceCycle a b c L 0) :=
    (realized_eq_iff a b c L (F a b) _ _).mpr hF1
  have hF3' : fChannel a b c L (sourceCycle a b c L 3) =
      fChannel a b c L (sourceCycle a b c L 4) :=
    (realized_eq_iff a b c L (F a b) _ _).mpr hF3
  have hG2' : gChannel a b c L (sourceCycle a b c L 2) =
      gChannel a b c L (sourceCycle a b c L 0) :=
    (realized_eq_iff a b c L (G b c) _ _).mpr hG2
  have hG3' : gChannel a b c L (sourceCycle a b c L 3) =
      gChannel a b c L (sourceCycle a b c L 5) :=
    (realized_eq_iff a b c L (G b c) _ _).mpr hG3
  constructor
  · simp only [muMass, nuMass, pushMass_thirds, thirds]
    rw [hF1', hF3']
    abel
  · simp only [muMass, nuMass, pushMass_thirds, thirds]
    rw [hG2', hG3']
    abel

private theorem channel_survivors_ne (a b c : α) (L : List α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hL : L.Nodup) (hL0 : L ≠ []) (haL : a ∉ L) (hbL : b ∉ L) (hcL : c ∉ L) :
    fChannel a b c L (sourceCycle a b c L 2) ≠
        fChannel a b c L (sourceCycle a b c L 5) ∧
    gChannel a b c L (sourceCycle a b c L 1) ≠
        gChannel a b c L (sourceCycle a b c L 4) := by
  obtain ⟨hF, hG⟩ := actual_survivors_ne a b c L hab hac hbc hL hL0 haL hbL hcL
  constructor
  · exact fun h => hF ((realized_eq_iff a b c L (F a b) _ _).mp h)
  · exact fun h => hG ((realized_eq_iff a b c L (G b c) _ _).mp h)

/-! One substantive terminal construction. The coefficient implications are
proved inside this construction, with the same native-law witnesses. There
are no standalone terminal specialization wrappers. -/

/-- For every legal finite support and every prescribed distinct supported
triple, construct real native probabilities on actual cycles with source TV
one and both overlapping paired-deletion TVs one third. Any sum/max inverse
coefficient valid for all native laws on this carrier is at least 3/2 or 3.

All three TVs use the repository's real finite half-l1 function applied to
singleton masses of actual ProbabilityMeasures. No rational TV is cast. -/
theorem real_probability_paired_deletion_sharpness
    (A : Finset α) (hA : 4 ≤ A.card) (a b c : α)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ L : List α, L.Nodup ∧ L.toFinset = remainder A a b c ∧ L ≠ [] ∧
      (∀ C : Source a b c L, C.val.Nodup ∧ C.val.toFinset = A) ∧
      Function.Injective (sourceCycle a b c L) ∧
      ∃ ρ σ : ProbabilityMeasure (Source a b c L),
        massVector ρ = muMass a b c L ∧ massVector σ = nuMass a b c L ∧
        totalVariation (massVector ρ) (massVector σ) = 1 ∧
        totalVariation (massVector (ρ.map (fChannel a b c L)))
          (massVector (σ.map (fChannel a b c L))) = 1 / 3 ∧
        totalVariation (massVector (ρ.map (gChannel a b c L)))
          (massVector (σ.map (gChannel a b c L))) = 1 / 3 ∧
        (∀ K : ℝ,
          (∀ m n : ProbabilityMeasure (Source a b c L),
            totalVariation (massVector m) (massVector n) ≤ K *
              (totalVariation (massVector (m.map (fChannel a b c L)))
                (massVector (n.map (fChannel a b c L))) +
               totalVariation (massVector (m.map (gChannel a b c L)))
                (massVector (n.map (gChannel a b c L))))) → (3 / 2 : ℝ) ≤ K) ∧
        (∀ K : ℝ,
          (∀ m n : ProbabilityMeasure (Source a b c L),
            totalVariation (massVector m) (massVector n) ≤ K * max
              (totalVariation (massVector (m.map (fChannel a b c L)))
                (massVector (n.map (fChannel a b c L))))
              (totalVariation (massVector (m.map (gChannel a b c L)))
                (massVector (n.map (gChannel a b c L))))) → (3 : ℝ) ≤ K) := by
  obtain ⟨L, hL, hS⟩ := Finset.exists_list_nodup_eq (remainder A a b c)
  obtain ⟨hL0, haL, hbL, hcL, hs⟩ :=
    listing_properties A hA a b c ha hb hc hab hac hbc L hS
  have hn := six_nodup a b c L hab hac hbc hL haL hbL hcL
  have hsupp (i : Fin 6) : (six a b c L i).toFinset = A :=
    (six_toFinset a b c L i).trans hs
  have hi := sourceCycle_injective a b c L
    (six_injective a b c L hab hac hbc hL hL0 haL hbL hcL)
  have hsource : totalVariation (muMass a b c L) (nuMass a b c L) = 1 :=
    six_thirds_tv (sourceCycle a b c L) hi
  obtain ⟨hsF, hsG⟩ := signed_pushforwards a b c L hab hac hbc haL hbL hcL
  obtain ⟨hneF, hneG⟩ := channel_survivors_ne a b c L hab hac hbc hL hL0 haL hbL hcL
  have hF : totalVariation (pushMass (fChannel a b c L) (muMass a b c L))
      (pushMass (fChannel a b c L) (nuMass a b c L)) = 1 / 3 :=
    tv_dipole _ _ _ _ (1 / 3) hneF (by norm_num) hsF
  have hG : totalVariation (pushMass (gChannel a b c L) (muMass a b c L))
      (pushMass (gChannel a b c L) (nuMass a b c L)) = 1 / 3 :=
    tv_dipole _ _ _ _ (1 / 3) hneG (by norm_num) hsG
  let ρ := muLaw a b c L
  let σ := nuLaw a b c L
  have hρ : massVector ρ = muMass a b c L := massVector_lawOfMass _
  have hσ : massVector σ = nuMass a b c L := massVector_lawOfMass _
  have hsource' : totalVariation (massVector ρ) (massVector σ) = 1 := by
    rw [hρ, hσ]
    exact hsource
  have hF' : totalVariation (massVector (ρ.map (fChannel a b c L)))
      (massVector (σ.map (fChannel a b c L))) = 1 / 3 := by
    rw [massVector_map, massVector_map, hρ, hσ]
    exact hF
  have hG' : totalVariation (massVector (ρ.map (gChannel a b c L)))
      (massVector (σ.map (gChannel a b c L))) = 1 / 3 := by
    rw [massVector_map, massVector_map, hρ, hσ]
    exact hG
  refine ⟨L, hL, hS, hL0, source_legal A a b c L hn hsupp, hi,
    ρ, σ, hρ, hσ, hsource', hF', hG', ?_, ?_⟩
  · intro K hK
    have hh := hK ρ σ
    rw [hsource', hF', hG'] at hh
    norm_num at hh
    linarith
  · intro K hK
    have hh := hK ρ σ
    rw [hsource', hF', hG'] at hh
    norm_num at hh
    linarith

end D5.S3.Combinatorics.CircularWords.PairedDeletionSharpness
