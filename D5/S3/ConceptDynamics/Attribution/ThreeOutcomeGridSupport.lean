/- GID: D5/S3/ConceptDynamics/Attribution/ThreeOutcomeGridSupport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ThreeOutcomeGridSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp finite seed support for pointwise permutation-equivariant calibration of three-outcome grids. -/

import D5.S3.ConceptDynamics.Attribution.CovariantGridSupport
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Finset

namespace D5.S3.ConceptDynamics.Attribution.ThreeOutcomeGridSupport

abbrev Label := Fin 3
abbrev Symmetry := Equiv.Perm Label
abbrev Profile (q : ℕ) := {p : Label → ℕ // ∑ i, p i = 6 * q}

abbrev relabel {q : ℕ} (g : Symmetry) (p : Profile q) : Profile q :=
  ⟨fun i => p.val (g⁻¹ i), (Equiv.sum_comp (g⁻¹ : Symmetry) p.val).trans p.property⟩

private theorem symmetry_card : Fintype.card Symmetry = 6 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  decide

private theorem unique_fixed (g : Symmetry) (nontrivial : g ≠ 1)
    {a b : Label} (ha : g a = a) (hb : g b = b) : a = b := by
  have all : ∀ h : Symmetry, h ≠ 1 → ∀ i j : Label, h i = i → h j = j → i = j := by
    decide
  exact all g nontrivial a b ha hb

private def uniform (q : ℕ) : Profile q :=
  ⟨fun _ => 2*q, by simp; omega⟩

private def missing (q : ℕ) (a : Label) : Profile q :=
  ⟨fun i => if i = a then 0 else 3*q, by
    fin_cases a <;> simp [Fin.sum_univ_succ] <;> omega⟩

private def tied (q : ℕ) (k : Fin (3*q+1)) : Profile q :=
  ⟨![k.val, k.val, 6*q - 2*k.val], by
    have hk := k.isLt
    simp [Fin.sum_univ_succ]
    omega⟩

private def swap01 : Symmetry := Equiv.swap 0 1

private theorem tied_relabel (q : ℕ) (k : Fin (3*q+1)) : relabel swap01 (tied q k) = tied q k := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

private theorem all_stabilizers_trivial {S : Type*} [Fintype S] [MulAction Symmetry S]
    {q : ℕ} (w : S → ℝ) (positive : ∀ s, 0 < w s)
    (f : Profile q → S → Label)
    (calibrated : ∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ))
    (covariant : ∀ g p s, f (relabel g p) (g • s) = g (f p s)) :
    ∀ s : S, MulAction.stabilizer Symmetry s = ⊥ := by
  classical
  intro s
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g fixes
  by_contra different
  have hfix := MulAction.mem_stabilizer_iff.mp fixes
  have stable (p : Profile q) (hp : relabel g p = p) : g (f p s) = f p s := by
    simpa only [hp, hfix] using (covariant g p s).symm
  let a := f (uniform q) s
  have ha : g a = a := stable (uniform q) rfl
  have hmissing : relabel g (missing q a) = missing q a := by
    apply Subtype.ext
    funext i
    change (if g⁻¹ i = a then 0 else 3*q) = if i = a then 0 else 3*q
    have same : g⁻¹ i = a ↔ i = a := g.symm_apply_eq.trans (by rw [ha])
    simp only [same]
  have hread : f (missing q a) s = a := unique_fixed g different (stable (missing q a) hmissing) ha
  have zero : (∑ t, (if f (missing q a) t = a then w t else 0)) = 0 := by
    simpa [missing] using calibrated (missing q a) a
  have bound := Finset.single_le_sum (s := Finset.univ)
    (f := fun t => if f (missing q a) t = a then w t else 0)
    (fun t _ => by split <;> first | exact (positive t).le | exact le_rfl) (Finset.mem_univ s)
  rw [zero, ite_eq_left hread] at bound
  exact (not_lt_of_ge bound) (positive s)

private noncomputable def orbitCoordinates {S : Type*} [MulAction Symmetry S]
    (free : ∀ s : S, MulAction.stabilizer Symmetry s = ⊥) :
    (MulAction.orbitRel.Quotient Symmetry S × Symmetry) ≃ S :=
  Equiv.ofBijective (fun (p : MulAction.orbitRel.Quotient Symmetry S × Symmetry) => p.2 • p.1.out) (by
    constructor
    · rintro ⟨i, g⟩ ⟨j, h⟩ eq
      have hi : i = j := by
        simpa only [MulAction.orbitRel.Quotient.quotient_smul_eq, Quotient.out_eq'] using
          congrArg (fun s : S => (Quotient.mk'' s : MulAction.orbitRel.Quotient Symmetry S)) eq
      subst j
      have : IsCancelSMul Symmetry S := isCancelSMul_iff_stabilizer_eq_bot.mpr free
      exact Prod.ext rfl (IsCancelSMul.right_cancel _ _ _ eq)
    · intro s
      let i : MulAction.orbitRel.Quotient Symmetry S := Quotient.mk'' s
      have h : s ∈ MulAction.orbit Symmetry i.out := Quotient.exact' (Quotient.out_eq' i).symm
      obtain ⟨g, hg⟩ := h
      exact ⟨(i, g), hg⟩)

private theorem count_at_most_three (f : Symmetry → Label)
    (equivariant : ∀ g, f (swap01*g) = swap01 (f g)) :
    (univ.filter fun g => f g = 0).card ≤ 3 := by
  classical
  let E := univ.filter fun g => f g = 0
  let F := univ.filter fun g => f g = 1
  have same : E.card = F.card := by
    have maps : E.map (Equiv.mulLeft swap01).toEmbedding = F := by
      ext g
      simp only [E, F, Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
      change f (swap01⁻¹ * g) = 0 ↔ f g = 1
      rw [show f g = swap01 (f (swap01⁻¹ * g)) by
        simpa only [mul_inv_cancel_left] using equivariant (swap01⁻¹ * g)]
      rw [← show swap01 0 = 1 by decide, Equiv.apply_eq_iff_eq]
    rw [← maps, Finset.card_map]
  have disj : Disjoint E F := Finset.disjoint_left.mpr fun g hE hF => by
    have h0 := (Finset.mem_filter.mp hE).2
    have h1 := (Finset.mem_filter.mp hF).2
    exact (by decide : (0 : Label) ≠ 1) (h0.symm.trans h1)
  have total : (E ∪ F).card ≤ 6 := by
    simpa only [Finset.card_univ, symmetry_card] using
      Finset.card_le_card (Finset.subset_univ (E ∪ F))
  rw [Finset.card_union_of_disjoint disj] at total
  change E.card ≤ 3
  omega

private theorem triple_grid_lower {S : Type*} [Fintype S] [MulAction Symmetry S]
    {q : ℕ} (w : S → ℝ) (positive : ∀ s, 0 < w s)
    (invariant : ∀ (g : Symmetry) s, w (g • s) = w s)
    (f : Profile q → S → Label)
    (calibrated : ∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ))
    (covariant : ∀ g p s, f (relabel g p) (g • s) = g (f p s)) :
    ∃ r, Fintype.card S = 6*r ∧ 3*q+1 ≤ 4^r := by
  classical
  let J := MulAction.orbitRel.Quotient Symmetry S
  let _ : Fintype J := Fintype.ofFinite J
  let e := orbitCoordinates (all_stabilizers_trivial w positive f calibrated covariant)
  have hcard : Fintype.card S = 6 * Fintype.card J := by
    simpa only [Fintype.card_prod, symmetry_card, Nat.mul_comm] using Fintype.card_congr e.symm
  let digit (k : Fin (3*q+1)) (j : J) : Fin 4 :=
    ⟨(univ.filter fun g => f (tied q k) (g • j.out) = 0).card,
      Nat.lt_succ_of_le (count_at_most_three (fun g => f (tied q k) (g • j.out)) (fun g => by
        simpa only [tied_relabel, mul_smul] using covariant swap01 (tied q k) (g • j.out)))⟩
  have weighted (k : Fin (3*q+1)) :
      ∑ j : J, (digit k j).val * w j.out = (k.val : ℝ) := by
    have eq := calibrated (tied q k) 0
    change ∑ s, (if f (tied q k) s = 0 then w s else 0) = (k.val : ℝ) at eq
    rw [← e.sum_comp] at eq
    rw [Fintype.sum_prod_type] at eq
    rw [← eq]
    apply Finset.sum_congr rfl
    intro j _
    change ((univ.filter fun g : Symmetry => f (tied q k) (g • j.out) = 0).card : ℝ) * w j.out =
      ∑ g : Symmetry, (if f (tied q k) (g • j.out) = 0 then w (g • j.out) else 0)
    simp only [invariant, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have inj : Function.Injective digit := by
    intro k l h
    have eq : (k.val : ℝ) = (l.val : ℝ) := by rw [← weighted k, ← weighted l, h]
    exact Fin.ext (by exact_mod_cast eq)
  exact ⟨Fintype.card J, hcard, by simpa using Fintype.card_le_of_injective digit inj⟩


private def assignedCount (f : Symmetry → Label) (i : Label) : ℕ :=
  (univ.filter fun g => f g = i).card

private def tiedReadout (count : Fin 4) (g : Symmetry) : Label :=
  let slot := g⁻¹ (2 : Label)
  if slot.val < count.val then g (slot + 1) else 2

private theorem tiedReadout_equivariant : ∀ (d : Fin 4) (g : Symmetry),
    tiedReadout d (swap01 * g) = swap01 (tiedReadout d g) := by
  decide

private theorem tiedReadout_count : ∀ (d : Fin 4),
    assignedCount (tiedReadout d) 0 = d.val ∧
    assignedCount (tiedReadout d) 1 = d.val ∧
    assignedCount (tiedReadout d) 2 = 6 - 2*d.val := by
  decide

private theorem perm_fixed_two : ∀ g : Symmetry, g 2 = 2 → g = 1 ∨ g = swap01 := by
  decide

private theorem uniformReadout_count : ∀ i : Label, assignedCount (fun g => g 0) i = 2 := by
  decide

private noncomputable def indexSymmetry : Symmetry ≃ Fin 6 :=
  (Fintype.equivFin Symmetry).trans (finCongr symmetry_card)

private noncomputable def distinctReadout (a b : ℕ) (g : Symmetry) : Label :=
  let n := (indexSymmetry g).val
  if n < a then 0 else if n < a + b then 1 else 2

private theorem distinctReadout_count {a b c : ℕ} (total : a+b+c = 6) :
    assignedCount (distinctReadout a b) 0 = a ∧
    assignedCount (distinctReadout a b) 1 = b ∧
    assignedCount (distinctReadout a b) 2 = c := by
  have checked : ∀ x y z : Fin 7, x.val+y.val+z.val = 6 →
      (univ.filter fun k : Fin 6 =>
        (if k.val < x.val then (0 : Label) else if k.val < x.val+y.val then 1 else 2) = 0).card = x.val ∧
      (univ.filter fun k : Fin 6 =>
        (if k.val < x.val then (0 : Label) else if k.val < x.val+y.val then 1 else 2) = 1).card = y.val ∧
      (univ.filter fun k : Fin 6 =>
        (if k.val < x.val then (0 : Label) else if k.val < x.val+y.val then 1 else 2) = 2).card = z.val := by
    decide
  have reindex (i : Label) : assignedCount (distinctReadout a b) i =
      (univ.filter fun k : Fin 6 =>
        (if k.val < a then (0 : Label) else if k.val < a+b then 1 else 2) = i).card := by
    rw [assignedCount, ← Finset.card_map indexSymmetry.toEmbedding]
    congr 1
    ext k
    rw [Finset.mem_map_equiv]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (if (indexSymmetry (indexSymmetry.symm k)).val < a then (0 : Label)
      else if (indexSymmetry (indexSymmetry.symm k)).val < a+b then 1 else 2) = i ↔ _
    rw [Equiv.apply_symm_apply]
  simp only [reindex]
  exact checked ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ total

private theorem weightedCount {n : ℕ} (w : Fin n → ℕ) (f : Fin n × Symmetry → Label) (i : Label) :
    (∑ s : Fin n × Symmetry, if f s = i then w s.1 else 0) =
      ∑ j : Fin n, assignedCount (fun g => f (j,g)) i * w j := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, assignedCount]

private def LocalReadout {q n : ℕ} (w : Fin n → ℕ) (p : Profile q) :=
  {f : Fin n × Symmetry → Label //
   (∀ i, ∑ s : Fin n × Symmetry, (if f s = i then w s.1 else 0) = p.val i) ∧
   (∀ g, relabel g p = p → ∀ j h, f (j,g*h) = g (f (j,h)))}

private theorem relabel_mul {q : ℕ} (g h : Symmetry) (p : Profile q) :
    relabel (g*h) p = relabel g (relabel h p) := by
  apply Subtype.ext
  funext i
  simp only [mul_inv_rev, Equiv.Perm.mul_apply]

private theorem relabel_one {q : ℕ} (p : Profile q) : relabel 1 p = p := by
  apply Subtype.ext
  funext i
  simp

private theorem relabel_val {q : ℕ} (p : Profile q) (g : Symmetry) (i : Label) :
    (relabel g p).val (g i) = p.val i := by
  exact congrArg p.val (g.symm_apply_apply i)


private noncomputable def transportReadout {q n : ℕ} {w : Fin n → ℕ} {p : Profile q}
    (f : LocalReadout w p) (g : Symmetry) : LocalReadout w (relabel g p) := by
  let e := (Equiv.refl (Fin n)).prodCongr (Equiv.mulLeft g⁻¹)
  refine ⟨fun s => g (f.val (e s)), ?_, ?_⟩
  · intro i
    have sum := e.sum_comp (fun s => if f.val s = g⁻¹ i then w s.1 else 0)
    change (∑ s, (if f.val (e s) = g⁻¹ i then w s.1 else 0)) = _ at sum
    have test (j : Label) : g j = i ↔ j = g⁻¹ i := by
      change g j = i ↔ j = g.symm i
      exact ⟨fun h => (g.symm_apply_eq.mpr h.symm).symm,
        fun h => h ▸ g.apply_symm_apply i⟩
    simpa only [test, ← sum] using f.property.1 (g⁻¹ i)
  · intro h stable j k
    let u : Symmetry := g⁻¹*h*g
    have hfix : relabel u p = p := by
      rw [show u = g⁻¹*(h*g) by simp [u, mul_assoc], relabel_mul, relabel_mul, stable,
        ← relabel_mul, inv_mul_cancel, relabel_one]
    change g (f.val (j, g⁻¹*(h*k))) = h (g (f.val (j,g⁻¹*k)))
    rw [show g⁻¹*(h*k) = u*(g⁻¹*k) by dsimp [u]; group,
        f.property.2 u hfix, ← Equiv.Perm.mul_apply, show g*u = h*g by dsimp [u]; group]
    rfl

private theorem local_uniform {q n : ℕ} (w : Fin n → ℕ) (total : ∑ j, w j = q) :
    Nonempty (LocalReadout w (uniform q)) := by
  refine ⟨⟨fun s => s.2 0, ?_, ?_⟩⟩
  · intro i
    rw [weightedCount]
    simp only [uniformReadout_count, ← Finset.mul_sum, total, uniform]
  · intro g _ j h
    rfl

private theorem local_tied {q n : ℕ} (w : Fin n → ℕ) (total : ∑ j, w j = q) (k : Fin (3*q+1))
    (d : Fin n → Fin 4) (digitSum : (∑ j, (d j).val * w j) = k.val) :
    Nonempty (LocalReadout w (tied q k)) := by
  by_cases uniformCase : k.val = 2*q
  · have eq : tied q k = uniform q := by
      apply Subtype.ext
      funext i
      fin_cases i
      · exact uniformCase
      · exact uniformCase
      · change 6*q - 2*k.val = 2*q
        omega
    exact eq ▸ local_uniform w total
  refine ⟨⟨fun s => tiedReadout (d s.1) s.2, ?_, ?_⟩⟩
  · intro i
    rw [weightedCount]
    fin_cases i
    · change (∑ j, assignedCount (tiedReadout (d j)) 0 * w j) = k.val
      simpa only [(tiedReadout_count _).1] using digitSum
    · change (∑ j, assignedCount (tiedReadout (d j)) 1 * w j) = k.val
      simpa only [(tiedReadout_count _).2.1] using digitSum
    · have expand (j : Fin n) :
          assignedCount (tiedReadout (d j)) 2 * w j + 2*((d j).val * w j) = 6*w j := by
            rw [(tiedReadout_count (d j)).2.2, ← Nat.mul_assoc, ← Nat.add_mul]
            congr 1
            have hj := (d j).isLt
            omega
      have summed := Finset.sum_congr (s₁ := (univ : Finset (Fin n))) rfl (fun j _ => expand j)
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, digitSum, total] at summed
      change (∑ j, assignedCount (tiedReadout (d j)) 2 * w j) = 6*q-2*k.val
      omega
  · intro g stable j h
    have fixe : g 2 = 2 := by
      have eql : (tied q k).val (g 2) = (tied q k).val 2 := by
        exact (congrArg (fun p : Profile q => p.val (g 2)) stable).symm.trans
          (relabel_val (tied q k) g 2)
      generalize g 2 = i at eql ⊢
      have hk := k.isLt
      fin_cases i <;> change _ = 6*q - 2*k.val at eql <;> first | rfl | change k.val = _ at eql; omega
    rcases perm_fixed_two g fixe with rfl | rfl
    · simp
    · exact tiedReadout_equivariant (d j) h

private theorem local_distinct {q n : ℕ} (w : Fin n → ℕ) (p : Profile q)
    (injective : Function.Injective p.val)
    (a b c : Fin n → ℕ) (counts : ∀ j, a j+b j+c j = 6)
    (A : ∑ j, a j*w j = p.val 0) (B : ∑ j, b j*w j = p.val 1)
    (C : ∑ j, c j*w j = p.val 2) : Nonempty (LocalReadout w p) := by
  refine ⟨⟨fun s => distinctReadout (a s.1) (b s.1) s.2, ?_, ?_⟩⟩
  · intro i
    rw [weightedCount]
    fin_cases i
    · change (∑ j, assignedCount (distinctReadout (a j) (b j)) 0 * w j) = p.val 0
      have eq : (∑ j, assignedCount (distinctReadout (a j) (b j)) 0 * w j) = _ :=
        Finset.sum_congr rfl (fun j _ => congrArg (· * w j) (distinctReadout_count (counts j)).1)
      exact eq.trans A
    · change (∑ j, assignedCount (distinctReadout (a j) (b j)) 1 * w j) = p.val 1
      have eq : (∑ j, assignedCount (distinctReadout (a j) (b j)) 1 * w j) = _ :=
        Finset.sum_congr rfl (fun j _ => congrArg (· * w j) (distinctReadout_count (counts j)).2.1)
      exact eq.trans B
    · change (∑ j, assignedCount (distinctReadout (a j) (b j)) 2 * w j) = p.val 2
      have eq : (∑ j, assignedCount (distinctReadout (a j) (b j)) 2 * w j) = _ :=
        Finset.sum_congr rfl (fun j _ => congrArg (· * w j) (distinctReadout_count (counts j)).2.2)
      exact eq.trans C
  · intro g stable j h
    have id : g = 1 := by
      apply Equiv.ext
      intro i
      exact injective ((congrArg (fun p : Profile q => p.val (g i)) stable).symm.trans
        (relabel_val p g i))
    simp [id]


private theorem local_of_cover {q n : ℕ} (w : Fin n → ℕ) (total : ∑ j, w j = q)
    (three : ∀ x y z : ℕ, x+y+z = 6*q →
      ∃ a b c : Fin n → ℕ, (∀ j, a j+b j+c j = 6) ∧
        (∑ j, a j*w j) = x ∧ (∑ j, b j*w j) = y ∧ (∑ j, c j*w j) = z)
    (pairs : ∀ k ≤ 3*q, ∃ d : Fin n → Fin 4, (∑ j, (d j).val*w j) = k)
    (p : Profile q) : Nonempty (LocalReadout w p) := by
  have with_tie (g : Symmetry) (tie : p.val (g 0) = p.val (g 1)) :
      Nonempty (LocalReadout w p) := by
    let x := relabel g⁻¹ p
    have same : x.val 0 = x.val 1 := by
      change p.val ((g⁻¹)⁻¹ 0) = p.val ((g⁻¹)⁻¹ 1)
      simpa only [inv_inv] using tie
    have sum : x.val 0 + x.val 1 + x.val 2 = 6*q := by
      simpa [Fin.sum_univ_succ, Nat.add_assoc] using x.property
    let k : Fin (3*q+1) := ⟨x.val 0, by omega⟩
    have eq : tied q k = x := by
      apply Subtype.ext
      funext i
      fin_cases i
      · rfl
      · exact same
      · change 6*q-2*x.val 0 = x.val 2
        omega
    obtain ⟨d, digits⟩ := pairs k.val (by have := k.isLt; omega)
    obtain ⟨f⟩ := local_tied w total k d digits
    have recover : relabel g (tied q k) = p := by
      rw [eq]
      change relabel g (relabel g⁻¹ p) = p
      rw [← relabel_mul, mul_inv_cancel, relabel_one]
    exact ⟨recover ▸ transportReadout f g⟩
  by_cases h01 : p.val 0 = p.val 1
  · exact with_tie 1 h01
  by_cases h02 : p.val 0 = p.val 2
  · exact with_tie (Equiv.swap 1 2) h02
  by_cases h12 : p.val 1 = p.val 2
  · exact with_tie (Equiv.swap 0 2) h12.symm
  have inj : Function.Injective p.val := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact False.elim (h01 h)
      | exact False.elim (h01 h.symm)
      | exact False.elim (h02 h)
      | exact False.elim (h02 h.symm)
      | exact False.elim (h12 h)
      | exact False.elim (h12 h.symm)
  have sum : p.val 0 + p.val 1 + p.val 2 = 6*q := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using p.property
  obtain ⟨a,b,c,counts,A,B,C⟩ := three _ _ _ sum
  exact local_distinct w p inj a b c counts A B C

private instance profileMulAction {q : ℕ} : MulAction Symmetry (Profile q) where
  smul := relabel
  one_smul := relabel_one
  mul_smul := relabel_mul

private theorem global_readout {q n : ℕ} (w : Fin n → ℕ)
    (all : ∀ p : Profile q, Nonempty (LocalReadout w p)) :
    ∃ f : Profile q → Fin n × Symmetry → Label,
      (∀ p i, ∑ s : Fin n × Symmetry, (if f p s = i then w s.1 else 0) = p.val i) ∧
      (∀ g p j h, f (relabel g p) (j,g*h) = g (f p (j,h))) := by
  classical
  let orbit (p : Profile q) : MulAction.orbitRel.Quotient Symmetry (Profile q) := Quotient.mk'' p
  let rep (p : Profile q) := (orbit p).out
  have existsSymmetry (p : Profile q) : ∃ g : Symmetry, relabel g (rep p) = p := by
    exact Quotient.exact' (Quotient.out_eq' (orbit p)).symm
  let g (p : Profile q) := (existsSymmetry p).choose
  have go (p : Profile q) : relabel (g p) (rep p) = p := (existsSymmetry p).choose_spec
  let localF (p : Profile q) : LocalReadout w p := Classical.choice (all p)
  let f (p : Profile q) (s : Fin n × Symmetry) :=
    (g p) ((localF (rep p)).val (s.1, (g p)⁻¹*s.2))
  refine ⟨f, ?_, ?_⟩
  · intro p i
    have calibration := (transportReadout (localF (rep p)) (g p)).property.1 i
    change (∑ s, (if f p s = i then w s.1 else 0)) = (relabel (g p) (rep p)).val i at calibration
    exact calibration.trans (congrArg (fun p : Profile q => p.val i) (go p))
  · intro h p j k
    let p' := relabel h p
    have same : rep p' = rep p :=
      congrArg Quotient.out (MulAction.orbitRel.Quotient.quotient_smul_eq (g := h) (a := p))
    let u := (g p')⁻¹*h*g p
    have stable : relabel u (rep p) = rep p := by
      rw [show u = (g p')⁻¹*(h*g p) by dsimp [u]; group, relabel_mul, relabel_mul,
        go p]
      change relabel (g p')⁻¹ p' = rep p
      calc
        relabel (g p')⁻¹ p' = relabel (g p')⁻¹ (relabel (g p') (rep p')) :=
          congrArg (relabel (g p')⁻¹) (go p').symm
        _ = rep p' := by rw [← relabel_mul, inv_mul_cancel, relabel_one]
        _ = rep p := same
    change (g p') ((localF (rep p')).val (j,(g p')⁻¹*(h*k))) =
      h ((g p) ((localF (rep p)).val (j,(g p)⁻¹*k)))
    rw [same, show (g p')⁻¹*(h*k) = u*((g p)⁻¹*k) by dsimp [u]; group,
      (localF (rep p)).property.2 u stable, ← Equiv.Perm.mul_apply,
      show g p'*u = h*g p by dsimp [u]; group]
    rfl


open CovariantGridSupport (capacity split_digit)

private theorem three_bin_step {old d x y z : ℕ} (positive : 0 < d)
    (capacity : 2 * (d - 1) ≤ old) (total : x + y + z = old + 6 * d) :
    ∃ a b c : ℕ, a + b + c = 6 ∧ a*d ≤ x ∧ b*d ≤ y ∧ c*d ≤ z ∧
      (x-a*d) + (y-b*d) + (z-c*d) = old := by
  let X := x / d
  let Y := y / d
  let Z := z / d
  have partition : x+y+z = (X+Y+Z)*d + (x%d+y%d+z%d) := by
    calc
      x+y+z = (x%d+d*X)+(y%d+d*Y)+(z%d+d*Z) := by
        rw [Nat.mod_add_div, Nat.mod_add_div, Nat.mod_add_div]
      _ = _ := by ring
  have enough : 6 ≤ X+Y+Z := by
    by_contra short
    have bound : (X+Y+Z)*d ≤ 5*d := Nat.mul_le_mul_right _ (by omega)
    have rx := Nat.mod_lt x positive
    have ry := Nat.mod_lt y positive
    have rz := Nat.mod_lt z positive
    omega
  let a := min X 6
  let b := min Y (6-a)
  let c := 6-a-b
  have hA : a ≤ X := min_le_left _ _
  have hB : b ≤ Y := min_le_left _ _
  have cum : a+b+c = 6 := by dsimp [a,b,c]; omega
  have hC : c ≤ Z := by
    by_cases hX : X ≤ 6
    · by_cases hY : Y ≤ 6 - X
      · simp only [c,b,a,min_eq_left hX,min_eq_left hY]
        omega
      · simp [c,b,a,min_eq_left hX,min_eq_right (le_of_not_ge hY)]
    · simp [c,b,a,min_eq_right (le_of_not_ge hX)]
  have hx : a*d ≤ x := (Nat.mul_le_mul_right _ hA).trans (Nat.div_mul_le_self _ _)
  have hy : b*d ≤ y := (Nat.mul_le_mul_right _ hB).trans (Nat.div_mul_le_self _ _)
  have hz : c*d ≤ z := (Nat.mul_le_mul_right _ hC).trans (Nat.div_mul_le_self _ _)
  have removed : a*d+b*d+c*d = 6*d := by rw [← Nat.add_mul, ← Nat.add_mul, cum]
  exact ⟨a,b,c,cum,hx,hy,hz,by omega⟩

private def TripleCoverage {n : ℕ} (w : Fin n → ℕ) (q : ℕ) :=
  ∀ x y z : ℕ, x + y + z = 6*q →
    ∃ a b c : Fin n → ℕ, (∀ i, a i + b i + c i = 6) ∧
      (∑ i, a i * w i) = x ∧ (∑ i, b i * w i) = y ∧ (∑ i, c i * w i) = z

private def PairCoverage {n : ℕ} (w : Fin n → ℕ) (q : ℕ) :=
  ∀ k ≤ 3*q, ∃ a : Fin n → Fin 4, (∑ i, (a i).val * w i) = k

private theorem cover_three {n : ℕ} {q : ℕ} (hq : q ≤ capacity 3 n) :
    ∃ w : Fin n → ℕ, (∑ i, w i) = q ∧ TripleCoverage w q ∧ PairCoverage w q := by
  induction n generalizing q with
  | zero =>
    have hq0 : q = 0 := Nat.eq_zero_of_le_zero (by simpa [capacity] using hq)
    subst q
    refine ⟨fun i => i.elim0, by simp, ?_, ?_⟩
    · intro x y z h
      have hx : x = 0 := by omega
      have hy : y = 0 := by omega
      have hz : z = 0 := by omega
      exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        by simp [hx], by simp [hy], by simp [hz]⟩
    · intro k hk
      have hzero : k = 0 := by omega
      exact ⟨fun i => i.elim0, by simp [hzero]⟩
  | succ n ih =>
    let old := min q (capacity 3 n)
    let d := q - old
    have old_le : old ≤ capacity 3 n := min_le_right _ _
    have split : old+d=q := Nat.add_sub_of_le (min_le_left _ _)
    have hd : d ≤ 3*old+1 := by
      by_cases h : q ≤ capacity 3 n
      · simp [d, old, min_eq_left h]
      · change q - min q (capacity 3 n) ≤ 3*min q (capacity 3 n)+1
        rw [min_eq_right (le_of_not_ge h)]
        have hq' : q ≤ 4*capacity 3 n+1 := by
          simpa only [capacity, geom_sum_succ] using hq
        omega
    obtain ⟨w, hw, three, pairs⟩ := ih old_le
    refine ⟨Fin.snoc w d, ?_, ?_, ?_⟩
    · simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hw] using split
    · intro x y z total
      have total' : x+y+z=6*old+6*d := by omega
      have step :
          ∃ a b c : ℕ, a+b+c=6 ∧ a*d≤x ∧ b*d≤y ∧ c*d≤z ∧
            (x-a*d)+(y-b*d)+(z-c*d)=6*old := by
        by_cases zero : d=0
        · exact ⟨6,0,0,by norm_num,by simp [zero],by simp,by simp,by simpa [zero] using total'⟩
        · exact three_bin_step (Nat.pos_of_ne_zero zero) (by omega) total'
      obtain ⟨a,b,c,counts,hx,hy,hz,hleft⟩ := step
      obtain ⟨as,bs,cs,hold,hA,hB,hC⟩ := three (x-a*d) (y-b*d) (z-c*d) hleft
      refine ⟨Fin.snoc as a, Fin.snoc bs b, Fin.snoc cs c, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using counts
        · simpa only [Fin.snoc_castSucc] using hold j
      · simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hA] using
          Nat.sub_add_cancel hx
      · simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hB] using
          Nat.sub_add_cancel hy
      · simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hC] using
          Nat.sub_add_cancel hz
    · intro k hk
      obtain ⟨x,hx,r,hr,eq⟩ := split_digit (k := k) hd (by simpa only [split] using hk)
      obtain ⟨xs, hxs⟩ := pairs r hr
      exact ⟨Fin.snoc xs ⟨x, Nat.lt_succ_of_le hx⟩,
        by simpa only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, hxs] using eq⟩

private theorem triple_and_pair_weights {q n : ℕ} (budget : 3*q+1 ≤ 4^n) :
    ∃ w : Fin n → ℕ, (∑ i, w i) = q ∧ TripleCoverage w q ∧ PairCoverage w q := by
  have h : 3*q+1 ≤ (3+1)^n := budget
  rw [← geom_sum_mul_add (R := ℕ) 3 n, ← capacity, Nat.mul_comm (capacity 3 n) 3] at h
  exact cover_three (by omega)


@[instance_reducible] private def regularSeedAction (S : Type*) : MulAction Symmetry (S × Symmetry) where
  smul g s := (s.1, g*s.2)
  one_smul s := Prod.ext rfl (one_mul s.2)
  mul_smul g h s := Prod.ext rfl (mul_assoc g h s.2)

private lemma sum_positive_support {A : Type*} [Fintype A] (w f : A → ℕ)
    (zero : ∀ a, w a = 0 → f a = 0) :
    (∑ s : {a : A // 0 < w a}, f s.val) = ∑ a : A, f a := by
  have vanish : (∑ s : {a : A // ¬ 0 < w a}, f s.val) = 0 :=
    Finset.sum_eq_zero fun a _ => zero a.val (Nat.eq_zero_of_not_pos a.property)
  simpa only [vanish, add_zero] using Fintype.sum_subtype_add_sum_subtype (fun a => 0 < w a) f

def CalibratingLaw {q : ℕ} (S : Type*) [Fintype S] [MulAction Symmetry S]
    (w : S → ℝ) (f : Profile q → S → Label) : Prop :=
  (∀ s, 0 < w s) ∧ (∑ s, w s = 1) ∧
  (∀ (g : Symmetry) s, w (g • s) = w s) ∧
  (∀ p i, ∑ s, (if f p s = i then w s else 0) = (p.val i : ℝ) / (6*q : ℕ)) ∧
  (∀ g p s, f (relabel g p) (g • s) = g (f p s))

theorem triple_grid_support_budget_iff {q : ℕ} (positive : 0 < q) (n : ℕ) :
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction Symmetry S) (w : S → ℝ)
      (f : Profile q → S → Label), CalibratingLaw S w f ∧ Fintype.card S ≤ 6*n) ↔
        3*q+1 ≤ 4^n := by
  classical
  let m : ℝ := (6*q : ℕ)
  have mpos : 0 < m := by
    change (0 : ℝ) < ((6*q : ℕ) : ℝ)
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 6) positive)
  constructor
  · rintro ⟨S, _, _, w, f, ⟨wp, _, wi, mass, equivariant⟩, support⟩
    let v (s : S) := m*w s
    have massV (p : Profile q) (i : Label) :
        (∑ s, (if f p s = i then v s else 0)) = (p.val i : ℝ) := by
      have hm (s : S) : (if f p s = i then v s else 0) = m*(if f p s = i then w s else 0) := by
        by_cases h : f p s = i <;> simp [h, v]
      simp only [hm, ← Finset.mul_sum, mass]
      change m*((p.val i : ℝ) / m) = (p.val i : ℝ)
      rw [mul_comm m, div_mul_cancel₀ _ mpos.ne']
    obtain ⟨r, card, bound⟩ := triple_grid_lower v (fun s => mul_pos mpos (wp s))
      (fun g s => congrArg (m*·) (wi g s)) f massV equivariant
    have le : r ≤ n := by omega
    exact bound.trans (Nat.pow_le_pow_right (by decide) le)
  · intro budget
    obtain ⟨w, total, three, pairs⟩ := triple_and_pair_weights budget
    obtain ⟨f, mass, equivariant⟩ := global_readout w (local_of_cover w total three pairs)
    let _ : MulAction Symmetry (Fin n × Symmetry) := regularSeedAction (Fin n)
    let S := {s : Fin n × Symmetry // 0 < w s.1}
    let _ : MulAction Symmetry S :=
      { smul := fun g s => ⟨g • s.val, s.property⟩
        one_smul := fun s => Subtype.ext (one_smul _ _)
        mul_smul := fun g h s => Subtype.ext (mul_smul g h s.val) }
    let v (s : S) : ℝ := (w s.val.1 : ℝ) / m
    let F (p : Profile q) (s : S) := f p s.val
    have supportedMass (p : Profile q) (i : Label) :
        (∑ s : S, (if F p s = i then w s.val.1 else 0)) = p.val i :=
      (sum_positive_support (fun (s : Fin n × Symmetry) => w s.1)
        (fun s => if f p s = i then w s.1 else 0) (fun s zero => by simp [zero])).trans (mass p i)
    have supportedTotal : (∑ s : S, w s.val.1) = 6*q := by
      rw [sum_positive_support (fun (s : Fin n × Symmetry) => w s.1) _ (fun _ zero => zero)]
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, symmetry_card,
        nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum, total]
    refine ⟨S, inferInstance, inferInstance, v, F, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro s
      exact div_pos (by exact_mod_cast s.property) mpos
    · simp only [v, ← Finset.sum_div, ← Nat.cast_sum, supportedTotal]
      exact div_self mpos.ne'
    · intro g s
      rfl
    · intro p i
      change (∑ s : S, (if F p s = i then (w s.val.1 : ℝ) / m else 0)) = (p.val i : ℝ) / m
      have castMass := congrArg (fun x : ℕ => (x : ℝ)) (supportedMass p i)
      push_cast at castMass
      calc
        _ = ∑ s : S, (if F p s = i then (w s.val.1 : ℝ) else 0) / m := by
          apply Finset.sum_congr rfl
          intro s _
          split <;> simp
        _ = _ := by rw [← Finset.sum_div, castMass]
    · intro g p s
      exact equivariant g p s.val.1 s.val.2
    · calc
        Fintype.card S ≤ Fintype.card (Fin n × Symmetry) := Fintype.card_subtype_le _
        _ = 6*n := by simp [symmetry_card, Nat.mul_comm]

end D5.S3.ConceptDynamics.Attribution.ThreeOutcomeGridSupport
