/- GID: D5/S3/Combinatorics/Permutation/Verkama62Charge
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/Verkama62Charge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: An integer potential bounds every 351624-avoiding northeast ear run. -/

import D5.S3.Combinatorics.Permutation.Verkama62Count

/-! The potential has three alternatives: unrestricted, terminal, and fresh. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.Verkama62Local

open D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)

/-- Runs start at an induced triangle or 3412 and add singletons of old degree
    at least two or northeast double ears. -/
inductive EarRun {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Fin n) → Prop
  | triangle (a b c : Fin n) (hab : a < b) (hbc : b < c)
      (hba : π b < π a) (hcb : π c < π b) : EarRun π {a, b, c}
  | square (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d)
      (hcdv : π c < π d) (hda : π d < π a) (habv : π a < π b) :
      EarRun π {a, b, c, d}
  | singleton {S : Finset (Fin n)} (run : EarRun π S) (x : Fin n) (hx : x ∉ S)
      (hdegree : 2 ≤ (neighbours π S x).card) : EarRun π (insert x S)
  | double {S : Finset (Fin n)} (run : EarRun π S) (e : Double π S) :
      EarRun π (insert e.u (insert e.v S))

/-- The signed edge-deficit potential; all subtraction takes place in the integers. -/
def potential {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : ℤ :=
  7 * (S.card : ℤ) - 4 * (inversions π S : ℤ)

private def Budget {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : Prop :=
  potential π S ≤ 10 ∨
    (potential π S ≤ 11 ∧ Nonempty (Terminal π S)) ∨
    (potential π S ≤ 12 ∧ Nonempty (Fresh π S))

private theorem triangle_counts {n : ℕ} (π : Equiv.Perm (Fin n))
    (a b c : Fin n) (hab : a < b) (hbc : b < c)
    (hba : π b < π a) (hcb : π c < π b) :
    ({a, b, c} : Finset (Fin n)).card = 3 ∧ inversions π {a, b, c} = 3 := by
  have hac := hab.trans hbc
  have hca := hcb.trans hba
  have hneab := ne_of_lt hab
  have hneac := ne_of_lt hac
  have hnebc := ne_of_lt hbc
  simp [inversions, Finset.filter_insert, Finset.filter_singleton,
    hneab, hneac, hnebc, hab, hbc, hac, hba, hcb, hca,
    not_lt_of_ge hab.le, not_lt_of_ge hbc.le, not_lt_of_ge hac.le]

private def square_fresh {n : ℕ} (π : Equiv.Perm (Fin n))
    (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hcdv : π c < π d) (hda : π d < π a) (habv : π a < π b) :
    Fresh π {a, b, c, d} where
  a := a
  b := b
  c := c
  d := d
  ha := by simp
  hb := by simp
  hc := by simp
  hd := by simp
  hab := hab
  hbc := hbc
  hcd := hcd
  hval₁ := hcdv
  hval₂ := hda
  hval₃ := habv
  rightmost := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> omega
  topmost := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> omega
  right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> omega
  top := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> omega

private theorem square_counts {n : ℕ} (π : Equiv.Perm (Fin n))
    (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hcdv : π c < π d) (hda : π d < π a) (habv : π a < π b) :
    ({a, b, c, d} : Finset (Fin n)).card = 4 ∧ inversions π {a, b, c, d} = 4 := by
  have hac := hab.trans hbc
  have had := hac.trans hcd
  have hbd := hbc.trans hcd
  have hca := hcdv.trans hda
  have hcb := hca.trans habv
  have hdb := hda.trans habv
  have hneab := ne_of_lt hab
  have hneac := ne_of_lt hac
  have hnead := ne_of_lt had
  have hnebc := ne_of_lt hbc
  have hnebd := ne_of_lt hbd
  have hnecd := ne_of_lt hcd
  simp [inversions, Finset.filter_insert, Finset.filter_singleton,
    hneab, hneac, hnead, hnebc, hnebd, hnecd,
    hab, hbc, hcd, hac, had, hbd, hcdv, hda, habv, hca, hcb, hdb,
    not_lt_of_ge hab.le, not_lt_of_ge hbc.le, not_lt_of_ge hcd.le,
    not_lt_of_ge hac.le, not_lt_of_ge had.le, not_lt_of_ge hbd.le,
    not_lt_of_ge habv.le, not_lt_of_ge hcdv.le]

private theorem singleton_potential {n : ℕ} (π : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (x : Fin n) (hx : x ∉ S) :
    potential π (insert x S) =
      potential π S + 7 - 4 * ((neighbours π S x).card : ℤ) := by
  rw [potential, potential, Finset.card_insert_of_notMem hx, inversions_insert π S x hx]
  push_cast
  ring

private theorem double_potential {n : ℕ} {π : Equiv.Perm (Fin n)}
    {S : Finset (Fin n)} (e : Double π S) :
    potential π (insert e.u (insert e.v S)) = potential π S + 2 := by
  have huv : e.u ≠ e.v := ne_of_lt (e.hux.trans e.hxv)
  rw [potential, potential, Finset.card_insert_of_notMem (by simp [huv, e.hu]),
    Finset.card_insert_of_notMem e.hv, e.inversion_increment]
  push_cast
  ring

private theorem run_budget {n : ℕ} {π : Equiv.Perm (Fin n)}
    {S : Finset (Fin n)} (run : EarRun π S) (havoid : ¬ Contains pattern π) :
    Budget π S := by
  induction run with
  | triangle a b c hab hbc hba hcb =>
    obtain ⟨hc, hi⟩ := triangle_counts π a b c hab hbc hba hcb
    left
    simp [potential, hc, hi]
  | square a b c d hab hbc hcd hcdv hda habv =>
    obtain ⟨hc, hi⟩ := square_counts π a b c d hab hbc hcd hcdv hda habv
    right; right
    exact ⟨by simp [potential, hc, hi], ⟨square_fresh π a b c d hab hbc hcd hcdv hda habv⟩⟩
  | @singleton S run x hx hdegree ih =>
    have heq := singleton_potential π S x hx
    rcases ih with h | ⟨h, ht⟩ | ⟨h, hf⟩
    · left; omega
    · left; omega
    · by_cases hd : (neighbours π S x).card = 2
      · right; left
        exact ⟨by omega, hf.elim (fun t => t.singleton_terminal x hx hd)⟩
      · left; omega
  | @double S run e ih =>
    have heq := double_potential e
    rcases ih with h | ⟨h, ⟨t⟩⟩ | ⟨h, ⟨t⟩⟩
    · right; right
      exact ⟨by omega, ⟨e.fresh⟩⟩
    · exact (havoid (t.forces e)).elim
    · exact ((t.no_cheap_double havoid).1.false e).elim

/-- Every avoiding northeast ear run satisfies the exact subtraction-free bound.
    Existence of such a run is a separate graph-theoretic obligation. -/
theorem ear_run_bound {n : ℕ} {π : Equiv.Perm (Fin n)}
    {S : Finset (Fin n)} (run : EarRun π S) (havoid : ¬ Contains pattern π) :
    7 * S.card ≤ 4 * inversions π S + 12 := by
  have h : potential π S ≤ 12 := by
    rcases run_budget run havoid with h | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  unfold potential at h
  omega

end D5.S3.Combinatorics.Permutation.Verkama62Local
