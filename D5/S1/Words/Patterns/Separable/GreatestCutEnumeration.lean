/- GID: D5/S1/Words/Patterns/Separable/GreatestCutEnumeration
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/GreatestCutEnumeration
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Greatest actual cuts give weighted finite separable-permutation recurrences. -/

import D5.S1.Words.Patterns.Separable.CutFactorization
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
The greatest-cut construction of Fu--Lin--Zeng, arXiv:1507.05184v2,
Theorem 2.3 and the signed recurrences in the proof of Corollary 2.4.
These are classical enumeration ingredients, not a real-rootedness result.
-/

namespace D5.S1.Words.Patterns.Separable.GreatestCutEnumeration

open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.ProperCut (avoidance_proper_cut)
open Polynomial
open scoped BigOperators

/-- A nonempty proper cut of the indicated orientation. -/
def HasProperCut {n : ℕ} (s : Bool) (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ m, 0 < m ∧ m < n ∧ Cut s π m

/-- Both lengths in this split are strictly positive. -/
abbrev PositiveSplit (n : ℕ) := {m : Fin n // 0 < m.val}

/-- Actual avoiders admitting a proper cut; singletons have neither sign. -/
abbrev SignedAvoider (s : Bool) (n : ℕ) := {π : Avoider n // HasProperCut s π.val}

/-- The right factor is a singleton or has the opposite orientation. -/
abbrev RightFactor (s : Bool) (k : ℕ) :=
  {β : Avoider k // k = 1 ∨ HasProperCut (!s) β.val}

/-- Actual factors indexed by a positive position split. -/
abbrev Factors (s : Bool) (n : ℕ) :=
  Σ m : PositiveSplit n, Avoider m.val.val × RightFactor s (n - m.val.val)

/-- The ordinary descent polynomial, with the empty-length convention excluded. -/
noncomputable def S (n : ℕ) : ℕ[X] := by
  classical
  exact if n = 0 then 0 else ∑ π : Avoider n, X ^ descents π.val

/-- Properly decomposable signed classes, without singleton padding. -/
noncomputable def P (s : Bool) (n : ℕ) : ℕ[X] := by
  classical
  exact ∑ π : SignedAvoider s n, X ^ descents π.val.val

open Classical in
/-- The actual weighted greatest-cut equivalence and its finite polynomial recurrences. -/
theorem result : (∀ (s : Bool) (n : ℕ),
    ∃ e : Factors s n ≃ SignedAvoider s n, ∀ x,
      (e x).val.val = cast
        (congrArg (fun l => Equiv.Perm (Fin l)) (Nat.add_sub_of_le x.1.val.isLt.le))
        (blockSum s x.2.1.val x.2.2.val.val) ∧
      Cut s (e x).val.val x.1.val.val ∧
      (∀ r, 0 < r → r < n → Cut s (e x).val.val r → r ≤ x.1.val.val) ∧
      descents (e x).val.val = descents x.2.1.val + descents x.2.2.val.val +
        (if s then 1 else 0)) ∧
    S 0 = 0 ∧ S 1 = 1 ∧
    (∀ s, P s 0 = 0 ∧ P s 1 = 0) ∧
    (∀ n, S n = (if n = 1 then 1 else 0) + P false n + P true n) ∧
    (∀ s n, P s n = X ^ (if s then 1 else 0) *
      ∑ m : PositiveSplit n, S m.val.val *
        ((if n - m.val.val = 1 then 1 else 0) + P (!s) (n - m.val.val))) ∧
    (∀ n r, (S n).coeff r = (if n = 1 ∧ r = 0 then 1 else 0) +
      (P false n).coeff r + (P true n).coeff r) ∧
    (∀ n r, (P false n).coeff r =
      ∑ m : PositiveSplit n, ∑ ab ∈ Finset.antidiagonal r,
        (S m.val.val).coeff ab.1 *
          ((if n - m.val.val = 1 ∧ ab.2 = 0 then 1 else 0) +
            (P true (n - m.val.val)).coeff ab.2)) ∧
    (∀ n, (P true n).coeff 0 = 0) ∧
    (∀ n r, (P true n).coeff (r + 1) =
      ∑ m : PositiveSplit n, ∑ ab ∈ Finset.antidiagonal r,
        (S m.val.val).coeff ab.1 *
          ((if n - m.val.val = 1 ∧ ab.2 = 0 then 1 else 0) +
            (P false (n - m.val.val)).coeff ab.2)) := by
  classical
  have incompatible {n : ℕ} (s : Bool) (π : Equiv.Perm (Fin n)) :
      HasProperCut s π → ¬HasProperCut (!s) π := by
    rintro ⟨a, ha, han, hca⟩ ⟨b, hb, hbn, hcb⟩
    let first : Fin n := ⟨0, by omega⟩
    let last : Fin n := ⟨n - 1, by omega⟩
    have h₁ := hca first last (by dsimp [first]; omega) (by dsimp [last]; omega)
    have h₂ := hcb first last (by dsimp [first]; omega) (by dsimp [last]; omega)
    cases s <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at h₁ h₂ <;> exact (lt_asymm h₁ h₂)
  have extension {m k : ℕ} (s : Bool) (α : Equiv.Perm (Fin m))
      (β : Equiv.Perm (Fin k)) (r : ℕ) :
      Cut s (blockSum s α β) (m + r) ↔ Cut s β r := by
    have leftval (i : Fin m) :
        (blockSum s α β (Fin.castAdd k i)).val =
          (if s then k else 0) + (α i).val := by
      cases s <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm, Nat.add_comm]
    have rightval (i : Fin k) :
        (blockSum s α β (Fin.natAdd m i)).val =
          (if s then 0 else m) + (β i).val := by
      cases s <;> simp [blockSum, Equiv.sumCongr, Equiv.sumComm]
    constructor
    · intro h i j hi hj
      have hh := h (Fin.natAdd m i) (Fin.natAdd m j) (by simp; omega) (by simp; omega)
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Fin.lt_def,
        rightval, Nat.add_lt_add_iff_left] at hh ⊢ <;> exact hh
    · intro h i j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · intro _ hj
        simp only [Fin.val_castAdd] at hj
        omega
      · intro _ _
        cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Fin.lt_def,
          leftval, rightval] <;> simp <;> omega
      · intro _ hj
        simp only [Fin.val_castAdd] at hj
        omega
      · intro hi hj
        simp only [Fin.val_natAdd] at hi hj
        have hh := h i j (by omega) (by omega)
        cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, Fin.lt_def,
          rightval, Nat.add_lt_add_iff_left] at hh ⊢ <;> exact hh
  have eligible {k : ℕ} (hk : 0 < k) (s : Bool) (β : Avoider k) :
      (k = 1 ∨ HasProperCut (!s) β.val) ↔ ¬HasProperCut s β.val := by
    constructor
    · rintro (he | hc) hs
      · obtain ⟨r, hr, hrk, _⟩ := hs
        omega
      · exact incompatible s β.val hs hc
    · intro hs
      by_cases he : k = 1
      · exact Or.inl he
      · right
        obtain ⟨r, hr, hrk, hc⟩ := avoidance_proper_cut (by omega) β.val
          β.property.1 β.property.2
        cases s
        · rcases hc with hc | hc
          · exact (hs ⟨r, hr, hrk, hc⟩).elim
          · exact ⟨r, hr, hrk, hc⟩
        · rcases hc with hc | hc
          · exact ⟨r, hr, hrk, hc⟩
          · exact (hs ⟨r, hr, hrk, hc⟩).elim
  have transport {a b : ℕ} (h : a = b) (π : Avoider a) :
      (cast (congrArg Avoider h) π).val =
        cast (congrArg (fun l => Equiv.Perm (Fin l)) h) π.val ∧
      (∀ s r, Cut s (cast (congrArg Avoider h) π).val r ↔ Cut s π.val r) ∧
      descents (cast (congrArg Avoider h) π).val = descents π.val := by
    subst b
    exact ⟨rfl, fun _ _ => Iff.rfl, rfl⟩
  have hequiv : ∀ (s : Bool) (n : ℕ),
      ∃ e : Factors s n ≃ SignedAvoider s n, ∀ x,
        (e x).val.val = cast
          (congrArg (fun l => Equiv.Perm (Fin l)) (Nat.add_sub_of_le x.1.val.isLt.le))
          (blockSum s x.2.1.val x.2.2.val.val) ∧
        Cut s (e x).val.val x.1.val.val ∧
        (∀ r, 0 < r → r < n → Cut s (e x).val.val r → r ≤ x.1.val.val) ∧
        descents (e x).val.val = descents x.2.1.val + descents x.2.2.val.val +
          (if s then 1 else 0) := by
    intro s n
    let assemble : Factors s n → Avoider n := fun x =>
      cast (congrArg Avoider (Nat.add_sub_of_le x.1.val.isLt.le))
        ⟨blockSum s x.2.1.val x.2.2.val.val,
          (avoids_block_sum_iff s _ _).mpr ⟨x.2.1.property, x.2.2.val.property⟩⟩
    have certificates (x : Factors s n) :
        (assemble x).val = cast
          (congrArg (fun l => Equiv.Perm (Fin l)) (Nat.add_sub_of_le x.1.val.isLt.le))
          (blockSum s x.2.1.val x.2.2.val.val) ∧
        Cut s (assemble x).val x.1.val.val ∧
        (∀ r, 0 < r → r < n → Cut s (assemble x).val r → r ≤ x.1.val.val) ∧
        descents (assemble x).val = descents x.2.1.val + descents x.2.2.val.val +
          (if s then 1 else 0) := by
      let m := x.1.val.val
      have hm : 0 < m := x.1.property
      have hmn : m < n := x.1.val.isLt
      have hk : 0 < n - m := by omega
      let ρ : Avoider (m + (n - m)) := ⟨blockSum s x.2.1.val x.2.2.val.val,
        (avoids_block_sum_iff s _ _).mpr ⟨x.2.1.property, x.2.2.val.property⟩⟩
      have ht := transport (Nat.add_sub_of_le hmn.le) ρ
      refine ⟨ht.1, (ht.2.1 s m).mpr ?_, ?_, ht.2.2.trans ?_⟩
      · simpa [ρ] using (extension s x.2.1.val x.2.2.val.val 0).mpr
          (by intro i j hi; omega)
      · intro r hr hrn hc
        by_contra hle
        apply (eligible hk s x.2.2.val).mp x.2.2.property
        refine ⟨r - m, by omega, by omega, ?_⟩
        apply (extension s x.2.1.val x.2.2.val.val (r - m)).mp
        change Cut s ρ.val (m + (r - m))
        rw [Nat.add_sub_of_le (by omega : m ≤ r)]
        exact (ht.2.1 s r).mp hc
      · exact descents_block_sum hm hk s _ _
    let forward : Factors s n → SignedAvoider s n := fun x =>
      ⟨assemble x, x.1.val.val, x.1.property, x.1.val.isLt, (certificates x).2.1⟩
    have surjective : Function.Surjective forward := by
      intro π
      let cuts : Finset (Fin n) := Finset.univ.filter
        (fun m => 0 < m.val ∧ Cut s π.val.val m.val)
      have hne : cuts.Nonempty := by
        obtain ⟨m, hm, hmn, hc⟩ := π.property
        exact ⟨⟨m, hmn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, hc⟩⟩
      let m := cuts.max' hne
      have hm := (Finset.mem_filter.mp (cuts.max'_mem hne)).2
      have hmax (r : ℕ) (hr : 0 < r) (hrn : r < n) (hc : Cut s π.val.val r) : r ≤ m.val :=
        cuts.le_max' ⟨r, hrn⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr, hc⟩)
      have hmn := m.isLt
      have hk : 0 < n - m.val := by omega
      let j : PositiveSplit n := ⟨m, hm.1⟩
      have factor : ∃ q : Avoider m.val × RightFactor s (n - m.val),
          assemble ⟨j, q⟩ = π.val := by
        let hlen := Nat.add_sub_of_le hmn.le
        let π' : Avoider (m.val + (n - m.val)) := cast (congrArg Avoider hlen.symm) π.val
        have ht := transport hlen.symm π.val
        obtain ⟨q, hq, _⟩ := (fixed_cut_factorization hm.1 hk s π').mp
          ((ht.2.1 s m.val).mpr hm.2)
        have hright : n - m.val = 1 ∨ HasProperCut (!s) q.2.val := by
          apply (eligible hk s q.2).mpr
          rintro ⟨r, hr, hrk, hc⟩
          have hh := (extension s q.1.val q.2.val r).mpr hc
          rw [hq] at hh
          have := hmax (m.val + r) (by omega) (by omega) ((ht.2.1 s _).mp hh)
          omega
        refine ⟨(q.1, ⟨q.2, hright⟩), ?_⟩
        have heq : (⟨blockSum s q.1.val q.2.val,
            (avoids_block_sum_iff s _ _).mpr ⟨q.1.property, q.2.property⟩⟩ :
            Avoider (m.val + (n - m.val))) = π' := Subtype.ext hq
        change cast (congrArg Avoider hlen) _ = π.val
        rw [heq]
        simp [π']
      obtain ⟨q, hq⟩ := factor
      exact ⟨⟨j, q⟩, Subtype.ext hq⟩
    have injective : Function.Injective forward := by
      intro x y h
      have hv : (assemble x).val = (assemble y).val := congrArg (fun p => p.val.val) h
      have hxy := (certificates y).2.2.1 x.1.val.val x.1.property x.1.val.isLt
        (hv ▸ (certificates x).2.1)
      have hyx := (certificates x).2.2.1 y.1.val.val y.1.property y.1.val.isLt
        (hv.symm ▸ (certificates y).2.1)
      have hj : x.1 = y.1 := Subtype.ext (Fin.ext (by omega))
      rcases x with ⟨j, α, β⟩
      rcases y with ⟨l, γ, δ⟩
      dsimp at hj
      subst l
      congr 1
      have heq : blockSum s α.val β.val.val = blockSum s γ.val δ.val.val := by
        have hx := (certificates ⟨j, α, β⟩).1
        have hy := (certificates ⟨j, γ, δ⟩).1
        rw [hx, hy] at hv
        have hc := congrArg (cast (congrArg (fun l => Equiv.Perm (Fin l))
          (Nat.add_sub_of_le j.val.isLt.le).symm)) hv
        simpa using hc
      let π : Avoider (j.val.val + (n - j.val.val)) :=
        ⟨blockSum s α.val β.val.val, (avoids_block_sum_iff s _ _).mpr
          ⟨α.property, β.val.property⟩⟩
      have hc : Cut s π.val j.val.val := by
        simpa [π] using (extension s α.val β.val.val 0).mpr
          (by intro i j hi; omega)
      obtain ⟨q, _, unique⟩ := (fixed_cut_factorization j.property (by omega) s π).mp hc
      have hab : (α, β.val) = (γ, δ.val) :=
        (unique (α, β.val) rfl).trans (unique (γ, δ.val) heq.symm).symm
      have ha : α = γ := congrArg Prod.fst hab
      have hb : β = δ := Subtype.ext (congrArg Prod.snd hab)
      exact Prod.ext ha hb
    exact ⟨Equiv.ofBijective forward ⟨injective, surjective⟩, certificates⟩
  have small (s : Bool) (n : ℕ) (hn : n ≤ 1) : P s n = 0 := by
    apply Finset.sum_eq_zero
    intro π _
    obtain ⟨m, hm, hmn, _⟩ := π.property
    omega
  have singleton : (∑ π : Avoider 1, (X : ℕ[X]) ^ descents π.val) = 1 := by
    let one : Avoider 1 := ⟨Equiv.refl _, by
      constructor <;> rintro ⟨f, _⟩
      all_goals
        have h := f.strictMono (show (0 : Fin 4) < 1 by decide)
        have he : f 0 = f 1 := Subsingleton.elim _ _
        simp [he] at h⟩
    let : Unique (Avoider 1) := ⟨⟨one⟩, fun π => Subtype.ext (Subsingleton.elim _ _)⟩
    simp [descents, descentAt]
  have partition (n : ℕ) :
      S n = (if n = 1 then 1 else 0) + P false n + P true n := by
    by_cases hn0 : n = 0
    · subst n
      simp [S, small]
    by_cases hn1 : n = 1
    · subst n
      simp [S, singleton, small]
    have signs (π : Avoider n) :
        ¬HasProperCut false π.val ↔ HasProperCut true π.val := by
      constructor
      · intro hn
        obtain ⟨m, hm, hmn, hc⟩ := avoidance_proper_cut (by omega) π.val
          π.property.1 π.property.2
        rcases hc with hc | hc
        · exact (hn ⟨m, hm, hmn, hc⟩).elim
        · exact ⟨m, hm, hmn, hc⟩
      · intro ht hf
        exact incompatible false π.val hf ht
    have reindex := Fintype.sum_equiv (Equiv.subtypeEquivRight signs)
      (fun π => (X : ℕ[X]) ^ descents π.val.val)
      (fun π : SignedAvoider true n => (X : ℕ[X]) ^ descents π.val.val)
      (fun _ => rfl)
    have split := Fintype.sum_subtype_add_sum_subtype
      (fun π : Avoider n => HasProperCut false π.val)
      (fun π => (X : ℕ[X]) ^ descents π.val)
    rw [reindex] at split
    simpa [S, P, hn0, hn1] using split.symm
  have rightWeight (s : Bool) (k : ℕ) :
      (∑ β : RightFactor s k, (X : ℕ[X]) ^ descents β.val.val) =
        (if k = 1 then 1 else 0) + P (!s) k := by
    by_cases hk : k = 1
    · subst k
      have hsum := Finset.sum_subtype (Finset.univ : Finset (Avoider 1))
        (p := fun β => 1 = 1 ∨ HasProperCut (!s) β.val)
        (F := inferInstance)
        (by intro β; simp) (fun β => (X : ℕ[X]) ^ descents β.val)
      rw [← hsum, singleton]
      simp [small]
    · have hsum := Fintype.sum_equiv
        (Equiv.subtypeEquivRight (fun β : Avoider k =>
          show (k = 1 ∨ HasProperCut (!s) β.val) ↔ HasProperCut (!s) β.val by simp [hk]))
        (fun β : RightFactor s k => (X : ℕ[X]) ^ descents β.val.val)
        (fun β : SignedAvoider (!s) k => (X : ℕ[X]) ^ descents β.val.val)
        (fun _ => rfl)
      simpa [hk, P] using hsum
  have recurrence (s : Bool) (n : ℕ) :
      P s n = X ^ (if s then 1 else 0) *
        ∑ m : PositiveSplit n, S m.val.val *
          ((if n - m.val.val = 1 then 1 else 0) + P (!s) (n - m.val.val)) := by
    obtain ⟨e, he⟩ := hequiv s n
    have hsum := Fintype.sum_equiv e
      (fun x : Factors s n => (X : ℕ[X]) ^
        (descents x.2.1.val + descents x.2.2.val.val + (if s then 1 else 0)))
      (fun π : SignedAvoider s n => (X : ℕ[X]) ^ descents π.val.val)
      (fun x => by rw [(he x).2.2.2])
    change _ = P s n at hsum
    rw [← hsum, Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [S, if_neg (Nat.ne_of_gt m.property), ← rightWeight s (n - m.val.val),
      Fintype.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    simp only [pow_add]
    ac_rfl
  have delta_coeff (k r : ℕ) :
      ((if k = 1 then 1 else 0) : ℕ[X]).coeff r =
        if k = 1 ∧ r = 0 then 1 else 0 := by
    by_cases hk : k = 1 <;> simp [hk, coeff_one]
  have convolution (s : Bool) (n r : ℕ) :
      (∑ m : PositiveSplit n, S m.val.val *
        ((if n - m.val.val = 1 then 1 else 0) + P (!s) (n - m.val.val))).coeff r =
      ∑ m : PositiveSplit n, ∑ ab ∈ Finset.antidiagonal r,
        (S m.val.val).coeff ab.1 *
          ((if n - m.val.val = 1 ∧ ab.2 = 0 then 1 else 0) +
            (P (!s) (n - m.val.val)).coeff ab.2) := by
    rw [finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro m _
    rw [coeff_mul]
    apply Finset.sum_congr rfl
    intro ab _
    rw [coeff_add, delta_coeff]
  refine ⟨hequiv, by simp [S], by simpa [S] using singleton,
    fun s => ⟨small s 0 (by omega), small s 1 (by omega)⟩,
    partition, recurrence, ?_, ?_, ?_, ?_⟩
  · intro n r
    rw [partition, coeff_add, coeff_add, delta_coeff]
  · intro n r
    rw [recurrence false n]
    simpa only [Bool.false_eq_true, ↓reduceIte, pow_zero, one_mul, Bool.not_false]
      using convolution false n r
  · intro n
    rw [recurrence true n]
    simp
  · intro n r
    rw [recurrence true n]
    simpa only [↓reduceIte, pow_one, coeff_X_mul, Bool.not_true]
      using convolution true n r

#print axioms result

end D5.S1.Words.Patterns.Separable.GreatestCutEnumeration
