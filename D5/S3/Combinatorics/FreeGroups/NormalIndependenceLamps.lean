/- GID: D5/S3/Combinatorics/FreeGroups/NormalIndependenceLamps
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FreeGroups/NormalIndependenceLamps
   mirror-E: none(waiver:explicit-coset-action)
   anchors: [mathlib/module/Mathlib.GroupTheory.SpecificGroups.ZGroup]
   utility: none
   digest: Binary lamp configurations distinguish all indexed ordered coset orbits. -/
import Mathlib.GroupTheory.SpecificGroups.ZGroup

namespace D5.S3.Combinatorics.FreeGroups.NormalIndependenceLamps

noncomputable section

/-- Binary lamps construct and classify the indexed ordered coset orbits. -/
theorem lamplighter_orbits :
    ∃ φ : Multiplicative ℤ →* MulAut (Multiplicative (ℤ →₀ ZMod 2)),
      let Q := SemidirectProduct (Multiplicative (ℤ →₀ ZMod 2)) (Multiplicative ℤ) φ
      ∃ (H : Subgroup Q) (sigma tau : Q),
        let x0 : Q ⧸ H := QuotientGroup.mk 1
        sigma ^ 2 = 1 ∧ sigma • x0 = x0 ∧
        (∀ e f : List Bool,
          (∃ g : Q, g • x0 = x0 ∧
            g • ((tau * (e.map fun b => sigma ^ (if b then 1 else 0) * tau).prod) • x0) =
              (tau * (f.map fun b => sigma ^ (if b then 1 else 0) * tau).prod) • x0) ↔ e = f) ∧
        (∀ e f : List Bool,
          ¬ ∃ g : Q,
            g • x0 = (tau * (f.map fun b => sigma ^ (if b then 1 else 0) * tau).prod) • x0 ∧
            g • ((tau * (e.map fun b => sigma ^ (if b then 1 else 0) * tau).prod) • x0) = x0) ∧
        (∀ e : List Bool, ∀ x : Q ⧸ H,
          ¬ ∃ g : Q, g • x0 = x ∧
            g • ((tau * (e.map fun b => sigma ^ (if b then 1 else 0) * tau).prod) • x0) = x) := by
  let φ : Multiplicative ℤ →* MulAut (Multiplicative (ℤ →₀ ZMod 2)) := {
    toFun := fun p =>
      AddEquiv.toMultiplicative (Finsupp.domCongr (Equiv.addRight p.toAdd))
    map_one' := by
      ext f j
      simp [Finsupp.domCongr, Finsupp.equivMapDomain_apply, Equiv.addRight]
    map_mul' := by
      intro p q
      ext f j
      simp [Finsupp.domCongr, Finsupp.equivMapDomain_apply, Equiv.addRight,
        add_assoc, add_comm] }
  let Q := SemidirectProduct (Multiplicative (ℤ →₀ ZMod 2)) (Multiplicative ℤ) φ
  let sigma : Q := ⟨Multiplicative.ofAdd (Finsupp.single 0 1), Multiplicative.ofAdd 0⟩
  let tau : Q := ⟨Multiplicative.ofAdd 0, Multiplicative.ofAdd 1⟩
  let H : Subgroup Q := {
    carrier := {x | x.right.toAdd = 0 ∧ ∀ j : ℤ, j ≠ 0 → x.left.toAdd j = 0}
    one_mem' := by
      change (0 : ℤ) = 0 ∧ ∀ j : ℤ, j ≠ 0 → (0 : ℤ →₀ ZMod 2) j = 0
      simp
    mul_mem' := by
      rintro x y ⟨hx, hfx⟩ ⟨hy, hfy⟩
      constructor
      · exact (congrArg₂ (· + ·) hx hy).trans (zero_add 0)
      · intro j hj
        change x.left.toAdd j +
          Finsupp.equivMapDomain (Equiv.addRight x.right.toAdd) y.left.toAdd j = 0
        simp [Finsupp.equivMapDomain_apply, Equiv.addRight, hx, hfx j hj, hfy j hj]
    inv_mem' := by
      rintro x ⟨hx, hfx⟩
      constructor
      · exact (congrArg Neg.neg hx).trans (neg_zero)
      · intro j hj
        change (-Finsupp.equivMapDomain (Equiv.addRight (-x.right.toAdd)) x.left.toAdd) j = 0
        simp [Finsupp.equivMapDomain_apply, Equiv.addRight, hx, hfx j hj] }
  let x0 : Q ⧸ H := QuotientGroup.mk 1
  let q : List Bool → Q := fun e =>
    e.foldr (fun b rest => tau * sigma ^ (if b then 1 else 0 : ℕ) * rest) tau
  have qnil : q [] = tau := rfl
  have qcons (b : Bool) (bs : List Bool) :
      q (b :: bs) = tau * sigma ^ (if b then 1 else 0 : ℕ) * q bs := rfl
  have indexed_coordinates (e : List Bool) :
      q e = tau * (e.map (fun b => sigma ^ (if b then 1 else 0 : ℕ) * tau)).prod ∧
      (q e).right.toAdd = (e.length : ℤ) + 1 ∧
      (∀ j : ℤ, j ≤ 0 ∨ (e.length : ℤ) + 1 ≤ j → (q e).left.toAdd j = 0) ∧
      (∀ i : ℕ, (q e).left.toAdd ((i : ℤ) + 1) =
        if e[i]? = some true then 1 else 0) := by
    have step (b : Bool) (bs : List Bool) (j : ℤ) :
        (q (b :: bs)).left.toAdd j =
          (if j = 1 ∧ b = true then 1 else 0) + (q bs).left.toAdd (j - 1) := by
      rw [qcons]
      cases b
      · simp only [Bool.false_eq_true, if_false, pow_zero, mul_one]
        change (0 : ZMod 2) + (q bs).left.toAdd (j - 1) = _
        simp
      · simp only [if_true, pow_one]
        change ((0 : ZMod 2) + Finsupp.single 0 (1 : ZMod 2) (j - 1)) +
          (q bs).left.toAdd (j - 1) = _
        have hj : 0 = j - 1 ↔ j = 1 := by omega
        simp [Finsupp.single_apply, hj]
    induction e with
    | nil => simp [qnil, tau]
    | cons b bs ih =>
      rcases ih with ⟨hp, ht, hz, hi⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [qcons, hp, List.map_cons, List.prod_cons, mul_assoc]
      · rw [qcons]
        cases b <;>
          simp only [Bool.false_eq_true, if_false, if_true, pow_zero, pow_one, mul_one]
        all_goals
          change (1 : ℤ) + (q bs).right.toAdd = _
          rw [ht]
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          omega
      · intro j hj
        rw [step]
        have hjone : j ≠ 1 := by simp only [List.length_cons] at hj; omega
        have hjtail : j - 1 ≤ 0 ∨ (bs.length : ℤ) + 1 ≤ j - 1 := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hj
          omega
        simp [hjone, hz _ hjtail]
      · intro i
        rw [step]
        cases i with
        | zero =>
          have hzero := hz 0 (Or.inl (le_refl 0))
          cases b <;> simp [hzero]
        | succ i =>
          have hne : (↑i : ℤ) + 1 ≠ 0 := by omega
          simp [hne, hi, Nat.cast_add, Nat.cast_one]

  have orbit_classification :
      sigma ^ 2 = 1 ∧ sigma • x0 = x0 ∧
      (∀ e f : List Bool,
        (∃ g : Q, g • x0 = x0 ∧ g • (q e • x0) = q f • x0) ↔ e = f) ∧
      (∀ e f : List Bool,
        ¬ ∃ g : Q, g • x0 = q f • x0 ∧ g • (q e • x0) = x0) ∧
      (∀ e : List Bool, ∀ x : Q ⧸ H,
        ¬ ∃ g : Q, g • x0 = x ∧ g • (q e • x0) = x) := by
    have shift_apply (p : ℤ) (f : ℤ →₀ ZMod 2) (j : ℤ) :
        Finsupp.equivMapDomain (Equiv.addRight p) f j = f (j - p) := rfl
    have mk_eq (u v : Q) :
        (QuotientGroup.mk u : Q ⧸ H) = QuotientGroup.mk v ↔
          ∃ h : Q, h ∈ H ∧ v = u * h := by
      constructor
      · intro h
        refine ⟨u⁻¹ * v, QuotientGroup.eq.mp h, ?_⟩
        exact (mul_inv_cancel_left u v).symm
      · rintro ⟨h, hh, rfl⟩
        exact (QuotientGroup.mk_mul_of_mem u hh).symm
    have fix_mem (g : Q) (h : g • x0 = x0) : g ∈ H := by
      have heq : (QuotientGroup.mk g : Q ⧸ H) = QuotientGroup.mk 1 := by
        simpa [x0] using h
      have hm := QuotientGroup.eq.mp heq.symm
      simpa using hm
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [pow_two]
      apply SemidirectProduct.ext
      · ext j
        change ((Finsupp.single 0 (1 : ZMod 2) : ℤ →₀ ZMod 2) +
          Finsupp.equivMapDomain (Equiv.addRight (0 : ℤ)) (Finsupp.single 0 (1 : ZMod 2))) j = 0
        by_cases hj : j = 0
        · subst j
          simp only [Finsupp.add_apply, shift_apply, sub_zero, Finsupp.single_eq_same]
          decide
        · simp [hj]
      · rfl
    · have hs : sigma ∈ H := by
        change (0 : ℤ) = 0 ∧ ∀ j : ℤ, j ≠ 0 → Finsupp.single 0 (1 : ZMod 2) j = 0
        simp [Finsupp.single_apply, eq_comm]
      change (QuotientGroup.mk (sigma * 1) : Q ⧸ H) = QuotientGroup.mk 1
      rw [mul_one]
      apply (mk_eq sigma 1).mpr
      exact ⟨sigma⁻¹, H.inv_mem hs, (mul_inv_cancel sigma).symm⟩
    · intro e f
      constructor
      · rintro ⟨g, hg, hgf⟩
        have hgm := fix_mem g hg
        change g.right.toAdd = 0 ∧ ∀ j : ℤ, j ≠ 0 → g.left.toAdd j = 0 at hgm
        have heq : (QuotientGroup.mk (g * q e) : Q ⧸ H) = QuotientGroup.mk (q f) := by
          simpa [x0, mul_smul] using hgf
        obtain ⟨h, hh, heq⟩ := (mk_eq _ _).mp heq
        change h.right.toAdd = 0 ∧ ∀ j : ℤ, j ≠ 0 → h.left.toAdd j = 0 at hh
        have ce := indexed_coordinates e
        have cf := indexed_coordinates f
        have hp := congrArg (fun z : Q => z.right.toAdd) heq
        change (q f).right.toAdd = (g.right.toAdd + (q e).right.toAdd) + h.right.toAdd at hp
        rw [ce.2.1, cf.2.1, hgm.1, hh.1] at hp
        have hl : e.length = f.length := by omega
        apply List.ext_getElem hl
        intro i hi hf
        have hj : (i : ℤ) + 1 ≠ 0 := by omega
        have hjp : (i : ℤ) + 1 - ((e.length : ℤ) + 1) ≠ 0 := by omega
        have hv := congrArg (fun z : Q => z.left.toAdd ((i : ℤ) + 1)) heq
        change (q f).left.toAdd ((i : ℤ) + 1) =
          g.left.toAdd ((i : ℤ) + 1) +
          Finsupp.equivMapDomain (Equiv.addRight g.right.toAdd) (q e).left.toAdd ((i : ℤ) + 1) +
          Finsupp.equivMapDomain (Equiv.addRight (g.right.toAdd + (q e).right.toAdd)) h.left.toAdd
            ((i : ℤ) + 1) at hv
        simp only [shift_apply, hgm.1, ce.2.1, zero_add, sub_zero,
          hgm.2 _ hj, hh.2 _ hjp] at hv
        rw [ce.2.2.2, cf.2.2.2, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hf] at hv
        cases hei : e[i] <;> cases hfi : f[i] <;> simp [hei, hfi] at hv ⊢
      · rintro rfl
        exact ⟨1, one_smul _ _, one_smul _ _⟩
    · intro e f
      rintro ⟨g, hgf, hge⟩
      have eqf : (QuotientGroup.mk (q f) : Q ⧸ H) = QuotientGroup.mk g := by
        simpa [x0] using hgf.symm
      obtain ⟨h, hh, hgh⟩ := (mk_eq _ _).mp eqf
      have hm := fix_mem (g * q e) (by simpa [mul_smul] using hge)
      change h.right.toAdd = 0 ∧ _ at hh
      change g.right.toAdd + (q e).right.toAdd = 0 ∧ _ at hm
      have hp := congrArg (fun z : Q => z.right.toAdd) hgh
      change g.right.toAdd = (q f).right.toAdd + h.right.toAdd at hp
      have ce := (indexed_coordinates e).2.1
      have cf := (indexed_coordinates f).2.1
      rw [ce] at hm
      rw [cf, hh.1] at hp
      omega
    · intro e x
      rintro ⟨g, hgx, hge⟩
      have hsame : g • (q e • x0) = g • x0 := hge.trans hgx.symm
      have hbase : q e • x0 = x0 := (MulAction.injective g) hsame
      have hm := fix_mem (q e) hbase
      change (q e).right.toAdd = 0 ∧ _ at hm
      have hp := (indexed_coordinates e).2.1
      omega
  refine ⟨φ, H, sigma, tau, ?_⟩
  have hp (e : List Bool) := (indexed_coordinates e).1
  simpa only [hp] using orbit_classification

end

end D5.S3.Combinatorics.FreeGroups.NormalIndependenceLamps
