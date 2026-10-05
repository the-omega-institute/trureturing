/- GID: D5/S3/Combinatorics/FreeGroups/NormalIndependenceSeparator
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FreeGroups/NormalIndependenceSeparator
   mirror-E: none(waiver:explicit-finite-support-separating-action)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Finite-support lamp shears give explicit separating homomorphisms. -/

import D5.S3.Combinatorics.FreeGroups.NormalIndependenceWords
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.FreeGroups.NormalIndependenceSeparator

open NormalIndependenceWords

noncomputable section

/-- The finite-support shear construction separates one binary commutator from all others. -/
theorem separating_hom {Q X α : Type*} [Group Q] [MulAction Q X]
    (a b : α) (hab : a ≠ b) (σ τ : Q) (x₀ : X) (target : List Bool)
    (hσ : σ ^ 2 = 1) (hfix : σ • x₀ = x₀)
    (k : X → X → ZMod 3) (hd : ∀ x, k x x = 0)
    (hi : ∀ (g : Q) (x y : X), k (g • x) (g • y) = k x y)
    (hf : ∀ e : List Bool,
      k x₀ ((τ * (e.map fun bit => σ ^ (if bit then 1 else 0) * τ).prod) • x₀) =
        if e = target then 1 else 0)
    (hr : ∀ e : List Bool,
      k ((τ * (e.map fun bit => σ ^ (if bit then 1 else 0) * τ).prod) • x₀) x₀ = 0) :
    ∃ φ : FreeGroup α →* Equiv.Perm ((X →₀ ZMod 3) × ZMod 3),
      φ (s a b target) ≠ 1 ∧ ∀ e, e ≠ target → φ (s a b e) = 1 := by
  classical
  let L := fun x => Finsupp.linearCombination (ZMod 3) (k x)
  let E (x : X) : Equiv.Perm ((X →₀ ZMod 3) × ZMod 3) := {
    toFun z := (z.1 + Finsupp.single x 1, z.2 + L x z.1)
    invFun z := (z.1 - Finsupp.single x 1, z.2 - L x z.1)
    left_inv z := by rcases z with ⟨v, c⟩; simp [L, map_add, hd]
    right_inv z := by rcases z with ⟨v, c⟩; simp [L, map_sub, hd] }
  let T : Q →* Equiv.Perm ((X →₀ ZMod 3) × ZMod 3) := {
    toFun q := Equiv.prodCongr
      (Finsupp.domCongr (MulAction.toPerm q)).toEquiv (Equiv.refl _)
    map_one' := by
      ext z : 1
      apply Prod.ext
      · simp [Finsupp.domCongr, Finsupp.equivMapDomain_eq_mapDomain,
          show (MulAction.toPerm (1 : Q) : X → X) = id by funext x; exact one_smul Q x]
      · rfl
    map_mul' q p := by
      ext z : 1
      apply Prod.ext
      · change Finsupp.equivMapDomain (MulAction.toPerm (q * p)) z.1 =
          Finsupp.equivMapDomain (MulAction.toPerm q)
            (Finsupp.equivMapDomain (MulAction.toPerm p) z.1)
        simp only [Finsupp.equivMapDomain_eq_mapDomain]
        rw [← Finsupp.mapDomain_comp]
        congr 1
        funext x
        exact mul_smul q p x
      · rfl }
  have hL (g : Q) (x : X) (v : X →₀ ZMod 3) :
      L (g • x) ((T g (v, 0)).1) = L x v := by
    simp [L, T, Finsupp.domCongr,
      Finsupp.equivMapDomain_eq_mapDomain, Function.comp_def,
      hi]
  have hconj (g : Q) (x : X) : T g * E x = E (g • x) * T g := by
    ext z : 1
    apply Prod.ext
    · simp [T, E, L, Finsupp.domCongr,
        Finsupp.equivMapDomain_eq_mapDomain, Finsupp.mapDomain_add]
    · simpa [E, L, T] using
        congrArg (fun c => z.2 + c) (hL g x z.1).symm
  have h3 : (3 : ZMod 3) = 0 := by decide
  have he3 (x : X) : E x ^ 3 = 1 := by
    ext z : 1
    apply Prod.ext
    · simp [E, L, pow_succ, add_assoc, ← Finsupp.single_add]
      exact h3
    · simp [E, L, pow_succ, hd, map_add]
      ring_nf
      simp [h3]
  let A := E x₀ * T σ
  let B := T τ
  have hcomm : T σ * E x₀ = E x₀ * T σ := by simpa [hfix] using hconj σ x₀
  have hs : T σ * T σ = 1 := by rw [← map_mul, ← pow_two, hσ, map_one]
  have ha2 : A ^ 2 = E x₀ ^ 2 := by
    simp only [A, pow_two]
    calc
      E x₀ * T σ * (E x₀ * T σ) = E x₀ * (T σ * E x₀) * T σ := by
        simp only [mul_assoc]
      _ = E x₀ * (E x₀ * T σ) * T σ := by rw [hcomm]
      _ = E x₀ ^ 2 := by
        simp [mul_assoc, hs, pow_two]
  have ha3 : A ^ 3 = T σ := by
    rw [pow_succ, ha2]
    simp [A, ← mul_assoc, ← pow_succ, he3]
  let φ : FreeGroup α →* Equiv.Perm ((X →₀ ZMod 3) × ZMod 3) :=
    FreeGroup.lift (fun i => if i = a then A else if i = b then B else 1)
  have hfa : φ (FreeGroup.of a) = A := by simp [φ]
  have hfb : φ (FreeGroup.of b) = B := by simp [φ, hab.symm]
  have hu (e : List Bool) : φ (u a b e) =
      T (τ * (e.map fun bit => σ ^ (if bit then 1 else 0) * τ).prod) := by
    have hp :
        φ ((e.map fun bit => FreeGroup.of a ^ (if bit then 3 else 0) *
          FreeGroup.of b).prod) =
          T ((e.map fun bit => σ ^ (if bit then 1 else 0) * τ).prod) := by
      induction e with
      | nil => simp
      | cons bit e ih =>
        simp only [List.map_cons, List.prod_cons, map_mul, ih]
        cases bit <;> simp [hfa, hfb, ha3, B]
    simp only [u, map_mul, hfb, hp, B]
  have himage (e : List Bool) :
      φ (s a b e) =
        { toFun := fun z => (z.1, z.2 + (if e = target then 1 else 0))
          invFun := fun z => (z.1, z.2 - (if e = target then 1 else 0))
          left_inv := by intro ⟨v, c⟩; simp
          right_inv := by intro ⟨v, c⟩; simp } := by
    let q := τ * (e.map fun bit => σ ^ (if bit then 1 else 0) * τ).prod
    let y := q • x₀
    have hxy : k x₀ y = if e = target then 1 else 0 := hf e
    have hyx : k y x₀ = 0 := hr e
    have hc : T q * E x₀ ^ 2 * (T q)⁻¹ = E y ^ 2 := by
      rw [show T q * E x₀ ^ 2 = E y ^ 2 * T q by
        simpa [y, pow_two, mul_assoc] using
          calc T q * E x₀ * E x₀ = E y * T q * E x₀ := by rw [hconj]
               _ = E y * E y * T q := by rw [mul_assoc, hconj]; simp [mul_assoc, y]]
      simp
    have hinv (x : X) : (E x ^ 2)⁻¹ = E x := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_succ, mul_assoc] using he3 x
    simp only [s, map_mul, map_pow, map_inv, hfa, ha2, hu]
    simp only [← map_mul]
    change E x₀ ^ 2 * T q * E x₀ ^ 2 * (T q)⁻¹ * (E x₀ ^ 2)⁻¹ *
      T q * (E x₀ ^ 2)⁻¹ * (T q)⁻¹ = _
    have hc1 : T q * E x₀ * (T q)⁻¹ = E y := by rw [hconj]; simp [y]
    rw [hinv]
    calc
      _ = E x₀ ^ 2 * (T q * E x₀ ^ 2 * (T q)⁻¹) * E x₀ *
          (T q * E x₀ * (T q)⁻¹) := by simp only [mul_assoc]
      _ = E x₀ ^ 2 * E y ^ 2 * E x₀ * E y := by rw [hc, hc1]
      _ = _ := by
        ext z : 1
        apply Prod.ext
        · simp [E, L, pow_two, add_assoc, ← Finsupp.single_add]
          ext j
          simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.zero_apply]
          split_ifs <;> ring_nf <;> simp [h3, show (6 : ZMod 3) = 0 by decide]
        · simp [E, L, pow_two, hd, map_add, hxy, hyx]
          split_ifs <;> ring_nf <;>
            simp [h3, show (7 : ZMod 3) = 1 by decide]
  refine ⟨φ, ?_, ?_⟩
  · intro h
    have he := congrArg (fun P : Equiv.Perm ((X →₀ ZMod 3) × ZMod 3) => P (0, 0)) h
    rw [himage] at he
    have := congrArg Prod.snd he
    norm_num at this
  · intro e he
    rw [himage]
    ext z : 1
    simp [he]

end

end D5.S3.Combinatorics.FreeGroups.NormalIndependenceSeparator
