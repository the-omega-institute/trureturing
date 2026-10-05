/- GID: D5/S3/Combinatorics/FreeGroups/NormalIndependence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FreeGroups/NormalIndependence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Binary lamp separators settle Koch-Hyde and Olive's normal-independence problem. -/

import D5.S3.Combinatorics.FreeGroups.NormalIndependenceDefs
import D5.S3.Combinatorics.FreeGroups.NormalIndependenceLamps
import D5.S3.Combinatorics.FreeGroups.NormalIndependenceSeparator

set_option autoImplicit false

namespace D5.S3.Combinatorics.FreeGroups.NormalIndependence

open NormalIndependenceDefs NormalIndependenceWords NormalIndependenceLamps

/-- A positive answer to Koch-Hyde and Olive's Problem 5.2 in every rank at least two. -/
theorem result : NormalIndependenceDefs.claim := by
  classical
  intro r hr
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    dsimp [a, b] at this
    omega
  obtain ⟨action, H, sigma, tau, hσ, hfix, hforward, hreverse, hdiagonal⟩ :=
    lamplighter_orbits
  let Q := SemidirectProduct (Multiplicative (ℤ →₀ ZMod 2)) (Multiplicative ℤ) action
  let x0 : Q ⧸ H := QuotientGroup.mk 1
  have separators (t : List Bool) :
      ∃ φ : FreeGroup (Fin r) →* Equiv.Perm (((Q ⧸ H) →₀ ZMod 3) × ZMod 3),
        φ (s a b t) ≠ 1 ∧ ∀ e, e ≠ t → φ (s a b e) = 1 := by
    let O : (Q ⧸ H) → (Q ⧸ H) → Prop := fun x y => ∃ g : Q,
      g • x0 = x ∧
        g • ((tau * (t.map fun bit => sigma ^ (if bit then 1 else 0) * tau).prod) • x0) = y
    let k : (Q ⧸ H) → (Q ⧸ H) → ZMod 3 := fun x y => if O x y then 1 else 0
    have hd (x : Q ⧸ H) : k x x = 0 := by
      exact if_neg (show ¬ O x x from hdiagonal t x)
    have hi (g : Q) (x y : Q ⧸ H) : k (g • x) (g • y) = k x y := by
      have ho : O (g • x) (g • y) ↔ O x y := by
        constructor
        · rintro ⟨h, hx, hy⟩
          refine ⟨g⁻¹ * h, ?_, ?_⟩
          · rw [mul_smul, hx]
            exact inv_smul_smul g x
          · rw [mul_smul, hy]
            exact inv_smul_smul g y
        · rintro ⟨h, hx, hy⟩
          refine ⟨g * h, ?_, ?_⟩
          · rw [mul_smul, hx]
          · rw [mul_smul, hy]
      simp only [k, ho]
    have hf (e : List Bool) :
        k x0 ((tau * (e.map fun bit =>
          sigma ^ (if bit then 1 else 0) * tau).prod) • x0) =
          if e = t then 1 else 0 := by
      have ho : O x0 ((tau * (e.map fun bit =>
          sigma ^ (if bit then 1 else 0) * tau).prod) • x0) ↔ e = t :=
        (hforward t e).trans eq_comm
      simp only [k, ho]
    have hb (e : List Bool) :
        k ((tau * (e.map fun bit =>
          sigma ^ (if bit then 1 else 0) * tau).prod) • x0) x0 = 0 := by
      exact if_neg (show ¬ O _ _ from hreverse t e)
    exact NormalIndependenceSeparator.separating_hom a b hab sigma tau x0 t
      hσ hfix k hd hi hf hb
  choose Φ hΦ using separators
  have hs : Function.Injective (s a b) := by
    intro e f hef
    by_contra hne
    have h := congrArg (Φ e) hef
    rw [(hΦ e).2 f (Ne.symm hne)] at h
    exact (hΦ e).1 h
  have hgrowth : GrowsExponentially (Set.range (s a b)) := by
    classical
    have hfinite : ∀ n : ℕ, {e : List Bool | e.length ≤ n}.Finite := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        apply ((Set.finite_singleton []).union
          ((ih.image (List.cons false)).union (ih.image (List.cons true)))).subset
        intro e he
        cases e with
        | nil => simp
        | cons bit e =>
          have he' : e.length ≤ n := by simpa using he
          cases bit <;> simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image]
          · exact Or.inr (Or.inl ⟨e, he', rfl⟩)
          · exact Or.inr (Or.inr ⟨e, he', rfl⟩)
    refine ⟨33 / 32, by norm_num, 1 / 4, by norm_num, 12, ?_⟩
    intro n hn
    let m := (n - 12) / 16
    let f : (Fin m → Bool) → FreeGroup (Fin r) := fun e => s a b (List.ofFn e)
    have hf : Function.Injective f := hs.comp List.ofFn_injective
    let T := Set.range (s a b) ∩ {g | NormalIndependenceDefs.wordLength g ≤ n}
    have hT : T.Finite := by
      apply ((hfinite n).image (s a b)).subset
      rintro g ⟨⟨e, rfl⟩, he⟩
      refine ⟨e, ?_, rfl⟩
      change (FreeGroup.toWord (s a b e)).length ≤ n at he
      rw [relator_length a b hab e] at he
      change e.length ≤ n
      omega
    have hm : 16 * m + 12 ≤ n := by
      have h := Nat.mul_div_le (n - 12) 16
      dsimp [m]
      omega
    have hlevel : Set.range f ⊆ T := by
      rintro g ⟨e, rfl⟩
      refine ⟨⟨List.ofFn e, rfl⟩, ?_⟩
      change (FreeGroup.toWord (s a b (List.ofFn e))).length ≤ n
      rw [relator_length a b hab]
      have hcount := List.count_le_length (a := true) (l := List.ofFn e)
      simp only [List.length_ofFn] at hcount ⊢
      omega
    have hcard : 2 ^ m ≤ T.ncard := by
      have h := Set.ncard_le_ncard hlevel hT
      rw [Set.ncard_range_of_injective hf] at h
      simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using h
    have hbase : (33 / 32 : ℝ) ^ 16 ≤ 2 := by norm_num
    have hnm : n ≤ 16 * (m + 2) := by
      have hmod := Nat.mod_lt (n - 12) (by omega : 0 < 16)
      have hdiv := Nat.div_add_mod (n - 12) 16
      dsimp [m]
      omega
    have hpow : (33 / 32 : ℝ) ^ n ≤ 4 * (2 : ℝ) ^ m := by
      calc
        (33 / 32 : ℝ) ^ n ≤ (33 / 32 : ℝ) ^ (16 * (m + 2)) :=
          pow_le_pow_right₀ (by norm_num) hnm
        _ = ((33 / 32 : ℝ) ^ 16) ^ (m + 2) := by rw [pow_mul]
        _ ≤ (2 : ℝ) ^ (m + 2) := pow_le_pow_left₀ (by positivity) hbase _
        _ = 4 * (2 : ℝ) ^ m := by rw [pow_add]; norm_num [mul_comm]
    have hcard' : (2 : ℝ) ^ m ≤ (T.ncard : ℝ) := by exact_mod_cast hcard
    change (1 / 4 : ℝ) * (33 / 32 : ℝ) ^ n ≤ (T.ncard : ℝ)
    linarith
  refine ⟨Set.range (s a b), ?_, hgrowth⟩
  rintro z ⟨t, rfl⟩ hnormal
  have hsub : Set.range (s a b) \ {s a b t} ⊆ (Φ t).ker := by
    rintro z ⟨⟨e, rfl⟩, he⟩
    have het : e ≠ t := by
      rintro rfl
      exact he (Set.mem_singleton _)
    exact (hΦ t).2 e het
  exact (hΦ t).1 (Subgroup.normalClosure_le_normal hsub hnormal)

end D5.S3.Combinatorics.FreeGroups.NormalIndependence
