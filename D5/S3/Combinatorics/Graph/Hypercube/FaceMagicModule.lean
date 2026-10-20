/- GID: D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/FaceMagicModule
   mirror-E: none(waiver:all-ring-face-magic-coordinate-classification)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: All-ring coordinate classification of unrestricted face-magic hypercubes. -/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

/-!
This module settles the unrestricted full-cube face-magic module question over every
unital ring, including noncommutative rings.  The public predicate and submodule are
the source definitions; the public structure theorem is the sole settling result.
-/

/-
FaceMagic: proof_shape: definition consumed by faceMagicModule and the structure theorem;
  escape_witness: none.
faceMagicModule: proof_shape: content (the actual existential-witness submodule);
  escape_witness: none.
face_magic_module_structure: proof_shape: bind-only settling result with explicit
  reconstruction and inverse laws; escape_witness: none.
admission_basis: open-problem-resolution (#19560; Proved).
Direct frozen dependencies: pinned Mathlib Finset cardinality, finite-set induction,
  finite sums, product linear maps, parity and noncommutative ring normalization.
-/

namespace D5.S3.Combinatorics.Graph.Hypercube.FaceMagicModule

variable {R : Type*} [Ring R]

/-- A full cube array is face magic when all two-coordinate faces have one common sum. -/
def FaceMagic (n : ℕ) (f : Finset (Fin n) → R) : Prop :=
  ∃ C : R, ∀ (S : Finset (Fin n)) (i j : Fin n),
    i ∉ S → j ∉ S → i ≠ j →
      f S + f (insert i S) + f (insert j S) + f (insert i (insert j S)) = C

/-- The actual module of face-magic arrays; the common face sum is existential data, not a carrier coordinate. -/
def faceMagicModule (n : ℕ) : Submodule R (Finset (Fin n) → R) where
  carrier := {f | FaceMagic n f}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro S i j hi hj hij
    simp
  add_mem' := by
    rintro f g ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C + D, ?_⟩
    intro S i j hi hj hij
    calc
      (f + g) S + (f + g) (insert i S) + (f + g) (insert j S) +
          (f + g) (insert i (insert j S)) =
        (f S + f (insert i S) + f (insert j S) + f (insert i (insert j S))) +
          (g S + g (insert i S) + g (insert j S) + g (insert i (insert j S))) := by
            simp only [Pi.add_apply]
            abel
      _ = C + D := by rw [hC S i j hi hj hij, hD S i j hi hj hij]
  smul_mem' := by
    intro r f ⟨C, hC⟩
    refine ⟨r • C, ?_⟩
    intro S i j hi hj hij
    simpa only [Pi.smul_apply, smul_add] using
      congrArg (fun z : R => r • z) (hC S i j hi hj hij)

private def signedFormula {n : ℕ} (a : R) (b : Fin n → R) (C : R)
    (S : Finset (Fin n)) : R :=
  (-1 : R) ^ S.card *
    ((1 - (S.card : R)) * a - ∑ i ∈ S, b i + ((S.card / 2 : ℕ) : R) * C)

private theorem signedFormula_empty {n : ℕ} (a C : R) (b : Fin n → R) :
    signedFormula a b C ∅ = a := by
  simp [signedFormula]

private theorem signedFormula_singleton {n : ℕ} (a C : R) (b : Fin n → R) (i : Fin n) :
    signedFormula a b C {i} = b i := by
  simp [signedFormula]

private theorem signedFormula_face {n : ℕ} (a C : R) (b : Fin n → R)
    (S : Finset (Fin n)) (i j : Fin n)
    (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    signedFormula a b C S + signedFormula a b C (insert i S) +
      signedFormula a b C (insert j S) +
      signedFormula a b C (insert i (insert j S)) = C := by
  have hij' : j ∉ insert i S := by simp [hj, hij, Ne.symm hij]
  have hi' : i ∉ insert j S := by simp [hi, hij]
  have hcardi : (insert i S).card = S.card + 1 := by
    rw [Finset.card_insert_of_notMem hi]
  have hcardj : (insert j S).card = S.card + 1 := by
    rw [Finset.card_insert_of_notMem hj]
  have hcardij : (insert i (insert j S)).card = S.card + 2 := by
    rw [Finset.card_insert_of_notMem hi', Finset.card_insert_of_notMem hj]
  have hsum_i : (∑ x ∈ insert i S, b x) = (∑ x ∈ S, b x) + b i := by
    rw [Finset.sum_insert hi]
    abel
  have hsum_j : (∑ x ∈ insert j S, b x) = (∑ x ∈ S, b x) + b j := by
    rw [Finset.sum_insert hj]
    abel
  have hsum_ij : (∑ x ∈ insert i (insert j S), b x) =
      (∑ x ∈ S, b x) + b j + b i := by
    rw [Finset.sum_insert hi', Finset.sum_insert hj]
    abel
  unfold signedFormula
  rw [hcardi, hcardj, hcardij, hsum_i, hsum_j, hsum_ij]
  by_cases hpar : Even S.card
  · obtain ⟨q, hq⟩ := hpar
    have hpowq : (-1 : R) ^ q * (-1 : R) ^ q = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hdiv0 : (q + q) / 2 = q := by omega
    have hdiv1 : (q + q + 1) / 2 = q := by omega
    have hdiv2 : (q + q + 2) / 2 = q + 1 := by omega
    rw [hq]
    simp [hpowq, hdiv0, hdiv1, hdiv2, pow_succ, pow_add]
    noncomm_ring
  · have hodd : Odd S.card := Nat.not_even_iff_odd.mp hpar
    obtain ⟨q, hq⟩ := hodd
    have hpowq : (-1 : R) ^ (2 * q) * (-1 : R) = -1 := by
      rw [pow_mul]
      norm_num
    have hdiv0 : (2 * q + 1) / 2 = q := by omega
    have hdiv1 : (2 * q + 1 + 1) / 2 = q + 1 := by omega
    have hdiv2 : (2 * q + 1 + 2) / 2 = q + 1 := by omega
    rw [hq]
    simp [hpowq, hdiv0, hdiv1, hdiv2, pow_succ, pow_add]
    noncomm_ring

private theorem signedFormula_faceMagic (n : ℕ) (a C : R) (b : Fin n → R) :
    FaceMagic n (signedFormula a b C) := by
  refine ⟨C, ?_⟩
  intro S i j hi hj hij
  exact signedFormula_face a C b S i j hi hj hij

private theorem determined_by_two_faces {n : ℕ} {f g : Finset (Fin n) → R}
    {C D : R}
    (hf : ∀ (S : Finset (Fin n)) (i j : Fin n),
      i ∉ S → j ∉ S → i ≠ j →
        f S + f (insert i S) + f (insert j S) + f (insert i (insert j S)) = C)
    (hg : ∀ (S : Finset (Fin n)) (i j : Fin n),
      i ∉ S → j ∉ S → i ≠ j →
        g S + g (insert i S) + g (insert j S) + g (insert i (insert j S)) = D)
    (hC : C = D) (h0 : f ∅ = g ∅)
    (h1 : ∀ i : Fin n, f {i} = g {i}) :
    ∀ k : ℕ, ∀ S : Finset (Fin n), S.card = k → f S = g S := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro S hS
      by_cases hk0 : k = 0
      · have : S = ∅ := by simpa [hk0] using hS
        simpa [this] using h0
      by_cases hk1 : k = 1
      · have hcard : S.card = 1 := by omega
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
        rw [hi]
        exact h1 i
      · have hk2 : 2 ≤ k := by omega
        obtain ⟨i, j, hiS, hjS, hij⟩ :=
          Finset.one_lt_card_iff.mp (by omega : 1 < S.card)
        have hjErase : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.symm, hjS⟩
        let T : Finset (Fin n) := (S.erase i).erase j
        have hTj : insert j T = S.erase i := by
          exact Finset.insert_erase hjErase
        have hTi : insert i (S.erase i) = S := Finset.insert_erase hiS
        have hSrepr : insert i (insert j T) = S := by
          rw [hTj, hTi]
        have hiT : i ∉ T := by
          simp [T, hij]
        have hjT : j ∉ T := by simp [T]
        have hcardT : T.card < k := by
          simp [T, Finset.card_erase_of_mem hiS, Finset.card_erase_of_mem hjErase]
          omega
        have hcardT_eq : T.card + 2 = k := by
          simp [T, Finset.card_erase_of_mem hiS, Finset.card_erase_of_mem hjErase, hS]
          omega
        have hcardiT : (insert i T).card < k := by
          rw [Finset.card_insert_of_notMem hiT]
          omega
        have hcardjT : (insert j T).card < k := by
          rw [Finset.card_insert_of_notMem hjT]
          omega
        have hfT := hf T i j hiT hjT hij
        have hgT := hg T i j hiT hjT hij
        have hTf : f T = g T := ih T.card hcardT T rfl
        have hTif : f (insert i T) = g (insert i T) :=
          ih (insert i T).card hcardiT (insert i T) rfl
        have hTjf : f (insert j T) = g (insert j T) :=
          ih (insert j T).card hcardjT (insert j T) rfl
        rw [← hSrepr]
        calc
          f (insert i (insert j T)) =
              C - f T - f (insert i T) - f (insert j T) := by
                rw [← hfT]
                abel
          _ = D - g T - g (insert i T) - g (insert j T) := by
                rw [hC, hTf, hTif, hTjf]
          _ = g (insert i (insert j T)) := by
                rw [← hgT]
                abel

private def coordinateMap {n : ℕ} (hn : 2 ≤ n) :
    faceMagicModule (R := R) n →ₗ[R] R × (Fin n → R) × R := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  exact
    { toFun := fun f => (f.1 ∅, (fun i => f.1 {i}),
        f.1 ∅ + f.1 {i₀} + f.1 {i₁} + f.1 {i₀, i₁})
      map_add' := by
        intro f g
        ext <;> simp [Submodule.coe_add, Pi.add_apply, add_assoc, add_comm, add_left_comm]
      map_smul' := by
        intro r f
        ext <;> simp [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_add]
        <;> noncomm_ring }

private def reconstructionMap {n : ℕ} :
    (R × (Fin n → R) × R) →ₗ[R] faceMagicModule (R := R) n :=
  { toFun := fun x =>
      ⟨signedFormula x.1 x.2.1 x.2.2, by
        change FaceMagic n (signedFormula x.1 x.2.1 x.2.2)
        exact signedFormula_faceMagic n x.1 x.2.2 x.2.1⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      funext S
      simp [signedFormula, Finset.sum_add_distrib, mul_add, mul_sub]
      noncomm_ring
    map_smul' := by
      intro r x
      apply Subtype.ext
      funext S
      change signedFormula (r * x.1) (fun i => r * x.2.1 i) (r * x.2.2) S =
        r * signedFormula x.1 x.2.1 x.2.2 S
      unfold signedFormula
      have hsum : (∑ i ∈ S, r * x.2.1 i) = r * (∑ i ∈ S, x.2.1 i) := by
        rw [Finset.mul_sum]
      by_cases hp : Even S.card
      · obtain ⟨q, hq⟩ := hp
        have hpowq : (-1 : R) ^ q * (-1 : R) ^ q = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]
          norm_num
        have hdiv0 : (q + q) / 2 = q := by omega
        have hq_a : (q : R) * (r * x.1) = r * ((q : R) * x.1) := by
          rw [← mul_assoc, Nat.cast_comm, mul_assoc]
        have hq_c : (q : R) * (r * x.2.2) = r * ((q : R) * x.2.2) := by
          rw [← mul_assoc, Nat.cast_comm, mul_assoc]
        rw [hq, hdiv0]
        simp [hsum, hpowq, pow_succ, pow_add, hq_a, hq_c,
          sub_mul, add_mul, mul_sub, mul_add, Nat.cast_comm]
      · obtain ⟨q, hq⟩ := Nat.not_even_iff_odd.mp hp
        have hpowq : (-1 : R) ^ (2 * q) * (-1 : R) = -1 := by
          rw [pow_mul]
          norm_num
        have hdiv1 : (2 * q + 1) / 2 = q := by omega
        have hq_a : (q : R) * (r * x.1) = r * ((q : R) * x.1) := by
          rw [← mul_assoc, Nat.cast_comm, mul_assoc]
        have hq_c : (q : R) * (r * x.2.2) = r * ((q : R) * x.2.2) := by
          rw [← mul_assoc, Nat.cast_comm, mul_assoc]
        have htwo : ∀ y : R, (2 : R) * y = y * 2 := by
          intro y
          exact Nat.cast_comm 2 y
        have h2q_a : (2 : R) * (q : R) * (r * x.1) =
            r * ((2 : R) * (q : R) * x.1) := by
          calc
            (2 : R) * (q : R) * (r * x.1) =
                (2 : R) * ((q : R) * (r * x.1)) := by rw [mul_assoc]
            _ = (2 : R) * (r * ((q : R) * x.1)) := by rw [hq_a]
            _ = r * ((2 : R) * ((q : R) * x.1)) := by
              rw [← mul_assoc, htwo, mul_assoc]
            _ = r * ((2 : R) * (q : R) * x.1) := by rw [mul_assoc]
        rw [hq, hdiv1]
        simp [hsum, hpowq, pow_succ, pow_add, hq_a, hq_c]
        rw [h2q_a]
        noncomm_ring }

private noncomputable def faceMagicEquiv_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    faceMagicModule (R := R) n ≃ₗ[R] R × (Fin n → R) × R := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hi01 : i₀ ≠ i₁ := by
    intro h
    have hv := congrArg Fin.val h
    simp [i₀, i₁] at hv
  let L := coordinateMap (R := R) hn
  let M := reconstructionMap (R := R) (n := n)
  apply LinearEquiv.ofBijective L
  constructor
  · intro f g hfg
    apply Subtype.ext
    funext S
    apply determined_by_two_faces
      (C := (L f).2.2) (D := (L g).2.2) ?_ ?_ ?_ ?_ ?_
      S.card S rfl
    · obtain ⟨C, hC⟩ := f.2
      intro S i j hi hj hij
      have hs := hC S i j hi hj hij
      have hcoord : (L f).2.2 = C := by
        dsimp [L, coordinateMap, i₀, i₁]
        simpa using hC ∅ i₀ i₁ (by simp) (by simp) hi01
      simpa [hcoord] using hs
    · obtain ⟨C, hC⟩ := g.2
      intro S i j hi hj hij
      have hs := hC S i j hi hj hij
      have hcoord : (L g).2.2 = C := by
        dsimp [L, coordinateMap, i₀, i₁]
        simpa using hC ∅ i₀ i₁ (by simp) (by simp) hi01
      simpa [hcoord] using hs
    · exact congrArg (fun z => z.2.2) hfg
    · exact congrArg Prod.fst hfg
    · intro i
      exact congrFun (congrArg (fun z => z.2.1) hfg) i
  · intro x
    refine ⟨M x, ?_⟩
    apply Prod.ext
    · simp [L, M, coordinateMap, reconstructionMap, signedFormula_empty]
    apply Prod.ext
    · funext i
      simp [L, M, coordinateMap, reconstructionMap, signedFormula_singleton]
    · simp [L, M, coordinateMap, reconstructionMap]
      exact signedFormula_face x.1 x.2.2 x.2.1 ∅ i₀ i₁ (by simp) (by simp) hi01

private def emptyEval : faceMagicModule (R := R) 0 →ₗ[R] R :=
  { toFun := fun f => f.1 ∅
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

private def emptyConst : R →ₗ[R] faceMagicModule (R := R) 0 :=
  { toFun := fun a => ⟨fun _ => a, by
      refine ⟨0, ?_⟩
      intro S i j hi hj hij
      exact Fin.elim0 i⟩
    map_add' := by intros; apply Subtype.ext; rfl
    map_smul' := by intros; apply Subtype.ext; rfl }

private noncomputable def faceMagicEquiv_zero :
    faceMagicModule (R := R) 0 ≃ₗ[R] R := by
  apply LinearEquiv.ofBijective (emptyEval (R := R))
  constructor
  · intro f g h
    change f.1 ∅ = g.1 ∅ at h
    apply Subtype.ext
    funext S
    have hS : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact Fin.elim0 i
    change f.1 S = g.1 S
    rw [hS]
    exact h
  · intro a
    exact ⟨emptyConst a, rfl⟩

private def pairEval : faceMagicModule (R := R) 1 →ₗ[R] R × R :=
  { toFun := fun f => (f.1 ∅, f.1 {(0 : Fin 1)})
    map_add' := by intros; ext <;> rfl
    map_smul' := by intros; ext <;> rfl }

private def pairConst : (R × R) →ₗ[R] faceMagicModule (R := R) 1 :=
  { toFun := fun x => ⟨fun S => if S = ∅ then x.1 else x.2, by
      refine ⟨0, ?_⟩
      intro S i j hi hj hij
      have heq : i = j := (Fin.eq_zero i).trans (Fin.eq_zero j).symm
      exact (hij heq).elim⟩
    map_add' := by intros; apply Subtype.ext; funext S; by_cases hS : S = ∅ <;> simp [hS]
    map_smul' := by intros; apply Subtype.ext; funext S; by_cases hS : S = ∅ <;> simp [hS] }

private noncomputable def faceMagicEquiv_one :
    faceMagicModule (R := R) 1 ≃ₗ[R] R × R := by
  apply LinearEquiv.ofBijective (pairEval (R := R))
  constructor
  · intro f g h
    change (f.1 ∅, f.1 {(0 : Fin 1)}) = (g.1 ∅, g.1 {(0 : Fin 1)}) at h
    apply Subtype.ext
    funext S
    by_cases hS : S = ∅
    · change f.1 S = g.1 S
      rw [hS]
      exact congrArg Prod.fst h
    · have hsub : S ⊆ ({(0 : Fin 1)} : Finset (Fin 1)) := by
        intro i hi
        simp only [Finset.mem_singleton]
        exact Fin.eq_zero i
      have hcard : S.card = 1 := by
        apply Finset.card_eq_one.mpr
        have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
        obtain ⟨i, hi⟩ := hnonempty
        have hi0 : i = (0 : Fin 1) := Fin.eq_zero i
        exact ⟨0, Finset.Subset.antisymm hsub (by simpa [hi0] using hi)⟩
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
      have hi0 : i = (0 : Fin 1) := Fin.eq_zero i
      rw [hi, hi0]
      exact congrArg Prod.snd h
  · intro x
    exact ⟨pairConst x, by rfl⟩

/-- Complete all-ring classification of unrestricted face-magic hypercubes.

For every ring, dimension zero gives one coordinate, dimension one gives two,
and the common face sum. -/
theorem face_magic_module_structure :
    Nonempty (faceMagicModule (R := R) 0 ≃ₗ[R] R) ∧
      Nonempty (faceMagicModule (R := R) 1 ≃ₗ[R] R × R) ∧
      ∀ n : ℕ, 2 ≤ n → Nonempty (faceMagicModule (R := R) n ≃ₗ[R] R × (Fin n → R) × R) := by
  exact ⟨⟨faceMagicEquiv_zero (R := R)⟩,
    ⟨⟨faceMagicEquiv_one (R := R)⟩,
      fun n hn => ⟨faceMagicEquiv_of_two_le (R := R) hn⟩⟩⟩

end D5.S3.Combinatorics.Graph.Hypercube.FaceMagicModule
