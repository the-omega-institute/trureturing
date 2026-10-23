/- GID: D5/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SpiderPowerZeroForcing
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.ToLin]
   utility: none
   digest: Ordinary zero forcing on powers of equal-legged spiders. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Nat.Dist

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.SpiderPowerZeroForcing

open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
open Matrix Module

abbrev Vertex (m ell : ℕ) := Option (Fin m × Fin ell)

/-- The center has depth zero; a leg index `i` has depth `i+1`. -/
def distance {m ell : ℕ} : Vertex m ell → Vertex m ell → ℕ
  | none, none => 0
  | none, some p => p.2.val + 1
  | some p, none => p.2.val + 1
  | some p, some q =>
      if p.1 = q.1 then Nat.dist p.2.val q.2.val else p.2.val + q.2.val + 2

/-- Distinct vertices at tree distance at most `k` are adjacent. -/
def power (m k ell : ℕ) : SimpleGraph (Vertex m ell) where
  Adj u v := u ≠ v ∧ distance u v ≤ k
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    have hd : distance v u = distance u v := by
      cases u with
      | none => cases v <;> rfl
      | some p =>
        cases v with
        | none => rfl
        | some q =>
          by_cases he : p.1 = q.1
          · simp only [distance, if_pos he, if_pos he.symm]
            exact Nat.dist_comm _ _
          · simp only [distance, if_neg he, if_neg (Ne.symm he)]
            omega
    simpa [hd] using h.2⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

private def tail (m k ell : ℕ) : Finset (Vertex m ell) := (((Finset.univ.filter fun a : Fin m => a.val < m-1).product
    (Finset.univ.filter fun i : Fin ell => ell-k ≤ i.val)).image Option.some)

private theorem tail_mem {m k ell : ℕ} (a : Fin m) (i : Fin ell) :
    some (a,i) ∈ tail m k ell ↔ a.val < m-1 ∧ ell-k ≤ i.val := by
  simp [tail]

private theorem tail_card (m k ell : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) (hl : k+1 ≤ ell) : (tail m k ell).card = (m-1)*k := by
  have ha : m-1 < m := by omega
  have hi : ell-k < ell := by omega
  have hA : (Finset.univ.filter fun a : Fin m => a.val < m-1) =
      Finset.Iio (⟨m-1,ha⟩ : Fin m)  := by ext a; simp [Fin.lt_def]
  have hI : (Finset.univ.filter fun i : Fin ell => ell-k ≤ i.val) =
      Finset.Ici (⟨ell-k,hi⟩ : Fin ell)  := by ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
  rw [tail, Finset.card_image_of_injective _ (Option.some_injective _), hA, hI]
  rw [show ((Finset.Iio (⟨m-1,ha⟩ : Fin m)).product (Finset.Ici (⟨ell-k,hi⟩ : Fin ell))).card =
      (Finset.Iio (⟨m-1,ha⟩ : Fin m)).card *
      (Finset.Ici (⟨ell-k,hi⟩ : Fin ell)).card from Finset.card_product _ _]
  simp only [Fin.card_Iio, Fin.card_Ici]; congr 1; omega

private theorem tail_leg_black (m k ell : ℕ) (hk : 1 ≤ k) (hl : k+1 ≤ ell)
    (a : Fin m) (ha : a.val < m-1) (i : Fin ell) :
    Black (power m k ell) (tail m k ell : Set (Vertex m ell)) (some (a,i)) := by
  have go : ∀ d : ℕ, ∀ j : Fin ell, ell-j.val ≤ d →
      Black (power m k ell) (tail m k ell : Set (Vertex m ell)) (some (a,j)) := by
    intro d
    induction d with
    | zero => intro j hj; have := j.isLt; omega
    | succ d ih =>
      intro j hj
      by_cases ht : ell-k ≤ j.val
      · exact .init ((tail_mem a j).2 ⟨ha,ht⟩)
      · have hs : j.val+k < ell := by omega
        let s : Fin ell := ⟨j.val+k,hs⟩
        apply Black.force (u := some (a,s)) (ih s (by dsimp [s]; omega))
        · constructor
          · intro h; have h' := congrArg (fun v : Vertex m ell => v.map fun p => p.2.val) h
            simp only [Option.map_some, Option.some.injEq] at h'; dsimp [s] at h'; omega
          · simp only [power, distance, if_pos rfl, Nat.dist]
            dsimp [s]; omega
        · intro x hx hxj
          have hd := hx.2
          cases x with
          | none => simp only [power, distance] at hd; dsimp [s] at hd; omega
          | some p =>
            rcases p with ⟨b,q⟩
            by_cases hab : a = b
            · subst b
              have hq : q.val ≠ j.val := by
                intro he; apply hxj; congr 2; exact Fin.ext he
              simp only [power, distance, if_pos rfl, Nat.dist] at hd; apply ih q; dsimp [s] at hd; omega
            · simp only [power, distance, if_neg hab] at hd
              dsimp [s] at hd; omega
  exact go ell i (by omega)

private theorem tail_forces (m k ell : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hl : k+1 ≤ ell) : IsZeroForcing (power m k ell) (tail m k ell : Set _) := by
  let a : Fin m := ⟨0,by omega⟩
  let z : Fin m := ⟨m-1,by omega⟩
  have ha : a.val < m-1 := by dsimp [a]; omega
  have hlegs := tail_leg_black m k ell hk hl
  have hc : Black (power m k ell) (tail m k ell : Set _) none := by
    let s : Fin ell := ⟨k-1,by omega⟩
    apply Black.force (u := some (a,s)) (hlegs a ha s)
    · constructor
      · simp
      · simp only [power, distance]; dsimp [s]; omega
    · intro x hx hxnone
      have hd := hx.2
      cases x with
      | none => exact (hxnone rfl).elim
      | some p =>
        rcases p with ⟨b,j⟩
        by_cases hab : a = b
        · subst b; exact hlegs a ha j
        · simp only [power, distance, if_neg hab] at hd
          dsimp [s] at hd; omega
  have hlast : ∀ i : Fin ell, Black (power m k ell) (tail m k ell : Set _) (some (z,i)) := by
    intro i
    have go : ∀ t : ℕ, ∀ j : Fin ell, j.val < t → Black (power m k ell) (tail m k ell : Set _) (some (z,j)) := by
      intro t
      induction t with
      | zero => intro j hj; omega
      | succ t ih =>
        intro j hj
        by_cases hjt : j.val < t
        · exact ih j hjt
        · have hjval : j.val = t := by omega
          by_cases hsmall : t+1 < k
          · let s : Fin ell := ⟨k-t-2,by omega⟩
            have haz : a ≠ z := by intro h; have := congrArg Fin.val h; dsimp [a,z] at this; omega
            apply Black.force (u := some (a,s)) (hlegs a ha s)
            · constructor
              · intro h; apply haz; exact congrArg Prod.fst (Option.some.inj h)
              · simp only [power, distance, if_neg haz]; dsimp [s]; omega
            · intro x hx hxj
              cases x with
              | none => exact hc
              | some p =>
                rcases p with ⟨b,q⟩
                by_cases hb : b.val < m-1
                · exact hlegs b hb q
                · have hbz : b = z := Fin.ext (by dsimp [z]; have := b.isLt; omega)
                  subst b
                  have hq : q.val ≠ j.val := by intro h; apply hxj; congr 2; exact Fin.ext h
                  have hd := hx.2; simp only [power, distance, if_neg haz] at hd; apply ih q; dsimp [s] at hd; omega
          · by_cases heq : t+1 = k
            · apply Black.force (u := none) hc
              · constructor
                · simp
                · simp only [power, distance]; omega
              · intro x hx hxj
                cases x with
                | none => exact hc
                | some p =>
                  rcases p with ⟨b,q⟩
                  by_cases hb : b.val < m-1
                  · exact hlegs b hb q
                  · have hbz : b = z := Fin.ext (by dsimp [z]; have := b.isLt; omega)
                    subst b
                    have hq : q.val ≠ j.val := by intro h; apply hxj; congr 2; exact Fin.ext h
                    have hd := hx.2; simp only [power, distance] at hd
                    exact ih q (by omega)
            · have hbig : k ≤ t := by omega
              let s : Fin ell := ⟨t-k,by have := j.isLt; omega⟩
              apply Black.force (u := some (z,s)) (ih s (by dsimp [s]; omega))
              · constructor
                · intro h
                  have h' := congrArg (fun v : Vertex m ell => v.map fun p => p.2.val) h
                  simp only [Option.map_some, Option.some.injEq] at h'; dsimp [s] at h'; omega
                · simp only [power, distance, if_pos rfl, Nat.dist]; dsimp [s]; omega
              · intro x hx hxj
                cases x with
                | none => exact hc
                | some p =>
                  rcases p with ⟨b,q⟩
                  by_cases hb : b.val < m-1
                  · exact hlegs b hb q
                  · have hbz : b = z := Fin.ext (by dsimp [z]; have := b.isLt; omega)
                    subst b
                    have hq : q.val ≠ j.val := by intro h; apply hxj; congr 2; exact Fin.ext h
                    have hd := hx.2; simp only [power, distance, if_pos rfl, Nat.dist] at hd; apply ih q
                    dsimp [s] at hd; omega
    exact go (i.val+1) i (by omega)
  intro v
  cases v with
  | none => exact hc
  | some p =>
    rcases p with ⟨b,i⟩
    by_cases hb : b.val < m-1
    · exact hlegs b hb i
    · have hbz : b = z := Fin.ext (by dsimp [z]; have := b.isLt; omega)
      subst b; exact hlast i

private theorem kernel_zero_of_forcing {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (M : Matrix V V ℚ)
    (hsupport : ∀ u v, u ≠ v → (M u v ≠ 0 ↔ G.Adj u v)) (S : Set V) (hS : IsZeroForcing G S) (x : V → ℚ)
    (hx : M *ᵥ x = 0) (hinit : ∀ v ∈ S, x v = 0) : x = 0 := by
  have go : ∀ v, Black G S v → x v = 0 := by
    intro v hv
    induction hv with
    | init h => exact hinit _ h
    | @force u w hu huw hall ihu ihall =>
      have hsum : (∑ v, M u v * x v) = M u w * x w := by
        apply Finset.sum_eq_single w
        · intro v _ hvw
          by_cases hvu : v = u
          · subst v; rw [ihu, mul_zero]
          · by_cases huv : G.Adj u v
            · rw [ihall v huv hvw, mul_zero]
            · have hm : M u v = 0 := by
                by_contra hm
                exact huv ((hsupport u v (Ne.symm hvu)).1 hm)
              rw [hm, zero_mul]
        · simp
      have hrow : (∑ v, M u v * x v) = 0 := congrFun hx u; have hmw : M u w ≠ 0 := (hsupport u w huw.ne).2 huw
      exact (mul_eq_zero.mp (hsum.symm.trans hrow)).resolve_left hmw
  funext v; exact go v (hS v)

private theorem kernel_finrank_le_forcing {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (M : Matrix V V ℚ)
    (hsupport : ∀ u v, u ≠ v → (M u v ≠ 0 ↔ G.Adj u v)) (S : Finset V) (hS : IsZeroForcing G (S : Set V)) :
    finrank ℚ (LinearMap.ker M.mulVecLin) ≤ S.card := by
  let rho : LinearMap.ker M.mulVecLin →ₗ[ℚ] (S → ℚ) :=
    { toFun := fun x v => x.val v.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective rho := by
    intro x y h
    have hz : (x-y).val = 0 := kernel_zero_of_forcing G M hsupport (S : Set V) hS
      (x-y).val (x-y).property (by
        intro v hv; apply sub_eq_zero.mpr
        exact congrFun h ⟨v,hv⟩)
    apply Subtype.ext; exact sub_eq_zero.mp hz
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi, Fintype.card_coe] using hd

private def up (n : ℕ) : Matrix (Fin (n+1)) (Fin n) ℚ := fun i a =>
  (if i = a.castSucc then ((n:ℚ)-a.val) else 0) +
  (if i = a.succ then ((a.val:ℚ)+1) else 0)

private def down (n : ℕ) : Matrix (Fin n) (Fin (n+1)) ℚ := fun a i =>
  (if i = a.castSucc then 1 else 0) + (if i = a.succ then 1 else 0)

private def leg (n : ℕ) : Matrix (Fin n) (Fin n) ℚ := fun i j =>
  (if i = j then ((n:ℚ)-1) else 0) +
  (if j.val = i.val+1 then ((n:ℚ)-1-i.val) else 0) +
  (if i.val = j.val+1 then ((j.val:ℚ)+1) else 0)

private theorem up_mul_apply {J : Type*} (n : ℕ) (M : Matrix (Fin n) J ℚ) (i : Fin (n+1)) (j : J) : (up n * M) i j =
      (if h : i.val < n then ((n:ℚ)-i.val) * M ⟨i.val,h⟩ j else 0) +
      (if h : 0 < i.val then (i.val:ℚ) * M ⟨i.val-1,by omega⟩ j else 0) := by
  simp only [Matrix.mul_apply, up, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]; congr 1
  · by_cases hi : i.val < n
    · rw [dif_pos hi]
      let a : Fin n := ⟨i.val,hi⟩
      have hei : i = a.castSucc := Fin.ext rfl; rw [Finset.sum_eq_single a]
      · simp only [hei, if_true]; rfl
      · intro b _ hba
        have hne : i ≠ b.castSucc := by
          intro h; apply hba; apply Fin.ext; have := congrArg Fin.val h; simpa [a] using this.symm
        rw [if_neg hne]
      · simp
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero; intro a _
      have hne : i ≠ a.castSucc := by
        intro h; have := congrArg Fin.val h; have := a.isLt; simp only [Fin.val_castSucc] at *; omega
      rw [if_neg hne]
  · by_cases hi : 0 < i.val
    · rw [dif_pos hi]
      let a : Fin n := ⟨i.val-1,by omega⟩
      have hei : i = a.succ := Fin.ext (by dsimp [a]; omega)
      rw [Finset.sum_eq_single a]
      · simp only [hei, if_true, Fin.val_succ]
        dsimp [a]; push_cast; ring
      · intro b _ hba
        have hne : i ≠ b.succ := by
          intro h; apply hba; apply Fin.ext; have := congrArg Fin.val h; dsimp [a]; simp only [Fin.val_succ] at this
          omega
        rw [if_neg hne]
      · simp
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero; intro a _
      have hne : i ≠ a.succ := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_succ] at this; omega
      rw [if_neg hne]

private theorem up_down (n : ℕ) : up n * down n = leg (n+1) := by
  ext i j
  rw [up_mul_apply]; simp only [down, leg]
  split_ifs <;> simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
  all_goals try { exfalso; omega }
  all_goals push_cast
  all_goals try ring
  all_goals norm_cast
  all_goals try simp only [Int.subNatNat_eq_coe]
  all_goals omega

private theorem down_up (n : ℕ) : down n * up n = leg n + (2:ℚ) • 1 := by
  ext a b
  simp only [Matrix.mul_apply, down, add_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [up, leg, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
  all_goals try { exfalso; omega }
  all_goals push_cast
  all_goals try ring
  all_goals norm_cast
  all_goals try simp only [Int.subNatNat_eq_coe]
  all_goals omega

private def product {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [Ring R] (A : Matrix V V R) : ℕ → Matrix V V R
  | 0 => 1
  | r+1 => (A - (2*r:R) • 1) * product A r

private theorem leg_mul_up (n : ℕ) : leg (n+1) * up n = up n * leg n + (2:ℚ) • up n := by
  rw [← up_down n, Matrix.mul_assoc, down_up, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]

private theorem shift_mul_up (n r : ℕ) : (leg (n+1) - (2*(r+1):ℚ) • 1) * up n = up n * (leg n - (2*r:ℚ) • 1) := by
  rw [Matrix.sub_mul, leg_mul_up, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  have hs : (2*(r+1):ℚ) = 2*r+2 := by ring
  rw [hs, add_smul]; abel

private theorem product_leg_rung (n r : ℕ) : product (leg (n+1)) (r+1) = up n * product (leg n) r * down n := by
  induction r with
  | zero => simp [product, up_down]
  | succ r ih =>
    rw [product, ih]; simp only [Nat.cast_add, Nat.cast_one]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, shift_mul_up]
    simp only [product, Nat.cast_add, Nat.cast_one, Matrix.mul_assoc]

private def raising (n : ℕ) : (r : ℕ) → Matrix (Fin (n+r)) (Fin n) ℚ
  | 0 => 1
  | r+1 => up (n+r) * raising n r

private def lowering (n : ℕ) : (r : ℕ) → Matrix (Fin n) (Fin (n+r)) ℚ
  | 0 => 1
  | r+1 => lowering n r * down (n+r)

private theorem product_leg_factors (n r : ℕ) : product (leg (n+r)) r = raising n r * lowering n r := by
  induction r with
  | zero => simp [product, raising, lowering]
  | succ r ih =>
    change product (leg ((n+r)+1)) (r+1) = _; rw [product_leg_rung, ih]; simp only [raising, lowering, Matrix.mul_assoc]

private theorem lowering_kernel_dimension (n r : ℕ) : r ≤ finrank ℚ (LinearMap.ker (lowering n r).mulVecLin) := by
  have hd := (lowering n r).mulVecLin.finrank_range_add_finrank_ker
  have hr := (LinearMap.range (lowering n r).mulVecLin).finrank_le; simp only [Module.finrank_fin_fun] at hd hr; omega

private theorem product_leg_kernel_dimension (n r : ℕ) :
    r ≤ finrank ℚ (LinearMap.ker (product (leg (n+r)) r).mulVecLin) := by
  have hsub : LinearMap.ker (lowering n r).mulVecLin ≤
      LinearMap.ker (product (leg (n+r)) r).mulVecLin := by
    intro x hx; rw [product_leg_factors, Matrix.mulVecLin_mul, LinearMap.mem_ker, LinearMap.comp_apply]
    rw [LinearMap.mem_ker] at hx; rw [hx, map_zero]
  exact (lowering_kernel_dimension n r).trans
    (LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hsub))

private theorem up_nonneg (n : ℕ) (i : Fin (n+1)) (a : Fin n) : 0 ≤ up n i a := by
  unfold up
  have h : (a.val:ℚ) < n := by exact_mod_cast a.isLt
  split_ifs <;> positivity

private theorem up_positive (n : ℕ) (i : Fin (n+1)) (a : Fin n) : 0 < up n i a ↔ i.val = a.val ∨ i.val = a.val+1 := by
  unfold up
  have h : (a.val:ℚ) < n := by exact_mod_cast a.isLt
  simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> linarith

private theorem down_nonneg (n : ℕ) (a : Fin n) (i : Fin (n+1)) : 0 ≤ down n a i := by
  unfold down
  split_ifs <;> norm_num

private theorem down_positive (n : ℕ) (a : Fin n) (i : Fin (n+1)) :
    0 < down n a i ↔ i.val = a.val ∨ i.val = a.val+1 := by
  unfold down; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> norm_num <;> tauto

private theorem mul_nonneg {I J K : Type*} [Fintype J] (A : Matrix I J ℚ) (B : Matrix J K ℚ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ j k, 0 ≤ B j k) (i : I) (k : K) : 0 ≤ (A*B) i k := by
  exact Finset.sum_nonneg fun j _ => _root_.mul_nonneg (hA i j) (hB j k)

private theorem mul_positive {I J K : Type*} [Fintype J] (A : Matrix I J ℚ) (B : Matrix J K ℚ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ j k, 0 ≤ B j k) (i : I) (k : K) : 0 < (A*B) i k ↔ ∃ j, 0 < A i j ∧ 0 < B j k := by
  rw [Matrix.mul_apply, Finset.sum_pos_iff_of_nonneg (fun j _ => _root_.mul_nonneg (hA i j) (hB j k))]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j,hj⟩
    rcases mul_pos_iff.mp hj with hp | hn
    · exact ⟨j,hp⟩
    · have hh := hA i j; linarith [hn.1]
  · rintro ⟨j,hj,hk⟩
    exact ⟨j,mul_pos hj hk⟩

private theorem raising_nonneg (n r : ℕ) (i : Fin (n+r)) (a : Fin n) : 0 ≤ raising n r i a := by
  induction r generalizing a with
  | zero => simp only [raising, Matrix.one_apply]; split_ifs <;> norm_num
  | succ r ih => exact mul_nonneg _ _ (up_nonneg _) (fun i a => ih i a) i a

private theorem lowering_nonneg (n r : ℕ) (a : Fin n) (i : Fin (n+r)) : 0 ≤ lowering n r a i := by
  induction r generalizing a with
  | zero => simp only [lowering, Matrix.one_apply]; split_ifs <;> norm_num
  | succ r ih => exact mul_nonneg _ _ (fun a i => ih a i) (down_nonneg _) a i

private theorem raising_positive (n r : ℕ) (i : Fin (n+r)) (a : Fin n) :
    0 < raising n r i a ↔ a.val ≤ i.val ∧ i.val ≤ a.val+r := by
  induction r generalizing a with
  | zero => simp only [raising, Matrix.one_apply, Fin.ext_iff]; split_ifs <;> simp_all <;> omega
  | succ r ih =>
    rw [raising, mul_positive _ _ (up_nonneg _) (raising_nonneg n r)]; simp only [up_positive, ih]
    constructor
    · rintro ⟨b,hb,hba⟩; rcases hb with hb | hb <;> omega
    · rintro ⟨hai,hia⟩
      by_cases hi : i.val ≤ a.val+r
      · have hin : i.val < n+r := by have := a.isLt; omega
        exact ⟨⟨i.val,hin⟩,Or.inl rfl,hai,hi⟩
      · have hip : 0 < i.val := by omega
        have hin : i.val-1 < n+r := by have := i.isLt; omega
        exact ⟨⟨i.val-1,hin⟩,Or.inr (by dsimp; omega),by dsimp; omega,by dsimp; omega⟩

private theorem lowering_positive (n r : ℕ) (a : Fin n) (i : Fin (n+r)) :
    0 < lowering n r a i ↔ a.val ≤ i.val ∧ i.val ≤ a.val+r := by
  induction r generalizing a with
  | zero => simp only [lowering, Matrix.one_apply, Fin.ext_iff]; split_ifs <;> simp_all <;> omega
  | succ r ih =>
    rw [lowering, mul_positive _ _ (lowering_nonneg n r) (down_nonneg _)]; simp only [down_positive, ih]
    constructor
    · rintro ⟨b,hba,hb⟩; rcases hb with hb | hb <;> omega
    · rintro ⟨hai,hia⟩
      by_cases hi : i.val ≤ a.val+r
      · have hin : i.val < n+r := by have := a.isLt; omega
        exact ⟨⟨i.val,hin⟩,⟨hai,hi⟩,Or.inl rfl⟩
      · have hin : i.val-1 < n+r := by have := i.isLt; omega
        exact ⟨⟨i.val-1,hin⟩,⟨by dsimp; omega,by dsimp; omega⟩,Or.inr (by dsimp; omega)⟩

private theorem product_leg_nonneg (n r : ℕ) (i j : Fin (n+r)) : 0 ≤ product (leg (n+r)) r i j := by
  rw [product_leg_factors]; exact mul_nonneg _ _ (raising_nonneg n r) (lowering_nonneg n r) i j

private theorem product_leg_positive (n r : ℕ) (hn : 1 ≤ n) (i j : Fin (n+r)) :
    0 < product (leg (n+r)) r i j ↔ Nat.dist i.val j.val ≤ r := by
  rw [product_leg_factors, mul_positive _ _ (raising_nonneg n r) (lowering_nonneg n r)]
  simp only [raising_positive, lowering_positive]
  constructor
  · rintro ⟨a,hi,hj⟩; unfold Nat.dist; omega
  · intro hd
    let a : ℕ := max i.val j.val - r
    have ha : a < n := by dsimp [a]; have := i.isLt; have := j.isLt; omega
    refine ⟨⟨a,ha⟩,?_,?_⟩ <;> dsimp [a] <;> unfold Nat.dist at hd <;> omega

private def spiderMatrix (m ell : ℕ) (t : ℚ) : Matrix (Vertex m ell) (Vertex m ell) ℚ
  | none, none => t
  | none, some p => if p.2.val = 0 then 1 else 0
  | some p, none => if p.2.val = 0 then 1 else 0
  | some p, some q => if p.1 = q.1 then leg ell p.2 q.2 else 0

private def assemble (m ell : ℕ) : (Fin m → Fin ell → ℚ) →ₗ[ℚ] (Vertex m ell → ℚ) where
  toFun x := fun v => match v with | none => 0 | some p => x p.1 p.2
  map_add' := by intros; funext v; cases v <;> simp
  map_smul' := by intros; funext v; cases v <;> simp

private theorem assemble_injective (m ell : ℕ) : Function.Injective (assemble m ell) := by
  intro x y h; funext a i; exact congrFun h (some (a,i))

private theorem matrix_assemble (m ell : ℕ) (he : 1 ≤ ell) (t : ℚ) (x : Fin m → Fin ell → ℚ) (hx : ∑ a, x a = 0) :
    spiderMatrix m ell t *ᵥ assemble m ell x = assemble m ell (fun a => leg ell *ᵥ x a) := by
  funext v
  cases v with
  | none =>
    have hz : (∑ a, x a ⟨0,he⟩) = 0 := by
      have h := congrFun hx ⟨0,he⟩
      simpa only [Finset.sum_apply, Pi.zero_apply] using h
    have hidx (i : Fin ell) : i.val = 0 ↔ i = ⟨0,he⟩ := by simp [Fin.ext_iff]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, Fintype.sum_prod_type,
      spiderMatrix, assemble, LinearMap.coe_mk, AddHom.coe_mk, mul_zero, zero_add,
      ite_mul, one_mul, zero_mul, hidx, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hz
  | some p =>
    rcases p with ⟨a,i⟩
    simp [Matrix.mulVec, dotProduct, Fintype.sum_option, Fintype.sum_prod_type, spiderMatrix, assemble]

private theorem product_assemble (m ell r : ℕ) (he : 1 ≤ ell) (t : ℚ) (x : Fin m → Fin ell → ℚ) (hx : ∑ a, x a = 0) :
    product (spiderMatrix m ell t) r *ᵥ assemble m ell x = assemble m ell (fun a => product (leg ell) r *ᵥ x a) := by
  induction r with
  | zero => simp [product]
  | succ r ih =>
    let y : Fin m → Fin ell → ℚ := fun a => product (leg ell) r *ᵥ x a
    have hy : ∑ a, y a = 0 := by
      change (∑ a, (product (leg ell) r).mulVecLin (x a)) = 0; rw [← map_sum, hx, map_zero]
    rw [product, ← Matrix.mulVec_mulVec, ih, Matrix.sub_mulVec,
      matrix_assemble m ell he t y hy, Matrix.smul_mulVec, Matrix.one_mulVec]
    change assemble m ell (fun a => leg ell *ᵥ y a) - (2*r:ℚ) • assemble m ell y = _; rw [← map_smul, ← map_sub]
    congr 1; funext a
    simp only [product, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, y]

private theorem spider_kernel_dimension (m k ell : ℕ) (hm : 2 ≤ m) (hl : k+1 ≤ ell) (t : ℚ) :
    (m-1)*k ≤ finrank ℚ (LinearMap.ker (product (spiderMatrix m ell t) k).mulVecLin) := by
  let W := LinearMap.ker (product (leg ell) k).mulVecLin
  let sigma : (Fin m → W) →ₗ[ℚ] W := ∑ a : Fin m, LinearMap.proj a
  let U := LinearMap.ker sigma
  have hW : k ≤ finrank ℚ W := by
    have hdim := product_leg_kernel_dimension (ell-k) k
    have he : ell-k+k = ell := by omega
    rw [he] at hdim; exact hdim
  have hU : (m-1)*k ≤ finrank ℚ U := by
    have hd := sigma.finrank_range_add_finrank_ker; have hr := (LinearMap.range sigma).finrank_le
    simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hd
    change finrank ℚ sigma.range + finrank ℚ sigma.ker = m * finrank ℚ W at hd
    have hmd : (m-1)*finrank ℚ W ≤ finrank ℚ U := by
      have hm1 : m-1+1=m := by omega
      have hp := congrArg (fun z : ℕ => z * finrank ℚ W) hm1; simp only [Nat.add_mul, Nat.one_mul] at hp; dsimp [U]
      omega
    exact (Nat.mul_le_mul_left (m-1) hW).trans hmd
  let f : U →ₗ[ℚ] LinearMap.ker (product (spiderMatrix m ell t) k).mulVecLin :=
    { toFun := fun x => ⟨assemble m ell (fun a => (x.val a).val), by
        have hs : ∑ a, (x.val a).val = 0 := by
          have h := x.property; change sigma x.val = 0 at h; have hh := congrArg (fun w : W => w.val) h
          simp only [sigma, LinearMap.sum_apply, LinearMap.proj_apply, map_sum, map_zero] at hh
          simpa only [Submodule.coe_sum, Submodule.coe_zero] using hh
        rw [LinearMap.mem_ker]; change product (spiderMatrix m ell t) k *ᵥ assemble m ell (fun a => (x.val a).val) = 0
        rw [product_assemble m ell k (by omega) t _ hs]
        have he : (fun a => product (leg ell) k *ᵥ (x.val a).val) = 0 := by
          funext a; exact (x.val a).property
        rw [he, map_zero]⟩
      map_add' := by intros; apply Subtype.ext; exact map_add (assemble m ell) _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul (assemble m ell) _ _ }
  have hinj : Function.Injective f := by
    intro x y h; apply Subtype.ext; funext a; apply Subtype.ext; have hh := congrArg (fun w => w.val) h
    have hhh := assemble_injective m ell hh; exact congrFun hhh a
  exact hU.trans (LinearMap.finrank_le_finrank_of_injective hinj)

private theorem simultaneous_natural_parameter {I : Type*} [Fintype I] (p : I → Polynomial ℚ) (hp : ∀ i, p i ≠ 0) :
    ∃ t : ℕ, ∀ i, (p i).eval (t:ℚ) ≠ 0 := by
  classical
  let q : Polynomial ℚ := ∏ i, p i
  have hq : q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hex : ∃ t : ℕ, q.eval (t:ℚ) ≠ 0 := by
    by_contra! h
    apply hq
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q
      (f := fun i : Fin (q.natDegree+1) => (i.val:ℚ))
    · intro i j hij
      apply Fin.ext; have hcast : (i.val:ℚ) = (j.val:ℚ) := hij
      exact_mod_cast hcast
    · intro i; exact h i.val
    · simp
  obtain ⟨t,ht⟩ := hex
  refine ⟨t,?_⟩
  have hprod : (∏ i, (p i).eval (t:ℚ)) ≠ 0 := by simpa only [q, Polynomial.eval_prod] using ht
  exact fun i => Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)

private def centerProjector (m ell : ℕ) : Matrix (Vertex m ell) (Vertex m ell) ℚ :=
  fun u v => if u = none ∧ v = none then 1 else 0

private def polynomialMatrix (m ell : ℕ) : Matrix (Vertex m ell) (Vertex m ell) (Polynomial ℚ) :=
  (spiderMatrix m ell 0).map Polynomial.C + (Polynomial.X : Polynomial ℚ) • (centerProjector m ell).map Polynomial.C

private def legBlock (m ell : ℕ) (B : Matrix (Fin ell) (Fin ell) ℚ) : Matrix (Vertex m ell) (Vertex m ell) ℚ
  | none, _ => 0
  | some _, none => 0
  | some p, some q => if p.1 = q.1 then B p.2 q.2 else 0

private theorem legBlock_mul (m ell : ℕ) (B C : Matrix (Fin ell) (Fin ell) ℚ) :
    legBlock m ell (B*C) = legBlock m ell B * legBlock m ell C := by
  apply Matrix.ext; intro u v
  cases u with
  | none => simp [legBlock, Matrix.mul_apply, Fintype.sum_option]
  | some p =>
    cases v with
    | none => simp [legBlock, Matrix.mul_apply, Fintype.sum_option, Fintype.sum_prod_type]
    | some q =>
      rcases p with ⟨a,i⟩; rcases q with ⟨b,j⟩
      by_cases hab : a = b
      · subst b
        simp [legBlock, Matrix.mul_apply, Fintype.sum_option, Fintype.sum_prod_type, ite_mul, mul_ite]
      · simp [legBlock, Matrix.mul_apply, Fintype.sum_option, Fintype.sum_prod_type, hab, ite_mul, mul_ite]

private theorem legBlock_shift_mul (m ell r : ℕ) (B : Matrix (Fin ell) (Fin ell) ℚ) :
    (legBlock m ell (leg ell) - (2*r:ℚ) • 1) * legBlock m ell B = legBlock m ell ((leg ell - (2*r:ℚ) • 1)*B) := by
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [← legBlock_mul]; apply Matrix.ext; intro u v
  cases u <;> cases v <;> simp [legBlock, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;> split_ifs <;> simp

private def correction (m ell r : ℕ) : Matrix (Vertex m ell) (Vertex m ell) (Polynomial ℚ) :=
  product (polynomialMatrix m ell) r - (legBlock m ell (product (leg ell) r)).map Polynomial.C

private theorem polynomialMatrix_eval (m ell : ℕ) (t : ℚ) :
    (polynomialMatrix m ell).map (Polynomial.eval t) = spiderMatrix m ell t := by
  apply Matrix.ext; intro u v
  cases u <;> cases v <;> simp [polynomialMatrix, spiderMatrix, centerProjector,
    Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    apply_ite (Polynomial.eval t)]

private theorem product_eval (m ell r : ℕ) (t : ℚ) : (product (polynomialMatrix m ell) r).map (Polynomial.eval t) =
      product (spiderMatrix m ell t) r := by
  let f : Matrix (Vertex m ell) (Vertex m ell) (Polynomial ℚ) →+*
      Matrix (Vertex m ell) (Vertex m ell) ℚ := (Polynomial.evalRingHom t).mapMatrix
  change f (product (polynomialMatrix m ell) r) = _
  induction r with
  | zero => simp [product]
  | succ r ih =>
    rw [product, map_mul, ih, product]; congr 1; rw [map_sub]
    have hA : f (polynomialMatrix m ell) = spiderMatrix m ell t := polynomialMatrix_eval m ell t; rw [hA]
    apply Matrix.ext; intro u v
    simp [f, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, apply_ite (Polynomial.eval t)]

private def depth {m ell : ℕ} : Vertex m ell → ℕ
  | none => 0
  | some p => p.2.val+1

private def rationalShift (m ell r : ℕ) : Matrix (Vertex m ell) (Vertex m ell) ℚ := spiderMatrix m ell 0 - (2*r:ℚ) • 1

private theorem legBlock_map_next (m ell r : ℕ) : (legBlock m ell (product (leg ell) (r+1))).map Polynomial.C =
      ((legBlock m ell (leg ell)).map Polynomial.C - (2*r:Polynomial ℚ) • 1) *
      (legBlock m ell (product (leg ell) r)).map Polynomial.C := by
  have h := legBlock_shift_mul m ell r (product (leg ell) r); have hm := congrArg (fun M => M.map Polynomial.C) h
  rw [Matrix.map_mul (f := (Polynomial.C : ℚ →+* Polynomial ℚ))] at hm; rw [product]; rw [← hm]; congr 1
  apply Matrix.ext; intro u v
  simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, apply_ite Polynomial.C, Polynomial.C_ofNat, Polynomial.C_eq_natCast]

private theorem correction_next (m ell r : ℕ) : correction m ell (r+1) = ((rationalShift m ell r).map Polynomial.C +
        (Polynomial.X : Polynomial ℚ) • (centerProjector m ell).map Polynomial.C) * correction m ell r +
      (polynomialMatrix m ell - (legBlock m ell (leg ell)).map Polynomial.C) *
        (legBlock m ell (product (leg ell) r)).map Polynomial.C := by
  have hshift : (rationalShift m ell r).map Polynomial.C +
      (Polynomial.X : Polynomial ℚ) • (centerProjector m ell).map Polynomial.C =
      polynomialMatrix m ell - (2*r:Polynomial ℚ) • 1 := by
    apply Matrix.ext; intro u v
    simp [rationalShift, polynomialMatrix, Matrix.map_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      apply_ite Polynomial.C, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
    ring
  rw [hshift, correction, product, legBlock_map_next, correction]; rw [Matrix.mul_sub, Matrix.sub_mul]
  noncomm_ring

private theorem correction_entry_next (m ell r : ℕ) (he : 1 ≤ ell) (u v : Vertex m ell) : correction m ell (r+1) u v =
      (∑ w, Polynomial.C (rationalShift m ell r u w) * correction m ell r w v) +
      (if u = none then Polynomial.X * correction m ell r none v else 0) + (if u = none then match v with
        | none => 0
        | some p => Polynomial.C (product (leg ell) r ⟨0,he⟩ p.2)
       else 0) := by
  rw [correction_next, Matrix.add_apply, Matrix.add_mul, Matrix.add_apply, Matrix.mul_apply]; congr 1
  · simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, centerProjector]
    cases u <;> simp [ite_mul]
  · cases u with
    | none =>
      cases v with
      | none => simp [Matrix.mul_apply, legBlock, Matrix.map_apply,
          Matrix.sub_apply, Matrix.add_apply, polynomialMatrix, spiderMatrix, centerProjector,
          Matrix.smul_apply, smul_eq_mul]
      | some p =>
        rcases p with ⟨a,i⟩
        have hidx (j : Fin ell) : j.val = 0 ↔ j = ⟨0,he⟩ := by simp [Fin.ext_iff]
        simp [Matrix.mul_apply, legBlock, Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply,
          polynomialMatrix, spiderMatrix, centerProjector, Matrix.smul_apply, smul_eq_mul,
          Fintype.sum_option, Fintype.sum_prod_type, ite_mul, mul_ite, hidx, apply_ite Polynomial.C]
    | some p =>
      cases v <;> simp [Matrix.mul_apply, legBlock, Matrix.map_apply,
        Matrix.sub_apply, Matrix.add_apply, polynomialMatrix, spiderMatrix, centerProjector,
        Matrix.smul_apply, smul_eq_mul, Fintype.sum_option, Fintype.sum_prod_type, ite_mul]

private theorem rationalShift_depth (m ell r : ℕ) (u v : Vertex m ell)
    (h : rationalShift m ell r u v ≠ 0) : depth u ≤ depth v+1 := by
  cases u with
  | none => simp [depth]
  | some p =>
    cases v with
    | none =>
      simp only [rationalShift, Matrix.sub_apply, spiderMatrix, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
      by_cases hi : p.2.val = 0
      · simp [depth,hi]
      · simp [hi] at h
    | some q =>
      rcases p with ⟨a,i⟩; rcases q with ⟨b,j⟩
      by_cases hab : a = b
      · subst b
        by_cases hij : i = j
        · subst j; simp [depth]
        · have hv : i.val ≠ j.val := by intro hh; exact hij (Fin.ext hh)
          simp only [rationalShift, Matrix.sub_apply, spiderMatrix, if_pos rfl,
            leg, if_neg hij, Matrix.smul_apply, Matrix.one_apply,
            Option.some.injEq, Prod.mk.injEq, true_and, if_neg hij, smul_eq_mul,
            mul_zero, sub_zero, zero_add] at h
          by_cases hnext : j.val = i.val+1
          · simp only [depth]; omega
          · by_cases hprev : i.val = j.val+1
            · simp only [depth]; omega
            · simp [hnext,hprev] at h
      · simp [rationalShift, Matrix.sub_apply, spiderMatrix, hab, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h

private theorem product_leg_band (ell r : ℕ) (hr : r < ell) (i j : Fin ell) : 0 ≤ product (leg ell) r i j ∧
      (0 < product (leg ell) r i j ↔ Nat.dist i.val j.val ≤ r) := by
  have he : ell-r+r = ell := by omega
  have h : ∀ i j : Fin (ell-r+r), 0 ≤ product (leg (ell-r+r)) r i j ∧
      (0 < product (leg (ell-r+r)) r i j ↔ Nat.dist i.val j.val ≤ r) :=
    fun i j => ⟨product_leg_nonneg (ell-r) r i j, product_leg_positive (ell-r) r (by omega) i j⟩
  rw [he] at h; exact h i j

private theorem product_leg_zero (ell r : ℕ) (hr : r < ell) (i j : Fin ell)
    (hd : r < Nat.dist i.val j.val) : product (leg ell) r i j = 0 := by
  have h := product_leg_band ell r hr i j
  have hn : ¬ 0 < product (leg ell) r i j := by intro hp; have := h.2.1 hp; omega
  exact le_antisymm (not_lt.mp hn) h.1

private theorem correction_zero (m ell : ℕ) : correction m ell 0 = (centerProjector m ell).map Polynomial.C := by
  apply Matrix.ext; intro u v
  cases u <;> cases v <;>
    simp [correction, product, legBlock, centerProjector, Matrix.one_apply,
      Matrix.sub_apply, Matrix.map_apply, apply_ite Polynomial.C, Prod.ext_iff, ite_and]

private theorem correction_coeff_zero (m ell : ℕ) : ∀ r : ℕ, r < ell → ∀ (u v : Vertex m ell) (s : ℕ),
      r < depth u + depth v + s → (correction m ell r u v).coeff s = 0 := by
  intro r
  induction r with
  | zero =>
    intro hr u v s hs; rw [correction_zero]
    by_cases hu : u = none <;> by_cases hv : v = none
    · subst u; subst v
      have hs0 : s ≠ 0 := by simp only [depth] at hs; omega
      simp [centerProjector, Matrix.map_apply, Polynomial.coeff_one, hs0]
    · simp [centerProjector, Matrix.map_apply, hu, hv]
    · simp [centerProjector, Matrix.map_apply, hu, hv]
    · simp [centerProjector, Matrix.map_apply, hu, hv]
  | succ r ih =>
    intro hr u v s hs
    have he : 1 ≤ ell := by omega
    rw [correction_entry_next m ell r he u v]
    simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
    have hsum : (∑ w, rationalShift m ell r u w * (correction m ell r w v).coeff s) = 0 := by
      apply Finset.sum_eq_zero; intro w _
      by_cases hw : rationalShift m ell r u w = 0
      · rw [hw, zero_mul]
      · have hd := rationalShift_depth m ell r u w hw
        rw [ih (by omega) w v s (by omega), mul_zero]
    rw [hsum, zero_add]
    have hx : (if u = none then Polynomial.X * correction m ell r none v else 0).coeff s = 0 := by
      by_cases hu : u = none
      · subst u; rw [if_pos rfl]
        cases s with
        | zero => exact Polynomial.coeff_X_mul_zero _
        | succ s =>
          rw [Polynomial.coeff_X_mul]
          apply ih (by omega) none v s
          simp only [depth] at hs ⊢; omega
      · rw [if_neg hu, Polynomial.coeff_zero]
    rw [hx, zero_add]
    by_cases hu : u = none
    · subst u; rw [if_pos rfl]
      cases v with
      | none => simp
      | some p =>
        cases s with
        | zero =>
          rw [Polynomial.coeff_C_zero]
          apply product_leg_zero ell r (by omega) ⟨0,he⟩ p.2
          simp only [depth, Nat.dist_zero_left] at hs ⊢; omega
        | succ s => simp
    · rw [if_neg hu, Polynomial.coeff_zero]

private def parent {m ell : ℕ} : Vertex m ell → Vertex m ell
  | none => none
  | some p => if h : p.2.val = 0 then none else some (p.1,⟨p.2.val-1,by omega⟩)

private theorem depth_eq_zero {m ell : ℕ} (u : Vertex m ell) : depth u = 0 ↔ u = none := by cases u <;> simp [depth]

private theorem parent_depth {m ell : ℕ} (u : Vertex m ell) (hu : u ≠ none) : depth (parent u)+1 = depth u := by
  cases u with
  | none => exact (hu rfl).elim
  | some p => simp only [parent]; split_ifs <;> simp [depth] <;> omega

private theorem rationalShift_parent (m ell r : ℕ) (u : Vertex m ell) (hu : u ≠ none) :
    0 < rationalShift m ell r u (parent u) := by
  cases u with
  | none => exact (hu rfl).elim
  | some p =>
    rcases p with ⟨a,i⟩; simp only [parent]
    split_ifs with hi
    · simp [rationalShift, spiderMatrix, hi, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    · have hne : i ≠ (⟨i.val-1,by omega⟩ : Fin ell) := by intro h; have := congrArg Fin.val h; dsimp at this; omega
      have hprev : i.val = (i.val-1)+1 := by omega
      have hnext : ¬ i.val-1 = i.val+1 := by omega
      simp only [rationalShift, spiderMatrix, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, Option.some.injEq, Prod.mk.injEq, true_and, if_pos rfl,
        if_neg hne, smul_eq_mul, mul_zero, sub_zero, leg, Fin.val_mk, hnext,
        if_false, if_pos hprev, zero_add]
      change 0 < ((i.val-1:ℕ):ℚ)+1; positivity

private theorem rationalShift_nonparent_depth (m ell r : ℕ) (u w : Vertex m ell)
    (hu : u ≠ none) (hw : w ≠ parent u) (h : rationalShift m ell r u w ≠ 0) : depth u ≤ depth w := by
  cases u with
  | none => exact (hu rfl).elim
  | some p =>
    rcases p with ⟨a,i⟩
    cases w with
    | none =>
      by_cases hi : i.val = 0
      · simp [parent,hi] at hw
      · simp [rationalShift, spiderMatrix, hi, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
    | some q =>
      rcases q with ⟨b,j⟩
      by_cases hab : a = b
      · subst b
        by_cases hij : i = j
        · subst j; simp [depth]
        · by_cases hnext : j.val = i.val+1
          · simp [depth]; omega
          · by_cases hprev : i.val = j.val+1
            · have hi : i.val ≠ 0 := by omega
              have hp : parent (some (a,i)) = some (a,j) := by
                simp only [parent, dif_neg hi]; congr 2; apply Fin.ext; dsimp; omega
              exact (hw hp.symm).elim
            · simp [rationalShift, spiderMatrix, hij, leg, hnext, hprev,
                Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
      · simp [rationalShift, spiderMatrix, hab, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h

private theorem correction_coeff_positive (m ell : ℕ) : ∀ r : ℕ, r < ell → ∀ (u v : Vertex m ell) (s : ℕ),
      r = depth u + depth v + s → 0 < (correction m ell r u v).coeff s := by
  intro r
  induction r with
  | zero =>
    intro hr u v s hs
    have hu : u = none := (depth_eq_zero u).1 (by omega)
    have hv : v = none := (depth_eq_zero v).1 (by omega)
    have hz : s = 0 := by omega
    subst u; subst v; subst s; rw [correction_zero]
    norm_num [centerProjector, Matrix.map_apply]
  | succ r ih =>
    intro hr u v s hs
    have he : 1 ≤ ell := by omega
    rw [correction_entry_next m ell r he u v]
    simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
    by_cases hu : u = none
    · subst u
      have hsum : (∑ w, rationalShift m ell r none w * (correction m ell r w v).coeff s) = 0 := by
        apply Finset.sum_eq_zero; intro w _
        rw [correction_coeff_zero m ell r (by omega) w v s (by
          simp only [show depth (none : Vertex m ell) = 0 from rfl, zero_add] at hs
          omega), mul_zero]
      rw [hsum, zero_add, if_pos rfl, if_pos rfl]
      cases s with
      | zero =>
        rw [Polynomial.coeff_X_mul_zero, zero_add]
        cases v with
        | none => simp only [depth] at hs; omega
        | some p =>
          rw [Polynomial.coeff_C_zero]
          have hb := (product_leg_band ell r (by omega) ⟨0,he⟩ p.2).2
          apply hb.2; simp only [depth] at hs; simp only [Nat.dist_zero_left]; omega
      | succ s =>
        rw [Polynomial.coeff_X_mul]
        have hz : (match v with
          | none => (0 : Polynomial ℚ)
          | some p => Polynomial.C (product (leg ell) r ⟨0,he⟩ p.2)).coeff (s+1) = 0 := by
          cases v <;> simp
        rw [hz, add_zero]
        apply ih (by omega) none v s
        simp only [depth] at hs ⊢; omega
    · rw [if_neg hu, if_neg hu, Polynomial.coeff_zero, add_zero, add_zero]
      rw [Finset.sum_eq_single (parent u)]
      · have hp := parent_depth u hu
        exact mul_pos (rationalShift_parent m ell r u hu)
          (ih (by omega) (parent u) v s (by omega))
      · intro w _ hwp
        by_cases hw : rationalShift m ell r u w = 0
        · rw [hw, zero_mul]
        · have hd := rationalShift_nonparent_depth m ell r u w hu hwp hw
          rw [correction_coeff_zero m ell r (by omega) w v s (by omega), mul_zero]
      · simp

private theorem correction_vanishes (m ell r : ℕ) (hr : r < ell)
    (u v : Vertex m ell) (h : r < depth u + depth v) : correction m ell r u v = 0 := by
  apply Polynomial.ext; intro s; rw [Polynomial.coeff_zero]
  exact correction_coeff_zero m ell r hr u v s (by omega)

private theorem block_nonneg (m ell r : ℕ) (hr : r < ell) (u v : Vertex m ell) :
    0 ≤ legBlock m ell (product (leg ell) r) u v := by
  cases u <;> cases v <;> simp only [legBlock]
  · norm_num
  · norm_num
  · norm_num
  · split_ifs
    · exact (product_leg_band ell r hr _ _).1
    · norm_num

private theorem polynomial_entry_nonzero (m ell r : ℕ) (hr : r < ell) (u v : Vertex m ell) (hd : distance u v ≤ r) :
    product (polynomialMatrix m ell) r u v ≠ 0 := by
  have hE : product (polynomialMatrix m ell) r u v = correction m ell r u v +
      Polynomial.C (legBlock m ell (product (leg ell) r) u v) := by
    simp only [correction, Matrix.sub_apply, Matrix.map_apply]; ring
  rw [hE]
  by_cases hc : depth u + depth v ≤ r
  · let s := r - (depth u + depth v)
    have hs : r = depth u + depth v + s := by dsimp [s]; omega
    have hpos := correction_coeff_positive m ell r hr u v s hs
    have hblock := block_nonneg m ell r hr u v
    have hn : 0 < (correction m ell r u v + Polynomial.C (legBlock m ell (product (leg ell) r) u v)).coeff s := by
      rw [Polynomial.coeff_add, Polynomial.coeff_C]
      split_ifs <;> linarith
    intro hzero
    rw [hzero, Polynomial.coeff_zero] at hn
    exact (lt_irrefl _ hn)
  · rw [correction_vanishes m ell r hr u v (by omega), zero_add]
    apply Polynomial.C_ne_zero.mpr
    cases u with
    | none => cases v <;> simp only [depth, distance] at hc hd <;> omega
    | some p =>
      cases v with
      | none => simp only [depth,distance] at hc hd; omega
      | some q =>
        rcases p with ⟨a,i⟩
        rcases q with ⟨b,j⟩
        by_cases hab : a = b
        · simp only [distance, if_pos hab] at hd
          simp only [legBlock, if_pos hab]
          exact ne_of_gt ((product_leg_band ell r hr i j).2.2 hd)
        · simp only [distance, if_neg hab, depth] at hd hc
          omega

private theorem polynomial_entry_zero (m ell r : ℕ) (hr : r < ell) (u v : Vertex m ell) (hd : r < distance u v) :
    product (polynomialMatrix m ell) r u v = 0 := by
  have hsum : r < depth u + depth v := by
    cases u <;> cases v <;> simp only [depth,distance] at *
    · omega
    · omega
    · omega
    · split_ifs at hd <;> (try simp only [Nat.dist] at hd) <;> omega
  have hc := correction_vanishes m ell r hr u v hsum
  have hb : legBlock m ell (product (leg ell) r) u v = 0 := by
    cases u with
    | none => simp [legBlock]
    | some p =>
      cases v with
      | none => simp [legBlock]
      | some q =>
        simp only [legBlock]
        split_ifs with h
        · simp only [distance, if_pos h] at hd
          exact product_leg_zero ell r hr _ _ hd
        · rfl
  have hE : product (polynomialMatrix m ell) r u v = correction m ell r u v +
      Polynomial.C (legBlock m ell (product (leg ell) r) u v) := by
    simp only [correction, Matrix.sub_apply, Matrix.map_apply]; ring
  rw [hE,hc,hb,Polynomial.C_0,zero_add]

private theorem spider_supported_parameter (m k ell : ℕ) (hl : k+1 ≤ ell) : ∃ t : ℕ, ∀ u v : Vertex m ell, u ≠ v →
      (product (spiderMatrix m ell (t:ℚ)) k u v ≠ 0 ↔ (power m k ell).Adj u v) := by
  classical
  let I := { p : Vertex m ell × Vertex m ell // (power m k ell).Adj p.1 p.2 }
  obtain ⟨t,ht⟩ := simultaneous_natural_parameter
    (fun p : I => product (polynomialMatrix m ell) k p.val.1 p.val.2)
    (fun p => polynomial_entry_nonzero m ell k (by omega) p.val.1 p.val.2 p.property.2)
  refine ⟨t,?_⟩
  intro u v huv
  have hEval := congrFun (congrFun (product_eval m ell k (t:ℚ)) u) v
  change (product (polynomialMatrix m ell) k u v).eval (t:ℚ) = product (spiderMatrix m ell (t:ℚ)) k u v at hEval
  rw [← hEval]
  constructor
  · intro h
    refine ⟨huv,?_⟩
    by_contra hd
    have hz := polynomial_entry_zero m ell k (by omega) u v (by omega)
    rw [hz,Polynomial.eval_zero] at h
    exact h rfl
  · intro hadj
    exact ht ⟨(u,v),hadj⟩

private theorem spider_all_sets_lower (m k ell : ℕ) (hm : 2 ≤ m) (hl : k+1 ≤ ell)
    (S : Finset (Vertex m ell)) (hS : IsZeroForcing (power m k ell) (S : Set _)) : (m-1)*k ≤ S.card := by
  obtain ⟨t,ht⟩ := spider_supported_parameter m k ell hl
  exact (spider_kernel_dimension m k ell hm hl (t:ℚ)).trans
    (kernel_finrank_le_forcing (power m k ell) (product (spiderMatrix m ell (t:ℚ)) k) ht S hS)

/-- Conjecture 10: ordinary powers of the equal-legged spider have zero forcing number `(m-1)k`. -/
theorem result (m k ell : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) (hl : k+1 ≤ ell) :
    zeroForcingNumber (power m k ell) = (m-1)*k := by
  have htail := tail_forces m k ell hm hk hl
  apply Nat.le_antisymm
  · exact Nat.sInf_le ⟨tail m k ell,tail_card m k ell hm hk hl,htail⟩
  · have hne : {n : ℕ | ∃ S : Finset (Vertex m ell), S.card = n ∧ IsZeroForcing (power m k ell) (S : Set _)}.Nonempty :=
      ⟨(tail m k ell).card,tail m k ell,rfl,htail⟩
    obtain ⟨S,hcard,hS⟩ := Nat.sInf_mem hne
    have h := spider_all_sets_lower m k ell hm hl S hS
    simpa only [hcard,zeroForcingNumber] using h

#print axioms result

end D5.S3.Combinatorics.SpectralGraph.SpiderPowerZeroForcing
