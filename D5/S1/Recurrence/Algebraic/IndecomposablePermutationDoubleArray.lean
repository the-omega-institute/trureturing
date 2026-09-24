/- GID: D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Pi, mathlib/module/Mathlib.Data.Fintype.Perm, mathlib/module/Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: Indecomposable permutations are the common exact border of Kurkov's two arrays. -/

/- Formalization classification:
   proof_shape: result: content
   escape_witness: result (least-stable-prefix decomposition and two array invariants)
   admission_basis: open-problem-resolution (issue #9477)
   Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Sum

namespace D5.S1.Recurrence.Algebraic.IndecomposablePermutationDoubleArray

/-- Permutations with no proper nonempty invariant initial interval. -/
def IndecomposablePerm (n : ℕ) :=
  {p : Equiv.Perm (Fin n) //
    ∀ k : ℕ, 0 < k → k < n →
      ¬ (∀ i : Fin n, (p i).val < k ↔ i.val < k)}

/-- The number of indecomposable permutations of `Fin n`. -/
noncomputable def c (n : ℕ) : ℕ :=
  by
    letI : Finite (IndecomposablePerm n) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    exact @Fintype.card (IndecomposablePerm n) (Fintype.ofFinite _)

/-- Kurkov's first array, OEIS A370380. -/
def U : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, k => (k + 2) * U m (k + 1) + ∑ j ∈ Finset.range (k + 1), U m j

/-- Kurkov's second array, OEIS A370381. -/
def V : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, k => ∑ j ∈ Finset.range (k + 2), (k + 2).choose (j + 1) * V m j

/-- Kurkov's conjecture: the actual indecomposable-permutation count is the
common left border of the two recursively defined arrays. -/
theorem result :
    c 0 = 1 ∧ c 1 = 1 ∧
      ∀ n : ℕ, 2 ≤ n → c n = U (n - 2) 0 ∧ c n = V (n - 2) 0 := by
  classical
  let Stable {n : ℕ} (p : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
    ∀ i : Fin n, (p i).val < k ↔ i.val < k
  let prefixEquiv {n k : ℕ} (hk : k ≤ n) :
      {i : Fin n // i.val < k} ≃ Fin k :=
    { toFun := fun i => ⟨i.val, i.property⟩
      invFun := fun i => ⟨⟨i.val, lt_of_lt_of_le i.isLt hk⟩, i.isLt⟩
      left_inv := fun i => by ext; rfl
      right_inv := fun i => by ext; rfl }
  let suffixEquiv {n k : ℕ} (hk : k ≤ n) :
      {i : Fin n // ¬ i.val < k} ≃ Fin (n - k) :=
    { toFun := fun i => ⟨i.val - k, by omega⟩
      invFun := fun i => ⟨⟨k + i.val, by omega⟩, by simp⟩
      left_inv := fun i => by
        ext
        change k + (i.val - k) = i.val
        omega
      right_inv := fun i => by
        ext
        change k + i.val - k = i.val
        omega }
  let splitLeft {n k : ℕ} (hk : k ≤ n) (p : Equiv.Perm (Fin n))
      (hp : Stable p k) : Equiv.Perm (Fin k) :=
    (prefixEquiv hk).permCongr (p.subtypePerm hp)
  let splitRight {n k : ℕ} (hk : k ≤ n) (p : Equiv.Perm (Fin n))
      (hp : Stable p k) : Equiv.Perm (Fin (n - k)) :=
    (suffixEquiv hk).permCongr
      (p.subtypePerm (fun i => not_congr (hp i)))
  let join {n k : ℕ} (hk : k ≤ n) (a : Equiv.Perm (Fin k))
      (b : Equiv.Perm (Fin (n - k))) : Equiv.Perm (Fin n) :=
    ((prefixEquiv hk).permCongr.symm a).subtypeCongr
      ((suffixEquiv hk).permCongr.symm b)
  have join_stable {n k : ℕ} (hk : k ≤ n) (a : Equiv.Perm (Fin k))
      (b : Equiv.Perm (Fin (n - k))) : Stable (join hk a b) k := by
    intro i
    by_cases hi : i.val < k
    · simp [join, Equiv.Perm.subtypeCongr.left_apply _ _ hi, hi,
        Equiv.permCongr_symm_apply, prefixEquiv]
    · simp [join, Equiv.Perm.subtypeCongr.right_apply _ _ hi, hi,
        Equiv.permCongr_symm_apply, suffixEquiv]
  have join_split {n k : ℕ} (hk : k ≤ n) (p : Equiv.Perm (Fin n))
      (hp : Stable p k) : join hk (splitLeft hk p hp) (splitRight hk p hp) = p := by
    ext i
    by_cases hi : i.val < k
    · rw [show join hk (splitLeft hk p hp) (splitRight hk p hp) i =
          ((prefixEquiv hk).permCongr.symm (splitLeft hk p hp)) ⟨i, hi⟩ by
            simp [join, hi]]
      rw [show (prefixEquiv hk).permCongr.symm (splitLeft hk p hp) =
          p.subtypePerm hp by
            exact (prefixEquiv hk).permCongr.left_inv _]
      rfl
    · rw [show join hk (splitLeft hk p hp) (splitRight hk p hp) i =
          ((suffixEquiv hk).permCongr.symm (splitRight hk p hp)) ⟨i, hi⟩ by
            simp [join, hi]]
      rw [show (suffixEquiv hk).permCongr.symm (splitRight hk p hp) =
          p.subtypePerm (fun i => not_congr (hp i)) by
            exact (suffixEquiv hk).permCongr.left_inv _]
      rfl
  have split_join_left {n k : ℕ} (hk : k ≤ n) (a : Equiv.Perm (Fin k))
      (b : Equiv.Perm (Fin (n - k))) :
      splitLeft hk (join hk a b) (join_stable hk a b) = a := by
    ext i
    simp [splitLeft, join, Equiv.permCongr_apply, Equiv.permCongr_symm_apply,
      prefixEquiv]
  have split_join_right {n k : ℕ} (hk : k ≤ n) (a : Equiv.Perm (Fin k))
      (b : Equiv.Perm (Fin (n - k))) :
      splitRight hk (join hk a b) (join_stable hk a b) = b := by
    ext i
    simp [splitRight, join, Equiv.permCongr_apply, Equiv.permCongr_symm_apply,
      suffixEquiv]
  have splitLeft_val {n k : ℕ} (hk : k ≤ n) (p : Equiv.Perm (Fin n))
      (hp : Stable p k) (i : Fin k) :
      (splitLeft hk p hp i).val = (p ⟨i.val, lt_of_lt_of_le i.isLt hk⟩).val := by
    simp [splitLeft, Equiv.permCongr_apply, prefixEquiv]
  have join_left_val {n k : ℕ} (hk : k ≤ n) (a : Equiv.Perm (Fin k))
      (b : Equiv.Perm (Fin (n - k))) (i : Fin k) :
      (join hk a b ⟨i.val, lt_of_lt_of_le i.isLt hk⟩).val = (a i).val := by
    simp [join, Equiv.permCongr_symm_apply, prefixEquiv]
  let BlockDecomposition (n : ℕ) :=
    Σ k : {k : ℕ // 1 ≤ k ∧ k ≤ n},
      IndecomposablePerm k.val × Equiv.Perm (Fin (n - k.val))
  have stable_exists {n : ℕ} (hn : 1 ≤ n) (p : Equiv.Perm (Fin n)) :
      ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ Stable p k := by
    refine ⟨n, by omega, le_rfl, ?_⟩
    intro i
    simp
  let firstIndex {n : ℕ} (hn : 1 ≤ n) (p : Equiv.Perm (Fin n)) :
      {k : ℕ // 1 ≤ k ∧ k ≤ n} :=
    ⟨Nat.find (stable_exists hn p),
      (Nat.find_spec (stable_exists hn p)).1,
      (Nat.find_spec (stable_exists hn p)).2.1⟩
  let Fiber {n : ℕ} (hn : 1 ≤ n) (idx : {k : ℕ // 1 ≤ k ∧ k ≤ n}) :=
    {p : Equiv.Perm (Fin n) // firstIndex hn p = idx}
  have fiberEquiv {n : ℕ} (hn : 1 ≤ n)
      (idx : {k : ℕ // 1 ≤ k ∧ k ≤ n}) :
      Fiber hn idx ≃
        (IndecomposablePerm idx.val × Equiv.Perm (Fin (n - idx.val))) := by
    let k := idx.val
    have hkn : k ≤ n := idx.property.2
    let parts (x : Fiber hn idx) :
        IndecomposablePerm k × Equiv.Perm (Fin (n - k)) := by
      let p := x.val
      have hfind : Nat.find (stable_exists hn p) = k := by
        exact congrArg Subtype.val x.property
      have hstable : Stable p k := by
        simpa only [hfind] using (Nat.find_spec (stable_exists hn p)).2.2
      have hindecomp :
          ∀ l : ℕ, 0 < l → l < k →
            ¬ Stable (splitLeft hkn p hstable) l := by
        intro l hl0 hlk hleft
        apply Nat.find_min (stable_exists hn p)
        · simpa only [hfind] using hlk
        refine ⟨hl0, le_trans (Nat.le_of_lt hlk) hkn, ?_⟩
        intro i
        by_cases hik : i.val < k
        · let ii : Fin k := ⟨i.val, hik⟩
          have h := hleft ii
          rw [splitLeft_val hkn p hstable ii] at h
          simpa [ii] using h
        · have hpik : ¬ (p i).val < k := by
            intro h
            exact hik ((hstable i).mp h)
          constructor <;> intro h <;> omega
      exact ⟨⟨splitLeft hkn p hstable, hindecomp⟩,
        splitRight hkn p hstable⟩
    let combine (y : IndecomposablePerm k × Equiv.Perm (Fin (n - k))) :
        Fiber hn idx := by
      refine ⟨join hkn y.1.val y.2, ?_⟩
      apply Subtype.ext
      apply (Nat.find_eq_iff _).2
      refine ⟨⟨idx.property.1, hkn, join_stable hkn y.1.val y.2⟩, ?_⟩
      intro l hlk hl
      rcases hl with ⟨hl0, -, hstable⟩
      apply y.1.property l hl0 hlk
      intro i
      let ii : Fin n := ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩
      have h := hstable ii
      rw [join_left_val hkn y.1.val y.2 i] at h
      simpa [ii] using h
    exact
      { toFun := parts
        invFun := combine
        left_inv := fun x => by
          apply Subtype.ext
          exact join_split hkn x.val _
        right_inv := fun y => by
          apply Prod.ext
          · apply Subtype.ext
            exact split_join_left hkn y.1.val y.2
          · exact split_join_right hkn y.1.val y.2 }
  have blockEquiv {n : ℕ} (hn : 1 ≤ n) :
      Equiv.Perm (Fin n) ≃ BlockDecomposition n :=
    (Equiv.sigmaFiberEquiv (firstIndex hn)).symm |>.trans
      (Equiv.sigmaCongrRight (fiberEquiv hn))
  letI indecompFinite (n : ℕ) : Finite (IndecomposablePerm n) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI indecompFintype (n : ℕ) : Fintype (IndecomposablePerm n) :=
    Fintype.ofFinite _
  letI blockIndexFinite (n : ℕ) : Finite {k : ℕ // 1 ≤ k ∧ k ≤ n} :=
    Finite.of_injective
      (fun k => (⟨k.val, Nat.lt_succ_of_le k.property.2⟩ : Fin (n + 1)))
      (fun _ _ h => Subtype.ext (Fin.ext_iff.mp h))
  letI blockIndexFintype (n : ℕ) : Fintype {k : ℕ // 1 ≤ k ∧ k ≤ n} :=
    Fintype.ofFinite _
  have card_first_block (n : ℕ) (hn : 1 ≤ n) :
      Nat.factorial n = ∑ k : {k : ℕ // 1 ≤ k ∧ k ≤ n},
        c k.val * Nat.factorial (n - k.val) := by
    calc
      Nat.factorial n = Fintype.card (Equiv.Perm (Fin n)) := by
        simpa using (@Fintype.card_perm (Fin n) inferInstance).symm
      _ = Fintype.card (BlockDecomposition n) := Fintype.card_congr (blockEquiv hn)
      _ = ∑ k : {k : ℕ // 1 ≤ k ∧ k ≤ n},
          c k.val * Nat.factorial (n - k.val) := by
            simp [BlockDecomposition, c, Fintype.card_perm]
  have hc0 : c 0 = 1 := by
    letI : Finite (IndecomposablePerm 0) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI : Fintype (IndecomposablePerm 0) := Fintype.ofFinite _
    unfold c
    let p0 : IndecomposablePerm 0 := ⟨Equiv.refl _, by omega⟩
    exact Fintype.card_eq_one_of_forall_eq (i := p0) fun p => by
      apply Subtype.ext
      exact Subsingleton.elim _ _
  have hc1 : c 1 = 1 := by
    letI : Finite (IndecomposablePerm 1) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI : Fintype (IndecomposablePerm 1) := Fintype.ofFinite _
    unfold c
    let p1 : IndecomposablePerm 1 := ⟨Equiv.refl _, by omega⟩
    exact Fintype.card_eq_one_of_forall_eq (i := p1) fun p => by
      apply Subtype.ext
      exact Subsingleton.elim _ _
  let blockIndexEquiv (r : ℕ) : Fin (r + 1) ≃ {k : ℕ // 1 ≤ k ∧ k ≤ r + 1} :=
    { toFun := fun j => ⟨j.val + 1, by omega⟩
      invFun := fun k => ⟨k.val - 1, by omega⟩
      left_inv := fun j => by ext; simp
      right_inv := fun k => by ext; simp; omega }
  have actual_convolution (r : ℕ) (hr : 1 ≤ r) :
      ∑ j ∈ Finset.range r, c (j + 2) * Nat.factorial (r - 1 - j) =
        r * Nat.factorial r := by
    have hcard := card_first_block (r + 1) (by omega)
    have hreindex :
        (∑ k : {k : ℕ // 1 ≤ k ∧ k ≤ r + 1},
            c k.val * Nat.factorial (r + 1 - k.val)) =
          ∑ j : Fin (r + 1), c (j.val + 1) * Nat.factorial (r - j.val) := by
      symm
      apply Fintype.sum_equiv (blockIndexEquiv r)
      intro j
      simp [blockIndexEquiv]
    rw [hreindex, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ'] at hcard
    have hcard_clean :
        Nat.factorial (r + 1) =
          (∑ j ∈ Finset.range r,
            c (j + 2) * Nat.factorial (r - 1 - j)) + Nat.factorial r := by
      rw [hcard]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        have hjr : j < r := Finset.mem_range.mp hj
        rw [dif_pos (by omega)]
        simp only [Fin.val_mk]
        rw [show j + 1 + 1 = j + 2 by omega,
          show r - (j + 1) = r - 1 - j by omega]
      · simp [hc1]
    rw [Nat.factorial_succ] at hcard_clean
    apply Nat.add_right_cancel (m := Nat.factorial r)
    calc
      (∑ j ∈ Finset.range r, c (j + 2) * Nat.factorial (r - 1 - j)) +
          Nat.factorial r = (r + 1) * Nat.factorial r := hcard_clean.symm
      _ = r * Nat.factorial r + Nat.factorial r := by ring
  let P (m k : ℕ) := ∑ i ∈ Finset.range k, U m i
  have P_zero (k : ℕ) : P 0 k = k := by
    simp [P, U]
  have P_step (m k : ℕ) :
      P (m + 1) k + U m 0 = (k + 1) * P m (k + 1) := by
    induction k with
    | zero => simp [P]
    | succ k ih =>
        rw [show P (m + 1) (k + 1) = P (m + 1) k + U (m + 1) k by
          simp [P, Finset.sum_range_succ]]
        calc
          P (m + 1) k + U (m + 1) k + U m 0 =
              (P (m + 1) k + U m 0) + U (m + 1) k := by omega
          _ = (k + 1) * P m (k + 1) + U (m + 1) k := by rw [ih]
          _ = (k + 1) * P m (k + 1) +
              ((k + 2) * U m (k + 1) + P m (k + 1)) := by rw [U]
          _ = (k + 2) * P m (k + 2) := by
            rw [show P m (k + 2) = P m (k + 1) + U m (k + 1) by
              simp [P, Finset.sum_range_succ]]
            ring
  have U_invariant (m k : ℕ) :
      P m k +
          ∑ j ∈ Finset.range m,
            (k + 1).ascFactorial (m - 1 - j) * U j 0 =
        (k + 1).ascFactorial m * (k + m) := by
    induction m generalizing k with
    | zero => simp [P_zero]
    | succ m ih =>
        calc
          P (m + 1) k +
                ∑ j ∈ Finset.range (m + 1),
                  (k + 1).ascFactorial (m + 1 - 1 - j) * U j 0 =
              (P (m + 1) k + U m 0) +
                ∑ j ∈ Finset.range m,
                  (k + 1).ascFactorial (m - j) * U j 0 := by
                    rw [Finset.sum_range_succ]
                    simp only [Nat.add_sub_cancel, Nat.sub_self,
                      Nat.ascFactorial_zero, Nat.one_mul]
                    ac_rfl
          _ = (k + 1) * P m (k + 1) +
                ∑ j ∈ Finset.range m,
                  (k + 1).ascFactorial (m - j) * U j 0 := by
                    rw [P_step]
          _ = (k + 1) *
                (P m (k + 1) +
                  ∑ j ∈ Finset.range m,
                    (k + 2).ascFactorial (m - 1 - j) * U j 0) := by
                    rw [Nat.mul_add, Finset.mul_sum]
                    congr 1
                    rw [Finset.mul_sum (Finset.range m)]
                    apply Finset.sum_congr rfl
                    intro j hj
                    have hjm : j < m := Finset.mem_range.mp hj
                    rw [show m - j = (m - 1 - j) + 1 by omega,
                      Nat.ascFactorial_succ, ← Nat.succ_ascFactorial]
                    simp only [Nat.succ_eq_add_one]
                    ring
          _ = (k + 1) *
                ((k + 2).ascFactorial m * (k + 1 + m)) := by
                    rw [ih (k + 1)]
          _ = (k + 1).ascFactorial (m + 1) * (k + (m + 1)) := by
                    rw [Nat.ascFactorial_succ, ← Nat.succ_ascFactorial]
                    simp only [Nat.succ_eq_add_one]
                    ring
  have U_convolution (m : ℕ) (hm : 1 ≤ m) :
      ∑ j ∈ Finset.range m, U j 0 * Nat.factorial (m - 1 - j) =
        m * Nat.factorial m := by
    have h := U_invariant m 0
    simpa [P, Nat.one_ascFactorial, Nat.mul_comm] using h
  let B : ℕ → ℕ → ℕ
    | _, 0 => 0
    | _, 1 => 0
    | m, q + 2 => V m q
  let delta : ℕ → ℕ
    | 1 => 1
    | _ => 0
  let E (a q : ℕ) := a ^ q
  let T : (ℕ → ℕ) →+ (ℕ → ℕ) :=
    { toFun := fun f q =>
        ∑ r ∈ Finset.range (q + 1), q.choose r * f (r + 1)
      map_zero' := by
        funext q
        simp
      map_add' := by
        intro f g
        funext q
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] }
  have T_B (m : ℕ) : T (B m) = B (m + 1) + V m 0 • delta := by
    funext q
    rcases q with _ | q
    · norm_num [T, B, delta, Finset.sum_range_succ]
    rcases q with _ | q
    · norm_num [T, B, delta, Finset.sum_range_succ, Nat.choose]
    rw [show q + 1 + 1 = q + 2 by omega]
    simp only [T, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.add_apply,
      Pi.smul_apply, Nat.nsmul_eq_mul]
    rw [Finset.sum_range_succ']
    simp [B, delta, V]
  have T_E (a : ℕ) : T (E a) = a • E (a + 1) := by
    funext q
    simp only [T, AddMonoidHom.coe_mk, ZeroHom.coe_mk, E, Pi.smul_apply,
      Nat.nsmul_eq_mul]
    calc
      (∑ r ∈ Finset.range (q + 1), q.choose r * a ^ (r + 1)) =
          a * ∑ r ∈ Finset.range (q + 1), q.choose r * a ^ r := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            rw [pow_succ]
            ring
      _ = a * (a + 1) ^ q := by
            congr 1
            simpa [mul_comm, mul_left_comm, mul_assoc] using (add_pow a 1 q).symm
  have T_delta : T delta = E 1 := by
    funext q
    simp only [T, AddMonoidHom.coe_mk, ZeroHom.coe_mk, E]
    rw [Finset.sum_eq_single 0]
    · simp [delta]
    · intro r hr hr0
      have : r + 1 ≠ 1 := by omega
      simp [delta, this]
    · simp
  have initial_identity : B 0 + E 0 + delta = E 1 := by
    funext q
    rcases q with _ | q
    · simp [B, E, delta]
    rcases q with _ | q
    · simp [B, E, delta]
    simp [B, E, delta, V]
  let I (m : ℕ) (f : ℕ → ℕ) :=
    ((T : (ℕ → ℕ) → (ℕ → ℕ))^[m]) f
  have I_zero (m : ℕ) : I m 0 = 0 := by
    induction m with
    | zero => simp [I]
    | succ m ih =>
        simp only [I, Function.iterate_succ_apply']
        rw [show ((T : (ℕ → ℕ) → (ℕ → ℕ))^[m]) 0 = 0 by simpa [I] using ih]
        exact T.map_zero
  have I_add (m : ℕ) (f g : ℕ → ℕ) : I m (f + g) = I m f + I m g := by
    induction m with
    | zero => simp [I]
    | succ m ih =>
        simp only [I, Function.iterate_succ_apply']
        rw [show ((T : (ℕ → ℕ) → (ℕ → ℕ))^[m]) (f + g) =
          ((T : (ℕ → ℕ) → (ℕ → ℕ))^[m]) f +
            ((T : (ℕ → ℕ) → (ℕ → ℕ))^[m]) g by simpa [I] using ih]
        exact T.map_add _ _
  have I_nsmul (m a : ℕ) (f : ℕ → ℕ) : I m (a • f) = a • I m f := by
    induction m with
    | zero => simp [I]
    | succ m ih =>
        simp only [I, Function.iterate_succ_apply']
        rw [show ((T : (ℕ → ℕ) → (ℕ → ℕ))^[m]) (a • f) =
          a • ((T : (ℕ → ℕ) → (ℕ → ℕ))^[m]) f by simpa [I] using ih]
        exact T.map_nsmul _ _
  have I_E_one (m : ℕ) : I m (E 1) = Nat.factorial m • E (m + 1) := by
    induction m with
    | zero => funext q; simp [I, E]
    | succ m ih =>
        calc
          I (m + 1) (E 1) = T (I m (E 1)) := by
            simp [I, Function.iterate_succ_apply']
          _ = T (Nat.factorial m • E (m + 1)) := by rw [ih]
          _ = Nat.factorial m • T (E (m + 1)) := T.map_nsmul _ _
          _ = Nat.factorial m • ((m + 1) • E (m + 2)) := by rw [T_E]
          _ = Nat.factorial (m + 1) • E (m + 2) := by
            funext q
            simp [Nat.factorial_succ, Pi.smul_apply, Nat.nsmul_eq_mul]
            ring
  have I_E_zero (m : ℕ) (hm : 1 ≤ m) : I m (E 0) = 0 := by
    rcases m with _ | m
    · omega
    · calc
        I (m + 1) (E 0) = I m (T (E 0)) := by
          simp [I, Function.iterate_succ_apply]
        _ = I m 0 := by rw [T_E]; simp
        _ = 0 := I_zero m
  have I_delta (m : ℕ) :
      I m delta = if m = 0 then delta else Nat.factorial (m - 1) • E m := by
    rcases m with _ | m
    · simp [I]
    · rw [if_neg (by omega)]
      calc
        I (m + 1) delta = I m (T delta) := by
          simp [I, Function.iterate_succ_apply]
        _ = I m (E 1) := by rw [T_delta]
        _ = Nat.factorial m • E (m + 1) := I_E_one m
        _ = Nat.factorial (m + 1 - 1) • E (m + 1) := by simp
  have I_delta_one (m : ℕ) : I m delta 1 = Nat.factorial m := by
    rcases m with _ | m
    · simp [I, delta]
    · rw [I_delta, if_neg (by omega)]
      simp [E, Nat.factorial_succ, Nat.nsmul_eq_mul, Nat.mul_comm]
  have I_succ (m : ℕ) (f : ℕ → ℕ) : I (m + 1) f = T (I m f) := by
    simp [I, Function.iterate_succ_apply']
  have I_B (m : ℕ) :
      I m (B 0) = B m +
        ∑ j ∈ Finset.range m, V j 0 • I (m - 1 - j) delta := by
    induction m with
    | zero => simp [I]
    | succ m ih =>
        have hold :
            T (∑ j ∈ Finset.range m, V j 0 • I (m - 1 - j) delta) =
              ∑ j ∈ Finset.range m, V j 0 • I (m - j) delta := by
          rw [map_sum T]
          apply Finset.sum_congr rfl
          intro j hj
          have hjm : j < m := Finset.mem_range.mp hj
          rw [T.map_nsmul]
          congr 1
          rw [← I_succ]
          congr 1
          omega
        have hshift :
            (∑ j ∈ Finset.range m, V j 0 • I (m - j) delta) =
              ∑ j ∈ Finset.range m,
                V j 0 • I (m + 1 - 1 - j) delta := by
          apply Finset.sum_congr rfl
          intro j hj
          congr 2
        calc
          I (m + 1) (B 0) = T (I m (B 0)) := I_succ m (B 0)
          _ = T (B m +
              ∑ j ∈ Finset.range m, V j 0 • I (m - 1 - j) delta) := by rw [ih]
          _ = T (B m) +
              T (∑ j ∈ Finset.range m, V j 0 • I (m - 1 - j) delta) :=
                T.map_add _ _
          _ = (B (m + 1) + V m 0 • delta) +
              ∑ j ∈ Finset.range m, V j 0 • I (m - j) delta := by
                rw [T_B, hold]
          _ = B (m + 1) +
              ∑ j ∈ Finset.range (m + 1),
                V j 0 • I (m + 1 - 1 - j) delta := by
                rw [Finset.sum_range_succ, ← hshift]
                simp [I]
                ac_rfl
  have V_convolution (m : ℕ) (hm : 1 ≤ m) :
      ∑ j ∈ Finset.range m, V j 0 * Nat.factorial (m - 1 - j) =
        m * Nat.factorial m := by
    have hiter := congrArg (fun f => I m f) initial_identity
    rw [I_add, I_add, I_E_zero m hm, I_E_one] at hiter
    have hcoord := congrFun hiter 1
    have hsum :
        I m (B 0) 1 + Nat.factorial m =
          m * Nat.factorial m + Nat.factorial m := by
      simpa [Pi.add_apply, Pi.smul_apply, Nat.nsmul_eq_mul, I_delta_one, E,
        Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcoord
    have hborder : I m (B 0) 1 = m * Nat.factorial m :=
      Nat.add_right_cancel hsum
    have hunroll := congrFun (I_B m) 1
    have hborder_sum :
        I m (B 0) 1 =
          ∑ j ∈ Finset.range m, V j 0 * Nat.factorial (m - 1 - j) := by
      simpa [B, Pi.add_apply, Pi.smul_apply, Nat.nsmul_eq_mul,
        I_delta_one] using hunroll
    exact hborder_sum.symm.trans hborder
  have convolution_unique (w z : ℕ → ℕ)
      (hw : ∀ r : ℕ, 1 ≤ r →
        ∑ j ∈ Finset.range r, w j * Nat.factorial (r - 1 - j) =
          r * Nat.factorial r)
      (hz : ∀ r : ℕ, 1 ≤ r →
        ∑ j ∈ Finset.range r, z j * Nat.factorial (r - 1 - j) =
          r * Nat.factorial r) :
      ∀ t : ℕ, w t = z t := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        have h := (hw (t + 1) (by omega)).trans (hz (t + 1) (by omega)).symm
        rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
        have hprefix :
            (∑ j ∈ Finset.range t,
                w j * Nat.factorial (t + 1 - 1 - j)) =
              ∑ j ∈ Finset.range t,
                z j * Nat.factorial (t + 1 - 1 - j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [ih j (Finset.mem_range.mp hj)]
        rw [hprefix] at h
        simpa using Nat.add_left_cancel h
  refine ⟨hc0, hc1, ?_⟩
  intro n hn
  have hU (t : ℕ) : U t 0 = c (t + 2) :=
    convolution_unique (fun m => U m 0) (fun m => c (m + 2))
      U_convolution actual_convolution t
  have hV (t : ℕ) : V t 0 = c (t + 2) :=
    convolution_unique (fun m => V m 0) (fun m => c (m + 2))
      V_convolution actual_convolution t
  constructor
  · calc
      c n = c (n - 2 + 2) := by congr 1; omega
      _ = U (n - 2) 0 := (hU (n - 2)).symm
  · calc
      c n = c (n - 2 + 2) := by congr 1; omega
      _ = V (n - 2) 0 := (hV (n - 2)).symm

end D5.S1.Recurrence.Algebraic.IndecomposablePermutationDoubleArray
