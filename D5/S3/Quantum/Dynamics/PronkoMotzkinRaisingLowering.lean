/- GID: D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves Conjecture 2 of Pronko (arXiv:2504.00835) on the periodic Motzkin spin-1 chain: the operators Sigma^+ and Sigma^-, sums of products of local powers s^r with total exponent 1 or -1, commute with the periodic Hamiltonian, send each ground state v_m to a nonzero multiple of v_(m+1), respectively v_(m-1), and send v_N, respectively v_(-N), to 0. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: an ordered product of site
  operators has the product of the local entries as its entries (`prod_sites`), and exactly one
  exponent vector `r` contributes to each entry of `Sig`, so `Sig N e a b = [S a = S b + e]`
  (`Sig_apply`); every row of the local projector sums to zero over each height class (`Pi_row`),
  so each two-site term and `H` annihilate every `v m` from both sides (`twoSite_mulVec`,
  `twoSite_Pi_v`, `H_v`, `v_H`), whence `H * Sig = 0 = Sig * H` (`H_Sig`, `Sig_H`); `Sig N e`
  sends `v m` to the number of words of height `m` times `v (m + e)` (`Sig_v`), positive for
  `|m| ≤ N` (`count_pos`), and `v (±(N + 1)) = 0` (`v_out`)
admission_basis: open-problem-resolution (issue #10569)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.PronkoMotzkinRaisingLowering

open Matrix

/-- Heights of the letters `u`, `f`, `d` (basis vectors `0`, `1`, `2`). -/
def ht : Fin 3 → ℤ := ![1, 0, -1]

/-- The spin-1 matrices `s⁺`, `s⁻` of eq. `spin1rep`. -/
def sp : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 1; 0, 0, 0]
def sm : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 1, 0, 0; 0, 1, 0]

/-- `s^r` for `r = -2, …, 2`, indexed by `Fin 5`. -/
def spow : Fin 5 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => sm ^ 2
  | 1 => sm
  | 2 => 1
  | 3 => sp
  | 4 => sp ^ 2
def rv (r : Fin 5) : ℤ := r.val - 2

/-- `A` acting on site `i`, the identity elsewhere. -/
def site {N : ℕ} (i : Fin N) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin N → Fin 3) (Fin N → Fin 3) ℂ :=
  fun a b => if ∀ j, j ≠ i → a j = b j then A (a i) (b i) else 0

/-- `Σ⁺` (`e = 1`) and `Σ⁻` (`e = -1`) of eq. `Sigmapmsum`. -/
noncomputable def Sig (N : ℕ) (e : ℤ) : Matrix (Fin N → Fin 3) (Fin N → Fin 3) ℂ :=
  ∑ r ∈ (Finset.univ.filter fun r : Fin N → Fin 5 => ∑ i, rv (r i) = e),
    (List.ofFn fun i => site i (spow (r i))).prod

/-- The height `S^z` of a word: the number of `u` minus the number of `d`. -/
def S {N : ℕ} (a : Fin N → Fin 3) : ℤ := ∑ i, ht (a i)

/-- The basis vector `|x y⟩` of `ℂ³ ⊗ ℂ³`. -/
def ket (x y : Fin 3) : Fin 3 × Fin 3 → ℂ := Pi.single (x, y) 1

/-- `½ w wᵀ` (`Matrix.vecMulVec`, no complex conjugation); for the real vectors in `piProj`
this is `½ |w⟩⟨w|`. -/
noncomputable def proj (w : Fin 3 × Fin 3 → ℂ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 2 : ℂ) • Matrix.vecMulVec w w

/-- The local projector `Π = U + D + F` of eq. `UDF` (`u = 0`, `f = 1`, `d = 2`). -/
noncomputable def piProj : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  proj (ket 0 1 - ket 1 0) + proj (ket 2 1 - ket 1 2) + proj (ket 0 2 - ket 1 1)

/-- `P` acting on the sites `i` (first factor) and `j` (second factor). -/
def twoSite {N : ℕ} (i j : Fin N) (P : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    Matrix (Fin N → Fin 3) (Fin N → Fin 3) ℂ :=
  fun a b => if ∀ k, k ≠ i → k ≠ j → a k = b k then P (a i, a j) (b i, b j) else 0

/-- The periodic Hamiltonian of eq. `Hpbc`: `Π_{i,i+1}` for `i < N` and `Π_{N,1}`. -/
noncomputable def H (N : ℕ) : Matrix (Fin N → Fin 3) (Fin N → Fin 3) ℂ :=
  ∑ i : Fin N, twoSite i (finRotate N i) piProj

/-- The ground state `v_m`: the sum of the words of height `m`. -/
def v (N : ℕ) (m : ℤ) : (Fin N → Fin 3) → ℂ := fun a => if S a = m then 1 else 0

/-- Conjecture 2 of Pronko: for `N ≥ 2`, `Σ^±` commute with `H^periodic`, send `v_m` to a nonzero
multiple of `v_{m ± 1}` when `m ≠ ± N`, and send `v_{± N}` to `0`. -/
def claim : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    Sig N 1 * H N = H N * Sig N 1 ∧ Sig N (-1) * H N = H N * Sig N (-1) ∧
      (∀ m : ℤ, -(N : ℤ) ≤ m → m < N → ∃ c : ℂ, c ≠ 0 ∧ Sig N 1 *ᵥ v N m = c • v N (m + 1)) ∧
      (∀ m : ℤ, -(N : ℤ) < m → m ≤ N → ∃ c : ℂ, c ≠ 0 ∧ Sig N (-1) *ᵥ v N m = c • v N (m - 1)) ∧
      Sig N 1 *ᵥ v N N = 0 ∧ Sig N (-1) *ᵥ v N (-N) = 0

/-- The conjecture holds. -/
theorem result : claim := by
  have spow_apply : ∀ (r : Fin 5) (x y : Fin 3), spow r x y = if ht x = ht y + rv r then 1 else 0
      := by
    intro r x y
    have h2m : sm ^ 2 = !![0, 0, 0; 0, 0, 0; 1, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_three, sm]
    have h2p : sp ^ 2 = !![0, 0, 1; 0, 0, 0; 0, 0, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_three, sp]
    fin_cases r <;> fin_cases x <;> fin_cases y <;> simp only [spow, h2m, h2p] <;>
      simp [sp, sm, rv, ht]
  have prod_sites : ∀ {N : ℕ} (A : Fin N → Matrix (Fin 3) (Fin 3) ℂ) (a b : Fin N → Fin 3),
      (List.ofFn fun i => site i (A i)).prod a b = ∏ i, A i (a i) (b i) := by
    intro N A a b
    classical
    have key : ∀ k (hk : k ≤ N) (b : Fin N → Fin 3),
        (List.ofFn fun i : Fin k => site (Fin.castLE hk i) (A (Fin.castLE hk i))).prod a b =
          (if ∀ j : Fin N, k ≤ j.val → a j = b j then 1 else 0) *
            ∏ i : Fin k, A (Fin.castLE hk i) (a (Fin.castLE hk i)) (b (Fin.castLE hk i)) := by
      intro k
      induction k with
      | zero =>
        intro hk b
        simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
          Matrix.one_apply, zero_le, forall_const]
        by_cases h : a = b
        · simp [h]
        · rw [if_neg h, if_neg (fun h' => h (funext h'))]
      | succ k ih =>
        intro hk b
        rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton,
          Matrix.mul_apply]
        set t : Fin N := Fin.castLE hk (Fin.last k) with ht
        have hk' : k ≤ N := by omega
        have e1 : (List.ofFn fun i : Fin k =>
            site (Fin.castLE hk (Fin.castSucc i)) (A (Fin.castLE hk (Fin.castSucc i)))) =
            List.ofFn fun i : Fin k => site (Fin.castLE hk' i) (A (Fin.castLE hk' i)) := by
          simp only [Fin.castLE_castSucc]
        rw [e1, Finset.sum_eq_single (Function.update b t (a t))]
        · have hne : ∀ i : Fin k, Fin.castLE hk' i ≠ t := by
            intro i h
            have := congrArg Fin.val h
            simp [ht] at this
            omega
          have h1 : ∀ i : Fin k,
              Function.update b t (a t) (Fin.castLE hk' i) = b (Fin.castLE hk' i) :=
            fun i => Function.update_of_ne (hne i) _ _
          have h2 : site t (A t) (Function.update b t (a t)) b = A t (a t) (b t) := by
            simp only [site]
            rw [if_pos (fun j hj => Function.update_of_ne hj _ _), Function.update_self]
          have h3 : (∀ j : Fin N, k ≤ j.val → a j = Function.update b t (a t) j) ↔
              (∀ j : Fin N, k + 1 ≤ j.val → a j = b j) := by
            constructor
            · intro h j hj
              have := h j (by omega)
              rwa [Function.update_of_ne (fun e => by subst e; simp [ht] at hj)] at this
            · intro h j hj
              by_cases e : j = t
              · subst e
                simp
              · rw [Function.update_of_ne e]
                apply h
                have : j.val ≠ k := fun hv => e (Fin.ext (by simp [ht, hv]))
                omega
          rw [ih hk', Fin.prod_univ_castSucc, h2]
          simp only [h1, Fin.castLE_castSucc]
          by_cases hc : ∀ j : Fin N, k + 1 ≤ j.val → a j = b j
          · rw [if_pos (h3.2 hc), if_pos hc]
            ring
          · rw [if_neg (fun h => hc (h3.1 h)), if_neg hc]
            ring
        · intro c _ hc
          rw [ih hk']
          simp only [site]
          by_cases h1 : ∀ j : Fin N, k ≤ j.val → a j = c j
          · by_cases h2 : ∀ j, j ≠ t → c j = b j
            · exfalso
              apply hc
              funext j
              by_cases e : j = t
              · subst e
                rw [Function.update_self]
                exact (h1 _ (by simp [ht])).symm
              · rw [Function.update_of_ne e]
                exact h2 j e
            · rw [if_neg h2, mul_zero]
          · rw [if_neg h1, zero_mul, zero_mul]
        · simp
    simpa using key N le_rfl b
  have Sig_apply : ∀ (N : ℕ) (e : ℤ) (a b : Fin N → Fin 3), Sig N e a b = if S a = S b + e then 1
      else 0 := by
    intro N e a b
    classical
    have hb : ∀ x y : Fin 3, 0 ≤ ht x - ht y + 2 ∧ ht x - ht y + 2 < 5 := by decide
    set r0 : Fin N → Fin 5 := fun i =>
      ⟨(ht (a i) - ht (b i) + 2).toNat, by have := hb (a i) (b i); omega⟩ with hr0
    have hrv : ∀ i, rv (r0 i) = ht (a i) - ht (b i) := by
      intro i
      have := hb (a i) (b i)
      simp only [rv, hr0]
      omega
    have hsum : ∑ i, rv (r0 i) = S a - S b := by
      simp only [hrv, S, Finset.sum_sub_distrib]
    have hz : ∀ r : Fin N → Fin 5, r ≠ r0 →
        ∏ i, (if ht (a i) = ht (b i) + rv (r i) then (1 : ℂ) else 0) = 0 := by
      intro r hr
      obtain ⟨i, hi⟩ : ∃ i, r i ≠ r0 i := by
        by_contra h
        push Not at h
        exact hr (funext h)
      refine Finset.prod_eq_zero (Finset.mem_univ i) (if_neg ?_)
      intro h
      apply hi
      apply Fin.ext
      have := hrv i
      simp only [rv] at this h
      omega
    have hone : ∏ i, (if ht (a i) = ht (b i) + rv (r0 i) then (1 : ℂ) else 0) = 1 :=
      Finset.prod_eq_one fun i _ => by rw [if_pos (by rw [hrv]; ring)]
    unfold Sig
    rw [Matrix.sum_apply]
    simp only [prod_sites, spow_apply]
    by_cases hc : S a = S b + e
    · rw [if_pos hc, Finset.sum_eq_single r0 (fun r _ hr => hz r hr)
        (fun h => absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hsum]; omega⟩) h), hone]
    · rw [if_neg hc]
      refine Finset.sum_eq_zero fun r hr => hz r fun h => hc ?_
      subst h
      have := (Finset.mem_filter.1 hr).2
      omega
  have twoSite_mulVec : ∀ {N : ℕ} (i j : Fin N) (hij : i ≠ j) (P : Matrix (Fin 3 × Fin 3) (Fin 3 ×
      Fin 3) ℂ) (f : (Fin N → Fin 3) → ℂ) (a : Fin N → Fin 3), (twoSite i j P *ᵥ f) a = ∑ p : Fin
      3 × Fin 3, P (a i, a j) p * f (Function.update (Function.update a i p.1) j p.2) := by
    intro N i j hij P f a
    classical
    set g : Fin 3 × Fin 3 → (Fin N → Fin 3) :=
      fun p => Function.update (Function.update a i p.1) j p.2 with hg
    have gi : ∀ p, g p i = p.1 := fun p => by
      simp [hg, Function.update_of_ne hij]
    have gj : ∀ p, g p j = p.2 := fun p => by simp [hg]
    have ginj : Function.Injective g := fun p q h => by
      have h1 := congrFun h i
      have h2 := congrFun h j
      rw [gi, gi] at h1
      rw [gj, gj] at h2
      exact Prod.ext h1 h2
    have goff : ∀ p k, k ≠ i → k ≠ j → g p k = a k := fun p k hki hkj => by
      simp [hg, Function.update_of_ne hkj, Function.update_of_ne hki]
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image g)), Finset.sum_image
      (fun p _ q _ h => ginj h)]
    · refine Finset.sum_congr rfl fun p _ => ?_
      simp only [twoSite]
      rw [if_pos (fun k hki hkj => (goff p k hki hkj).symm), gi, gj]
    · intro b _ hb
      simp only [twoSite]
      rw [if_neg, zero_mul]
      intro h
      apply hb
      refine Finset.mem_image.2 ⟨(b i, b j), Finset.mem_univ _, funext fun k => ?_⟩
      by_cases hki : k = i
      · subst hki
        exact gi _
      · by_cases hkj : k = j
        · subst hkj
          exact gj _
        · rw [goff _ k hki hkj]
          exact h k hki hkj
  have Pi_row : ∀ (p : Fin 3 × Fin 3) (t : ℤ), ∑ q : Fin 3 × Fin 3, piProj p q * (if ht q.1 + ht
      q.2 = t then 1 else 0) = 0 := by
    intro p t
    obtain ⟨x, y⟩ := p
    rw [Fintype.sum_prod_type]
    fin_cases x <;> fin_cases y <;>
      simp [piProj, proj, ket, Pi.single_apply, Matrix.vecMulVec_apply, Fin.sum_univ_three, ht] <;>
      split_ifs <;> ring
  have S_update : ∀ {N : ℕ} (f : Fin N → Fin 3) (i : Fin N) (x : Fin 3), S (Function.update f i x)
      = S f - ht (f i) + ht x := by
    intro N f i x
    unfold S
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      Function.update_self]
    have : ∑ k ∈ Finset.univ.erase i, ht (Function.update f i x k) =
        ∑ k ∈ Finset.univ.erase i, ht (f k) :=
      Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    rw [this]
    ring
  have twoSite_Pi_v : ∀ {N : ℕ} (i j : Fin N) (hij : i ≠ j) (m : ℤ), twoSite i j piProj *ᵥ v N m =
      0 := by
    intro N i j hij m
    funext a
    rw [twoSite_mulVec i j hij, Pi.zero_apply]
    have key : ∀ q : Fin 3 × Fin 3, v N m (Function.update (Function.update a i q.1) j q.2) =
        if ht q.1 + ht q.2 = m - S a + ht (a i) + ht (a j) then 1 else 0 := by
      intro q
      simp only [v, S_update, Function.update_of_ne hij.symm]
      congr 1
      apply propext
      constructor <;> intro h <;> omega
    simp only [key]
    exact Pi_row _ _
  have finRotate_ne : ∀ {N : ℕ} (hN : 2 ≤ N) (i : Fin N), i ≠ finRotate N i := by
    intro N hN i
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    intro h
    have := congrArg Fin.val h
    rw [finRotate_apply] at this
    by_cases hl : i = Fin.last (n + 1)
    · subst hl
      simp at this
    · rw [Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.2 hl)] at this
      omega
  have H_v : ∀ {N : ℕ} (hN : 2 ≤ N) (m : ℤ), H N *ᵥ v N m = 0 := by
    intro N hN m
    rw [H, Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun i _ => twoSite_Pi_v i _ (finRotate_ne hN i) m
  have H_transpose : ∀ (N : ℕ), (H N).transpose = H N := by
    intro N
    have hP : piProj.transpose = piProj := by
      simp only [piProj, proj, Matrix.transpose_add, Matrix.transpose_smul,
        Matrix.transpose_vecMulVec]
    rw [H, Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext a b
    simp only [Matrix.transpose_apply, twoSite]
    have hc : (∀ k, k ≠ i → k ≠ finRotate N i → b k = a k) ↔
        (∀ k, k ≠ i → k ≠ finRotate N i → a k = b k) :=
      ⟨fun h k h1 h2 => (h k h1 h2).symm, fun h k h1 h2 => (h k h1 h2).symm⟩
    by_cases h : ∀ k, k ≠ i → k ≠ finRotate N i → a k = b k
    · rw [if_pos (hc.2 h), if_pos h, ← Matrix.transpose_apply piProj, hP]
    · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]
  have v_H : ∀ {N : ℕ} (hN : 2 ≤ N) (m : ℤ), v N m ᵥ* H N = 0 := by
    intro N hN m
    rw [← Matrix.mulVec_transpose, H_transpose, H_v hN]
  have H_Sig : ∀ {N : ℕ} (hN : 2 ≤ N) (e : ℤ), H N * Sig N e = 0 := by
    intro N hN e
    ext a b
    rw [Matrix.mul_apply, Matrix.zero_apply]
    have := congrFun (H_v hN (S b + e)) a
    simp only [Matrix.mulVec, dotProduct, v, Pi.zero_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun c _ => by rw [Sig_apply]
  have Sig_H : ∀ {N : ℕ} (hN : 2 ≤ N) (e : ℤ), Sig N e * H N = 0 := by
    intro N hN e
    ext a b
    rw [Matrix.mul_apply, Matrix.zero_apply]
    have := congrFun (v_H hN (S a - e)) b
    simp only [Matrix.vecMul, dotProduct, v, Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Sig_apply]
    congr 1
    simp only [eq_comm (a := S c)]
    apply if_congr _ rfl rfl
    constructor <;> intro h <;> omega
  have Sig_v : ∀ (N : ℕ) (e m : ℤ), Sig N e *ᵥ v N m = ((Finset.univ.filter fun b : Fin N → Fin 3
      => S b = m).card : ℂ) • v N (m + e) := by
    intro N e m
    funext a
    simp only [Matrix.mulVec, dotProduct, Sig_apply, v, Pi.smul_apply, smul_eq_mul]
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : S b = m
    · subst hb
      simp
    · simp [hb]
  have S_bounds : ∀ {N : ℕ} (a : Fin N → Fin 3), -(N : ℤ) ≤ S a ∧ S a ≤ N := by
    intro N a
    have h : ∀ x : Fin 3, -1 ≤ ht x ∧ ht x ≤ 1 := by decide
    constructor
    · have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (h (a i)).1
      simpa [S] using this
    · have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (h (a i)).2
      simpa [S] using this
  have count_pos : ∀ {N : ℕ} (m : ℤ) (h1 : -(N : ℤ) ≤ m) (h2 : m ≤ N), 0 < (Finset.univ.filter fun
      b : Fin N → Fin 3 => S b = m).card := by
    intro N m h1 h2
    apply Finset.card_pos.2
    rcases le_or_gt 0 m with hm | hm
    · refine ⟨fun i => if (i : ℕ) < m.toNat then 0 else 1,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      have : S (fun i : Fin N => if (i : ℕ) < m.toNat then (0 : Fin 3) else 1) =
          ((Finset.univ.filter fun i : Fin N => (i : ℕ) < m.toNat).card : ℤ) := by
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : (i : ℕ) < m.toNat <;> simp [h, ht]
      rw [this, Fin.card_filter_val_lt]
      omega
    · refine ⟨fun i => if (i : ℕ) < (-m).toNat then 2 else 1,
        Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      have : S (fun i : Fin N => if (i : ℕ) < (-m).toNat then (2 : Fin 3) else 1) =
          -((Finset.univ.filter fun i : Fin N => (i : ℕ) < (-m).toNat).card : ℤ) := by
        rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases h : (i : ℕ) < (-m).toNat <;> simp [h, ht]
      rw [this, Fin.card_filter_val_lt]
      omega
  have v_out : ∀ {N : ℕ} (m : ℤ) (h : (N : ℤ) < m ∨ m < -(N : ℤ)), v N m = 0 := by
    intro N m h
    funext a
    have := S_bounds a
    simp only [v, Pi.zero_apply]
    rw [if_neg]
    omega
  intro N hN
  refine ⟨by rw [Sig_H hN, H_Sig hN], by rw [Sig_H hN, H_Sig hN], fun m h1 h2 => ?_,
    fun m h1 h2 => ?_, ?_, ?_⟩
  · exact ⟨_, Nat.cast_ne_zero.2 (count_pos m h1 h2.le).ne', Sig_v N 1 m⟩
  · refine ⟨_, Nat.cast_ne_zero.2 (count_pos m h1.le h2).ne', ?_⟩
    rw [Sig_v, sub_eq_add_neg]
  · rw [Sig_v, v_out _ (Or.inl (by omega)), smul_zero]
  · rw [Sig_v, v_out _ (Or.inr (by omega)), smul_zero]

end D5.S3.Quantum.Dynamics.PronkoMotzkinRaisingLowering
