/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: CyclicResolvent for width-three bridge flow. -/

/-
proof_shape: inclusion_injective: bind-only; consumer: LongReservoir.rectId_tensor_injective
escape_witness: inclusion_injective: none
proof_shape: cyclic_resolvent_lemma: content
escape_witness: cyclic_resolvent_lemma: CyclicResolvent.forward_supported_zero
proof_shape: schur_rank: content
escape_witness: schur_rank: CyclicResolvent.forward_supported_zero
admission_basis: escape-witness (schur_rank)
Module content mechanism: forward_supported_zero: cyclic resolvent support and kernel propagation.
Direct frozen dependencies: none on the implementation baseline.
Utility: none; symbolic constructions and proofs for arbitrary dimensions,
not bounded enumeration, a checker, numeric reduction, or a certified instance.
Information-escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14762
-/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
open Matrix Module

open D5.S3.Quantum.TensorNetworks.BridgeGraph.FloorSelectorCycles
open Matrix Module
section

open Finset

private theorem shifted_recurrence_zero (κ : ℚ) (hκ : 0 < κ)
    (i o : ℤ → ℤ) (v z w : ℤ → ℚ)
    (hi : ∀ n, i n = 0 ∨ i n = 1) (ho : ∀ n, o n = 0 ∨ o n = 1)
    (hw : ∀ n, 0 < w n)
    (hr : ∀ n, v n = z n - w n * z (n - 1))
    (hin : ∀ n, i n = 0 → v n = 0)
    (hout : ∀ n, o n = 1 → z n + κ * v n = 0)
    (hbal : ∀ a : ℤ, ∀ len : ℕ,
      (∑ t ∈ range len, (i (a + t) - o (a + t))) ≤ 1)
    (L : ℕ) (hL : 0 < L) (hperiod : ∀ n, z (n + L) = z n)
    (hwhole : ∀ a : ℤ, (∑ t ∈ range L, (i (a + t) - o (a + t))) ≤ 0)
    (hproduct : ∀ a : ℤ, (∏ t ∈ range L, w (a + t + 1)) < 1) :
    ∀ a, z a = 0 := by
  let c : ℤ → ℚ := fun n => (if o n = 1 then κ / (κ + 1) else 1) * w n
  have hq : 0 < κ / (κ + 1) := div_pos hκ (by linarith)
  apply balanced_cycle_zero i o z c hi ho (L := L)
  · intro n heq
    rcases ho n with hO | hO
    · have hI : i n = 0 := heq.trans hO
      have hv := hin n hI
      have h := hr n
      dsimp [c]
      simp only [hO, zero_ne_one, ↓reduceIte, one_mul]
      linarith
    · have ho' := hout n hO
      have hr' := hr n
      dsimp [c]
      simp only [hO, ↓reduceIte]
      rw [mul_assoc, div_mul_eq_mul_div]
      apply (eq_div_iff (by linarith : κ + 1 ≠ 0)).mpr
      nlinarith
  · intro n
    dsimp [c]
    split_ifs
    · exact (mul_pos hq (hw n)).ne'
    · simpa using (hw n).ne'
  · intro n hI hO
    have hv := hin n hI
    have ho' := hout n hO
    have hr' := hr n
    have hz : z n = 0 := by nlinarith
    refine ⟨hz, ?_⟩
    have h : w n * z (n - 1) = 0 := by linarith
    exact (mul_eq_zero.mp h).resolve_left (hw n).ne'
  · exact hbal
  · exact hL
  · exact hperiod
  · exact hwhole
  · intro a
    exact lt_of_le_of_lt (common_node_product_bound κ hκ o w hw a L) (hproduct a)

private theorem homogeneous_periodic_zero (z w : ℤ → ℚ) (L : ℕ)
    (hperiod : ∀ n, z (n + L) = z n)
    (hr : ∀ n, z n = w n * z (n - 1))
    (hproduct : ∀ a : ℤ, (∏ t ∈ range L, w (a + t + 1)) < 1) :
    ∀ a, z a = 0 := by
  intro a
  have hrec : ∀ t < L, z (a + (t + 1 : ℕ)) = w (a + t + 1) * z (a + t) := by
    intro t ht
    have h := hr (a + t + 1)
    have he : (a + t + 1 - 1 : ℤ) = a + t := by ring
    rw [he] at h
    simpa [Nat.cast_add, add_assoc] using h
  have h := recurrence_product_bounded (fun t => z (a + t)) (fun t => w (a + t + 1)) L hrec
  simp only [Nat.cast_zero, add_zero, hperiod] at h
  exact monodromy_forces_zero _ _ (hproduct a) h

end
section

end
section

open Finset Matrix

private theorem reservoir_eq_one_sub (A G : ℕ) :
    reservoir A G = 1 - kronecker (backward A) (forwardHalf G) := by
  ext i j
  simp [reservoir, Matrix.kronecker_apply, sub_eq_add_neg]

private theorem reservoir_mulVec_orbit (A G : ℕ) (hA : 0 < A) (hG : 0 < G)
    (z : Fin A × Fin G → ℚ) (a b s : ℤ) :
    (reservoir A G).mulVec z (orbit A G hA hG a b s) =
      z (orbit A G hA hG a b s) - edge G hG (b + s) *
        z (orbit A G hA hG a b (s - 1)) := by
  rw [reservoir_eq_one_sub, Matrix.sub_mulVec, Matrix.one_mulVec]
  exact congrArg (fun x => z (orbit A G hA hG a b s) - x)
    (tensor_mulVec_orbit A G hA hG z a b s)

private theorem reservoir_isUnit (A G : ℕ) (hA : 0 < A) (hG : 0 < G) :
    IsUnit (reservoir A G) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  apply (injective_iff_map_eq_zero (reservoir A G).mulVecLin).mpr
  intro z hz
  funext x
  let a : ℤ := x.1.val
  let b : ℤ := x.2.val
  have hr : ∀ s, z (orbit A G hA hG a b s) = edge G hG (b + s) *
      z (orbit A G hA hG a b (s - 1)) := by
    intro s
    have h := congrFun hz (orbit A G hA hG a b s)
    change (reservoir A G).mulVec z (orbit A G hA hG a b s) = 0 at h
    rw [reservoir_mulVec_orbit] at h
    exact sub_eq_zero.mp h
  have hp : ∀ n, z (orbit A G hA hG a b (n + (A * G : ℕ))) =
      z (orbit A G hA hG a b n) := by
    intro n
    rw [Nat.cast_mul, orbit_period]
  have hw : ∀ c : ℤ, (∏ t ∈ range (A * G), edge G hG (b + (c + t + 1))) < 1 := by
    intro c
    simpa [add_assoc] using tensor_edge_product_lt_one A G hA hG (b + c)
  have h := homogeneous_periodic_zero (fun s => z (orbit A G hA hG a b s))
    (fun s => edge G hG (b + s)) (A * G) hp hr hw 0
  simpa [orbit, a, b] using h

end
section

open Finset Matrix

private def selectIndex (A B : ℕ) (hB : 0 < B) (hBA : B ≤ A) (k : Fin B) : Fin A :=
  ⟨k.val * A / B, by
    apply (Nat.div_lt_iff_lt_mul hB).mpr
    have hA : 0 < A := lt_of_lt_of_le hB hBA
    nlinarith [k.isLt]⟩

private theorem selectIndex_injective (A B : ℕ) (hB : 0 < B) (hBA : B ≤ A) :
    Function.Injective (selectIndex A B hB hBA) := by
  intro k l he
  have hq : k.val * A / B = l.val * A / B := congrArg Fin.val he
  have hk₁ := Nat.div_mul_le_self (k.val * A) B
  have hk₂ := Nat.lt_mul_div_succ (k.val * A) hB
  have hl₁ := Nat.div_mul_le_self (l.val * A) B
  have hl₂ := Nat.lt_mul_div_succ (l.val * A) hB
  rw [← hq] at hl₁ hl₂
  apply Fin.ext
  rcases lt_trichotomy k.val l.val with h | h | h
  · have hm : (k.val + 1) * A ≤ l.val * A := Nat.mul_le_mul_right A (by omega)
    nlinarith
  · exact h
  · have hm : (l.val + 1) * A ≤ k.val * A := Nat.mul_le_mul_right A (by omega)
    nlinarith

def inclusion {m n : Type*} [DecidableEq m] (e : n → m) : Matrix m n ℚ :=
  (1 : Matrix m m ℚ).submatrix id e

private theorem inclusion_at {m n : Type*} [Fintype n] [DecidableEq m]
    (e : n → m) (he : Function.Injective e) (u : n → ℚ) (y : n) :
    (inclusion e).mulVec u (e y) = u y := by
  classical
  change (∑ x, (if e y = e x then (1 : ℚ) else 0) * u x) = u y
  simp [he.eq_iff]

private theorem inclusion_support {m n : Type*} [Fintype n] [DecidableEq m]
    (e : n → m) (u : n → ℚ) (x : m) (hx : ¬ ∃ y, x = e y) :
    (inclusion e).mulVec u x = 0 := by
  change (∑ y, (if x = e y then (1 : ℚ) else 0) * u y) = 0
  apply sum_eq_zero
  intro y hy
  simp [show x ≠ e y from fun h => hx ⟨y, h⟩]

private theorem observation_at {m n : Type*} [Fintype m] [DecidableEq m]
    (e : n → m) (z : m → ℚ) (y : n) :
    ((inclusion e).transpose).mulVec z y = z (e y) := by
  change (∑ x, (if x = e y then (1 : ℚ) else 0) * z x) = z (e y)
  simp

private def inputIndex (A G D : ℕ) (hD : 0 < D) (hDG : D ≤ G) :
    Fin A × Fin D → Fin A × Fin G :=
  fun x => (x.1, selectIndex G D hD hDG x.2)

private def outputIndex (A B G : ℕ) (hB : 0 < B) (hBA : B ≤ A) :
    Fin B × Fin G → Fin A × Fin G :=
  fun x => (selectIndex A B hB hBA x.1, x.2)

private theorem inputIndex_injective (A G D : ℕ) (hD : 0 < D) (hDG : D ≤ G) :
    Function.Injective (inputIndex A G D hD hDG) := by
  intro x y h
  refine Prod.ext ?_ ?_
  · exact congrArg (fun u : Fin A × Fin G => u.1) h
  · exact selectIndex_injective G D hD hDG (congrArg (fun u : Fin A × Fin G => u.2) h)

private theorem outputIndex_injective (A B G : ℕ) (hB : 0 < B) (hBA : B ≤ A) :
    Function.Injective (outputIndex A B G hB hBA) := by
  intro x y h
  refine Prod.ext ?_ ?_
  · exact selectIndex_injective A B hB hBA (congrArg (fun u : Fin A × Fin G => u.1) h)
  · exact congrArg (fun u : Fin A × Fin G => u.2) h

private theorem input_matrix (A G D : ℕ) (hD : 0 < D) (hDG : D ≤ G) :
    kronecker (1 : Matrix (Fin A) (Fin A) ℚ) ((rowSelector G D).transpose) =
      inclusion (inputIndex A G D hD hDG) := by
  ext x y
  change ((if x.1 = y.1 then (1 : ℚ) else 0) *
    (if x.2.val = y.2.val * G / D then 1 else 0)) =
    (if x = (y.1, selectIndex G D hD hDG y.2) then 1 else 0)
  simp only [Prod.ext_iff, Fin.ext_iff, selectIndex]
  split_ifs <;> simp_all

private theorem output_matrix (A B G : ℕ) (hB : 0 < B) (hBA : B ≤ A) :
    kronecker (rowSelector A B) (1 : Matrix (Fin G) (Fin G) ℚ) =
      (inclusion (outputIndex A B G hB hBA)).transpose := by
  ext x y
  change ((if y.1.val = x.1.val * A / B then (1 : ℚ) else 0) *
    (if x.2 = y.2 then 1 else 0)) =
    (if y = (selectIndex A B hB hBA x.1, x.2) then 1 else 0)
  simp only [Prod.ext_iff, Fin.ext_iff, selectIndex]
  split_ifs <;> simp_all

end
section

open Finset Matrix

private theorem forward_supported_zero (A B G D : ℕ) (hB : 0 < B) (hBA : B ≤ A)
    (hD : 0 < D) (hDG : D ≤ G) (κ : ℚ) (hκ : 0 < κ)
    (hdim : A * D ≤ B * G) (v z : Fin A × Fin G → ℚ)
    (hr : (reservoir A G).mulVec z = v)
    (hin : ∀ x, (¬ ∃ h : Fin D, x.2.val = h.val * G / D) → v x = 0)
    (hout : ∀ x, (∃ k : Fin B, x.1.val = k.val * A / B) → z x + κ * v x = 0) :
    z = 0 := by
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hG : 0 < G := lt_of_lt_of_le hD hDG
  have hAQ : (0 : ℚ) < A := by exact_mod_cast hA
  have hGQ : (0 : ℚ) < G := by exact_mod_cast hG
  have hρI0 : (0 : ℚ) ≤ (D : ℚ) / G := by positivity
  have hρO0 : (0 : ℚ) ≤ (B : ℚ) / A := by positivity
  have hρI1 : (D : ℚ) / G ≤ 1 := (div_le_one hGQ).mpr (by exact_mod_cast hDG)
  have hρO1 : (B : ℚ) / A ≤ 1 := (div_le_one hAQ).mpr (by exact_mod_cast hBA)
  have hρ : (D : ℚ) / G ≤ (B : ℚ) / A := by
    apply (div_le_div_iff₀ hGQ hAQ).mpr
    have hd : (A : ℚ) * D ≤ (B : ℚ) * G := by exact_mod_cast hdim
    nlinarith
  funext x
  let a : ℤ := x.1.val
  let b : ℤ := x.2.val
  let i : ℤ → ℤ := fun s => jump ((D : ℚ) / G) (b + s)
  let o : ℤ → ℤ := fun s => jump ((B : ℚ) / A) (a - s)
  let v' : ℤ → ℚ := fun s => v (orbit A G hA hG a b s)
  let z' : ℤ → ℚ := fun s => z (orbit A G hA hG a b s)
  let w : ℤ → ℚ := fun s => edge G hG (b + s)
  have hi : ∀ s, i s = 0 ∨ i s = 1 := fun s => jump_zero_or_one hρI0 hρI1 _
  have ho : ∀ s, o s = 0 ∨ o s = 1 := fun s => jump_zero_or_one hρO0 hρO1 _
  have hr' : ∀ s, v' s = z' s - w s * z' (s - 1) := by
    intro s
    have h := congrFun hr (orbit A G hA hG a b s)
    rw [reservoir_mulVec_orbit] at h
    exact h.symm
  have hin' : ∀ s, i s = 0 → v' s = 0 := by
    intro s hs
    apply hin
    intro hh
    have hj := (jump_one_iff_fin_selector G D hD hDG
      (orbit A G hA hG a b s).2).mpr hh
    change jump ((D : ℚ) / G) (index G hG (b + s)).val = 1 at hj
    rw [jump_index] at hj
    change i s = 1 at hj
    omega
  have hout' : ∀ s, o s = 1 → z' s + κ * v' s = 0 := by
    intro s hs
    apply hout
    apply (jump_one_iff_fin_selector A B hB hBA (orbit A G hA hG a b s).1).mp
    change jump ((B : ℚ) / A) (index A hA (a - s)).val = 1
    rw [jump_index]
    exact hs
  have hbal : ∀ c : ℤ, ∀ len : ℕ, (∑ t ∈ range len, (i (c + t) - o (c + t))) ≤ 1 := by
    intro c len
    simpa [i, o, sub_add_eq_sub_sub, add_assoc] using
      opposite_direction_excess hρ (b + c) (a - c) len
  have hp : ∀ n, z' (n + (A * G : ℕ)) = z' n := by
    intro n
    dsimp [z']
    rw [orbit_period]
  have hwhole : ∀ c : ℤ, (∑ t ∈ range (A * G), (i (c + t) - o (c + t))) ≤ 0 := by
    intro c
    have he := whole_tensor_excess A B G D hA hG (b + c) (a - c)
    have hd : ((A * D : ℕ) : ℤ) - (G * B : ℕ) ≤ 0 := by
      have : A * D ≤ G * B := by simpa [mul_comm] using hdim
      have hd' : ((A * D : ℕ) : ℤ) ≤ (G * B : ℕ) := by exact_mod_cast this
      omega
    calc
      _ = ((A * D : ℕ) : ℤ) - (G * B : ℕ) := by
        simpa only [i, o, sub_add_eq_sub_sub, add_assoc] using he
      _ ≤ 0 := hd
  have hwprod : ∀ c : ℤ, (∏ t ∈ range (A * G), w (c + t + 1)) < 1 := by
    intro c
    simpa [w, add_assoc] using tensor_edge_product_lt_one A G hA hG (b + c)
  have hzero := shifted_recurrence_zero κ hκ i o v' z' w hi ho
    (fun s => edge_pos G hG _) hr' hin' hout' hbal (A * G) (Nat.mul_pos hA hG) hp hwhole hwprod
  have h := hzero 0
  simpa [z', orbit, a, b] using h

end
section

open Finset Matrix

private noncomputable def restrictedResolvent {m n p : Type*} [Fintype m] [DecidableEq m]
    (R : Matrix m m ℚ) (κ : ℚ) (ein : n → m) (eout : p → m) : Matrix p n ℚ :=
  (inclusion eout).transpose * (κ • 1 + R⁻¹) * inclusion ein

private theorem schur_eq_restricted (A B G D : ℕ) (hB : 0 < B) (hBA : B ≤ A)
    (hD : 0 < D) (hDG : D ≤ G) (κ : ℚ) :
    schurMap A B G D κ = restrictedResolvent (reservoir A G) κ
      (inputIndex A G D hD hDG) (outputIndex A B G hB hBA) := by
  unfold schurMap restrictedResolvent
  rw [← input_matrix, ← output_matrix]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hm := Matrix.mul_kronecker_mul (rowSelector A B)
    (1 : Matrix (Fin A) (Fin A) ℚ) (1 : Matrix (Fin G) (Fin G) ℚ) ((rowSelector G D).transpose)
  simp only [Matrix.mul_one, Matrix.one_mul] at hm
  simp only [Matrix.kronecker]
  rw [← hm]

theorem inclusion_injective {m n : Type*} [Fintype n] [DecidableEq m]
    (e : n → m) (he : Function.Injective e) : Function.Injective (inclusion e).mulVec := by
  intro u v h
  funext y
  have h' := congrFun h (e y)
  simpa only [inclusion_at e he] using h'

private theorem restricted_kernel_equations {m n p : Type*}
    [Fintype m] [Fintype n] [DecidableEq m]
    (R : Matrix m m ℚ) (hR : IsUnit R) (κ : ℚ) (ein : n → m) (eout : p → m)
    (u : n → ℚ) (hu : (restrictedResolvent R κ ein eout).mulVec u = 0) :
    let v := (inclusion ein).mulVec u
    let z := R⁻¹.mulVec v
    R.mulVec z = v ∧ (∀ y, z (eout y) + κ * v (eout y) = 0) := by
  dsimp
  constructor
  · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv R (R.isUnit_iff_isUnit_det.mp hR),
      Matrix.one_mulVec]
  · intro y
    have h := congrFun hu y
    unfold restrictedResolvent at h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, observation_at] at h
    change κ * (inclusion ein).mulVec u (eout y) +
      R⁻¹.mulVec ((inclusion ein).mulVec u) (eout y) = 0 at h
    linarith

private theorem schur_injective (A B G D : ℕ) (hB : 0 < B) (hBA : B ≤ A)
    (hD : 0 < D) (hDG : D ≤ G) (κ : ℚ) (hκ : 0 < κ)
    (hdim : A * D ≤ B * G) : Function.Injective (schurMap A B G D κ).mulVec := by
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hG : 0 < G := lt_of_lt_of_le hD hDG
  rw [schur_eq_restricted A B G D hB hBA hD hDG]
  apply (injective_iff_map_eq_zero
    (restrictedResolvent (reservoir A G) κ (inputIndex A G D hD hDG)
      (outputIndex A B G hB hBA)).mulVecLin).mpr
  intro u hu
  let ein := inputIndex A G D hD hDG
  let eout := outputIndex A B G hB hBA
  let v := (inclusion ein).mulVec u
  let z := (reservoir A G)⁻¹.mulVec v
  have heq := restricted_kernel_equations (reservoir A G) (reservoir_isUnit A G hA hG)
    κ ein eout u hu
  have hz : z = 0 := by
    apply forward_supported_zero A B G D hB hBA hD hDG κ hκ hdim v z heq.1
    · intro x hx
      apply inclusion_support
      rintro ⟨y, hy⟩
      apply hx
      exact ⟨y.2, congrArg (fun q : Fin A × Fin G => q.2.val) hy⟩
    · intro x hx
      rcases hx with ⟨k, hk⟩
      have hx' : x = eout (k, x.2) := by
        apply Prod.ext
        · exact Fin.ext hk
        · rfl
      rw [hx']
      exact heq.2 _
  have hv : v = 0 := by
    have hrz : (reservoir A G).mulVec z = v := heq.1
    rw [hz, Matrix.mulVec_zero] at hrz
    exact hrz.symm
  apply inclusion_injective ein (inputIndex_injective A G D hD hDG)
  simpa [v] using hv

end
section

open Finset Matrix

private theorem succ_pred_relation (N : ℕ) (hN : 0 < N) (x y : Fin N) :
    x.val = (y.val + 1) % N ↔ y.val = (x.val + N - 1) % N := by
  have hn : 0 < (N : ℤ) := by exact_mod_cast hN
  have hx : index N hN (x.val : ℤ) = x := index_nat N hN x
  have hy : index N hN (y.val : ℤ) = y := index_nat N hN y
  have hadd := index_add_one N hN (y.val : ℤ)
  rw [hy] at hadd
  have hsub := index_sub_one N hN (x.val : ℤ)
  rw [hx] at hsub
  constructor
  · intro h
    have he : index N hN ((y.val : ℤ) + 1) = x := Fin.ext (hadd.trans h.symm)
    have he' := congrArg (fun u : Fin N => index N hN ((u.val : ℤ) - 1)) he
    have hcan : index N hN (((index N hN ((y.val : ℤ) + 1)).val : ℤ) - 1) = y := by
      apply Fin.ext
      apply Int.natCast_inj.mp
      simp only [index_val_int, Int.emod_sub_emod]
      simp only [add_sub_cancel_right]
      exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast y.isLt)
    rw [hcan] at he'
    exact (congrArg Fin.val he').trans hsub
  · intro h
    have he : index N hN ((x.val : ℤ) - 1) = y := Fin.ext (hsub.trans h.symm)
    have he' := congrArg (fun u : Fin N => index N hN ((u.val : ℤ) + 1)) he
    have hcan : index N hN (((index N hN ((x.val : ℤ) - 1)).val : ℤ) + 1) = x := by
      apply Fin.ext
      apply Int.natCast_inj.mp
      simp only [index_val_int, Int.emod_add_emod]
      simp only [sub_add_cancel]
      exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast x.isLt)
    rw [hcan] at he'
    exact (congrArg Fin.val he').trans hadd

private def reverseOrbit (A G : ℕ) (hA : 0 < A) (hG : 0 < G) (a b s : ℤ) : Fin A × Fin G :=
  (index A hA (a + s), index G hG (b - s))

private theorem reverseOrbit_period (A G : ℕ) (hA : 0 < A) (hG : 0 < G) (a b s : ℤ) :
    reverseOrbit A G hA hG a b (s + A * G) = reverseOrbit A G hA hG a b s := by
  apply Prod.ext
  · change index A hA (a + (s + A * G)) = index A hA (a + s)
    have he : (a + (s + A * G) : ℤ) = a + s + G * A := by ring
    rw [he, index_add_multiple]
  · change index G hG (b - (s + A * G)) = index G hG (b - s)
    have he : (b - (s + A * G) : ℤ) = b - s + (-A) * G := by ring
    rw [he, index_add_multiple]

private theorem transpose_tensor_mulVec_orbit (A G : ℕ) (hA : 0 < A) (hG : 0 < G)
    (z : Fin A × Fin G → ℚ) (a b s : ℤ) :
    (kronecker (backward A) (forwardHalf G)).transpose.mulVec z
      (reverseOrbit A G hA hG a b s) =
      edge G hG (b - s + 1) * z (reverseOrbit A G hA hG a b (s - 1)) := by
  let x := reverseOrbit A G hA hG a b s
  let y := reverseOrbit A G hA hG a b (s - 1)
  have hi : y.1.val = (x.1.val + A - 1) % A := by
    dsimp [x, y, reverseOrbit]
    have he : a + (s - 1) = (a + s) - 1 := by ring
    rw [he, index_sub_one]
  have hj : y.2.val = (x.2.val + 1) % G := by
    dsimp [x, y, reverseOrbit]
    have he : b - (s - 1) = (b - s) + 1 := by ring
    rw [he, index_add_one]
  have hi' : x.1.val = (y.1.val + 1) % A := (succ_pred_relation A hA x.1 y.1).mpr hi
  have hj' : x.2.val = (y.2.val + G - 1) % G := (succ_pred_relation G hG y.2 x.2).mp hj
  change (∑ t : Fin A × Fin G, (backward A t.1 x.1 * forwardHalf G t.2 x.2) * z t) =
    edge G hG (b - s + 1) * z y
  rw [sum_eq_single y]
  · simp only [backward_apply, forwardHalf_apply, hi', hj', ↓reduceIte, one_mul]
    have he : y.2 = index G hG (b - s + 1) := by
      dsimp [y, reverseOrbit]
      congr 1
      ring
    rw [he]
    rfl
  · intro t ht hty
    have hcoords : t.1.val ≠ y.1.val ∨ t.2.val ≠ y.2.val := by
      by_contra h
      push Not at h
      exact hty (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
    rcases hcoords with h | h
    · have h' : x.1.val ≠ (t.1.val + 1) % A := by
        intro he
        have := (succ_pred_relation A hA x.1 t.1).mp he
        rw [← hi] at this
        exact h this
      simp [backward_apply, h']
    · have h' : x.2.val ≠ (t.2.val + G - 1) % G := by
        intro he
        have := (succ_pred_relation G hG t.2 x.2).mpr he
        rw [← hj] at this
        exact h this
      simp [forwardHalf_apply, h']
  · simp

end
section

open Finset Matrix

private theorem reverse_product_eq (f : ℤ → ℚ) (phase : ℤ) (len : ℕ) :
    (∏ t ∈ range len, f (phase - t)) = ∏ t ∈ range len, f (phase - len + 1 + t) := by
  rw [← prod_range_reflect]
  apply prod_congr rfl
  intro t ht
  congr 1
  have ht' := mem_range.mp ht
  have hcast : ((len - 1 - t : ℕ) : ℤ) = (len : ℤ) - 1 - t := by omega
  rw [hcast]
  ring

private theorem reverse_tensor_edge_product_lt_one (A G : ℕ) (hA : 0 < A) (hG : 0 < G)
    (phase : ℤ) : (∏ t ∈ range (A * G), edge G hG (phase - t)) < 1 := by
  rw [reverse_product_eq]
  rw [edge_product]
  exact half_pow_lt_one hA

private theorem transpose_reservoir_mulVec_orbit (A G : ℕ) (hA : 0 < A) (hG : 0 < G)
    (z : Fin A × Fin G → ℚ) (a b s : ℤ) :
    (reservoir A G).transpose.mulVec z (reverseOrbit A G hA hG a b s) =
      z (reverseOrbit A G hA hG a b s) - edge G hG (b - s + 1) *
        z (reverseOrbit A G hA hG a b (s - 1)) := by
  rw [reservoir_eq_one_sub, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.sub_mulVec, Matrix.one_mulVec]
  exact congrArg (fun x => z (reverseOrbit A G hA hG a b s) - x)
    (transpose_tensor_mulVec_orbit A G hA hG z a b s)

end
section

open Finset Matrix

private theorem reverse_supported_zero (A B G D : ℕ) (hB : 0 < B) (hBA : B ≤ A)
    (hD : 0 < D) (hDG : D ≤ G) (κ : ℚ) (hκ : 0 < κ)
    (hdim : B * G ≤ A * D) (v z : Fin A × Fin G → ℚ)
    (hr : (reservoir A G).transpose.mulVec z = v)
    (hin : ∀ x, (¬ ∃ k : Fin B, x.1.val = k.val * A / B) → v x = 0)
    (hout : ∀ x, (∃ h : Fin D, x.2.val = h.val * G / D) → z x + κ * v x = 0) :
    z = 0 := by
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hG : 0 < G := lt_of_lt_of_le hD hDG
  have hAQ : (0 : ℚ) < A := by exact_mod_cast hA
  have hGQ : (0 : ℚ) < G := by exact_mod_cast hG
  have hρI0 : (0 : ℚ) ≤ (B : ℚ) / A := by positivity
  have hρO0 : (0 : ℚ) ≤ (D : ℚ) / G := by positivity
  have hρI1 : (B : ℚ) / A ≤ 1 := (div_le_one hAQ).mpr (by exact_mod_cast hBA)
  have hρO1 : (D : ℚ) / G ≤ 1 := (div_le_one hGQ).mpr (by exact_mod_cast hDG)
  have hρ : (B : ℚ) / A ≤ (D : ℚ) / G := by
    apply (div_le_div_iff₀ hAQ hGQ).mpr
    have hd : (B : ℚ) * G ≤ (A : ℚ) * D := by exact_mod_cast hdim
    nlinarith
  funext x
  let a : ℤ := x.1.val
  let b : ℤ := x.2.val
  let i : ℤ → ℤ := fun s => jump ((B : ℚ) / A) (a + s)
  let o : ℤ → ℤ := fun s => jump ((D : ℚ) / G) (b - s)
  let v' : ℤ → ℚ := fun s => v (reverseOrbit A G hA hG a b s)
  let z' : ℤ → ℚ := fun s => z (reverseOrbit A G hA hG a b s)
  let w : ℤ → ℚ := fun s => edge G hG (b - s + 1)
  have hi : ∀ s, i s = 0 ∨ i s = 1 := fun s => jump_zero_or_one hρI0 hρI1 _
  have ho : ∀ s, o s = 0 ∨ o s = 1 := fun s => jump_zero_or_one hρO0 hρO1 _
  have hr' : ∀ s, v' s = z' s - w s * z' (s - 1) := by
    intro s
    have h := congrFun hr (reverseOrbit A G hA hG a b s)
    rw [transpose_reservoir_mulVec_orbit] at h
    exact h.symm
  have hin' : ∀ s, i s = 0 → v' s = 0 := by
    intro s hs
    apply hin
    intro hh
    have hj := (jump_one_iff_fin_selector A B hB hBA
      (reverseOrbit A G hA hG a b s).1).mpr hh
    change jump ((B : ℚ) / A) (index A hA (a + s)).val = 1 at hj
    rw [jump_index] at hj
    change i s = 1 at hj
    omega
  have hout' : ∀ s, o s = 1 → z' s + κ * v' s = 0 := by
    intro s hs
    apply hout
    apply (jump_one_iff_fin_selector G D hD hDG (reverseOrbit A G hA hG a b s).2).mp
    change jump ((D : ℚ) / G) (index G hG (b - s)).val = 1
    rw [jump_index]
    exact hs
  have hbal : ∀ c : ℤ, ∀ len : ℕ, (∑ t ∈ range len, (i (c + t) - o (c + t))) ≤ 1 := by
    intro c len
    simpa [i, o, sub_add_eq_sub_sub, add_assoc] using
      opposite_direction_excess hρ (a + c) (b - c) len
  have hp : ∀ n, z' (n + (A * G : ℕ)) = z' n := by
    intro n
    dsimp [z']
    rw [reverseOrbit_period]
  have hwhole : ∀ c : ℤ, (∑ t ∈ range (A * G), (i (c + t) - o (c + t))) ≤ 0 := by
    intro c
    have he := whole_tensor_excess G D A B hG hA (a + c) (b - c)
    have hd : ((G * B : ℕ) : ℤ) - (A * D : ℕ) ≤ 0 := by
      have hd' : ((G * B : ℕ) : ℤ) ≤ (A * D : ℕ) := by
        exact_mod_cast (show G * B ≤ A * D by simpa [mul_comm] using hdim)
      omega
    calc
      _ = ((G * B : ℕ) : ℤ) - (A * D : ℕ) := by
        simpa only [i, o, sub_add_eq_sub_sub, add_assoc, mul_comm] using he
      _ ≤ 0 := hd
  have hwprod : ∀ c : ℤ, (∏ t ∈ range (A * G), w (c + t + 1)) < 1 := by
    intro c
    have he : (∏ t ∈ range (A * G), w (c + t + 1)) =
        ∏ t ∈ range (A * G), edge G hG ((b - c) - t) := by
      apply prod_congr rfl
      intro t ht
      dsimp [w]
      congr 1
      ring
    rw [he]
    exact reverse_tensor_edge_product_lt_one A G hA hG (b - c)
  have hzero := shifted_recurrence_zero κ hκ i o v' z' w hi ho
    (fun s => edge_pos G hG _) hr' hin' hout' hbal (A * G) (Nat.mul_pos hA hG) hp hwhole hwprod
  have h := hzero 0
  simpa [z', reverseOrbit, a, b] using h

end
section

open Matrix Module

private theorem surjective_of_transpose_injective {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℚ) (h : Function.Injective M.transpose.mulVec) :
    Function.Surjective M.mulVec := by
  have hr : M.rank = Fintype.card m := by
    rw [← Matrix.rank_transpose M, Matrix.rank]
    have hi : Function.Injective M.transpose.mulVecLin := h
    rw [LinearMap.finrank_range_of_inj hi, Module.finrank_pi]
  apply (LinearMap.range_eq_top (f := M.mulVecLin)).mp
  apply Submodule.eq_top_of_finrank_eq
  change M.rank = Module.finrank ℚ (m → ℚ)
  simpa using hr

end
section

open Matrix

private theorem transpose_restrictedResolvent {m n p : Type*} [Fintype m] [DecidableEq m]
    (R : Matrix m m ℚ) (κ : ℚ) (ein : n → m) (eout : p → m) :
    (restrictedResolvent R κ ein eout).transpose =
      restrictedResolvent R.transpose κ eout ein := by
  unfold restrictedResolvent
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_add,
    Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_nonsing_inv]
  simp only [ Matrix.transpose_transpose, Matrix.mul_assoc]

private theorem schur_transpose_injective (A B G D : ℕ) (hB : 0 < B) (hBA : B ≤ A)
    (hD : 0 < D) (hDG : D ≤ G) (κ : ℚ) (hκ : 0 < κ)
    (hdim : B * G ≤ A * D) : Function.Injective (schurMap A B G D κ).transpose.mulVec := by
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hG : 0 < G := lt_of_lt_of_le hD hDG
  rw [schur_eq_restricted A B G D hB hBA hD hDG, transpose_restrictedResolvent]
  apply (injective_iff_map_eq_zero
    (restrictedResolvent (reservoir A G).transpose κ (outputIndex A B G hB hBA)
      (inputIndex A G D hD hDG)).mulVecLin).mpr
  intro u hu
  let ein := outputIndex A B G hB hBA
  let eout := inputIndex A G D hD hDG
  let v := (inclusion ein).mulVec u
  let z := ((reservoir A G).transpose)⁻¹.mulVec v
  have hR : IsUnit (reservoir A G).transpose := by
    simpa only [Matrix.isUnit_transpose] using reservoir_isUnit A G hA hG
  have heq := restricted_kernel_equations (reservoir A G).transpose hR κ ein eout u hu
  have hz : z = 0 := by
    apply reverse_supported_zero A B G D hB hBA hD hDG κ hκ hdim v z heq.1
    · intro x hx
      apply inclusion_support
      rintro ⟨y, hy⟩
      apply hx
      exact ⟨y.1, congrArg (fun q : Fin A × Fin G => q.1.val) hy⟩
    · intro x hx
      rcases hx with ⟨h, hh⟩
      have hx' : x = eout (x.1, h) := by
        apply Prod.ext
        · rfl
        · exact Fin.ext hh
      rw [hx']
      exact heq.2 _
  have hv : v = 0 := by
    have hrz : (reservoir A G).transpose.mulVec z = v := heq.1
    rw [hz, Matrix.mulVec_zero] at hrz
    exact hrz.symm
  apply inclusion_injective ein (outputIndex_injective A B G hB hBA)
  simpa [v] using hv

private theorem schur_surjective (A B G D : ℕ) (hB : 0 < B) (hBA : B ≤ A)
    (hD : 0 < D) (hDG : D ≤ G) (κ : ℚ) (hκ : 0 < κ)
    (hdim : B * G ≤ A * D) : Function.Surjective (schurMap A B G D κ).mulVec := by
  exact surjective_of_transpose_injective _
    (schur_transpose_injective A B G D hB hBA hD hDG κ hκ hdim)

end
section

open Matrix Module

theorem cyclic_resolvent_lemma : CyclicResolventLemma := by
  intro A B G D hB hBA hD hDG κ hκ
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hG : 0 < G := lt_of_lt_of_le hD hDG
  refine ⟨reservoir_isUnit A G hA hG, ?_, ?_⟩
  · exact schur_injective A B G D hB hBA hD hDG κ hκ
  · exact schur_surjective A B G D hB hBA hD hDG κ hκ

theorem schur_rank (A B G D : ℕ) (hB : 0 < B) (hBA : B ≤ A)
    (hD : 0 < D) (hDG : D ≤ G) (κ : ℚ) (hκ : 0 < κ) :
    (schurMap A B G D κ).rank = min (A * D) (B * G) := by
  rcases le_total (A * D) (B * G) with hdim | hdim
  · rw [min_eq_left hdim, Matrix.rank]
    have hi : Function.Injective (schurMap A B G D κ).mulVecLin :=
      schur_injective A B G D hB hBA hD hDG κ hκ hdim
    rw [LinearMap.finrank_range_of_inj hi]
    simp
  · rw [min_eq_right hdim, Matrix.rank]
    have hs : Function.Surjective (schurMap A B G D κ).mulVecLin :=
      schur_surjective A B G D hB hBA hD hDG κ hκ hdim
    rw [LinearMap.range_eq_top.mpr hs]
    simp

end

end D5.S3.Quantum.TensorNetworks.BridgeGraph.CyclicResolvent
