/- GID: D5/S3/Quantum/Entanglement/CarrozzaChevrierLionniIrreducibilityWIP
   generality: I
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:stage-a-open)
   anchors: []
   utility: none
   digest: Prime singleton ranks and rank-one leg stripping exclude proper-support factors. -/

import D5.S3.Quantum.Entanglement.CarrozzaChevrierLionniConverseWIP
import D5.S3.Quantum.Entanglement.CarrozzaChevrierLionniCutRanksWIP

/-! The obstruction to a proper-support product decomposition of the cluster state. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.CarrozzaChevrierLionniIrreducibilityWIP

open Matrix Module
open CarrozzaChevrierLionniCutRanksWIP
open CarrozzaChevrierLionniConverseWIP (Bits cluster clusterState prime_singleton_stripping)
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (productMap)

private theorem rectangular_outer {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (hA : A.rank ≤ 1) :
    ∃ u : m → ℂ, ∃ v : n → ℂ, A = vecMulVec u v := by
  classical
  obtain ⟨u, hu⟩ := (finrank_le_one_iff (K := ℂ)
    (V := LinearMap.range A.mulVecLin)).mp hA
  have hcol (j : n) : A.col j ∈ LinearMap.range A.mulVecLin :=
    ⟨Pi.single j 1, A.mulVec_single_one j⟩
  choose v hv using fun j => hu ⟨A.col j, hcol j⟩
  refine ⟨u.val, v, ?_⟩
  ext i j
  have h := congrArg (fun z : LinearMap.range A.mulVecLin => z.val i) (hv j)
  simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
    vecMulVec_apply, mul_comm] using h.symm

section Stripping

variable {I : Type} [Fintype I] [DecidableEq I]
variable {d : I → Type} [∀ i, Fintype (d i)]
variable (ψ : (∀ i, d i) → ℂ)

private theorem strip_one (base : ∀ i, d i) (hb : ψ base ≠ 0) (i : I)
    (hi : (flatten (· ∈ ({i} : Finset _)) ψ).rank ≤ 1) (z : ∀ i, d i) :
    ψ z = (ψ (Function.update base i (z i)) / ψ base) *
      ψ (Function.update z i (base i)) := by
  obtain ⟨u, v, hv⟩ := rectangular_outer _ hi
  have he (x : ∀ j, d j) :
      ψ x = u (fun j : {j // j ∈ ({i} : Finset I)} => x j) * v (fun j : {j // j ∉ ({i} : Finset I)} => x j) := by
    let E := Equiv.piEquivPiSubtypeProd (· ∈ ({i} : Finset I)) d
    have h := congrFun (congrFun hv (E x).1) (E x).2
    change ψ (E.symm (E x)) = u (E x).1 * v (E x).2 at h
    rw [E.symm_apply_apply] at h
    exact h
  simp only [div_mul_eq_mul_div]
  apply (eq_div_iff hb).mpr
  rw [he z, he base, he (Function.update base i (z i)), he (Function.update z i (base i))]
  have left (x y : ∀ j, d j) :
      (fun j : {j // j ∈ ({i} : Finset I)} => Function.update x i (y i) j) = (fun j : {j // j ∈ ({i} : Finset I)} => y j) := by
    funext j
    obtain ⟨j, hj⟩ := j
    obtain rfl := Finset.mem_singleton.mp hj
    simp
  have right (x y : ∀ j, d j) :
      (fun j : {j // j ∉ ({i} : Finset I)} => Function.update x i (y i) j) = (fun j : {j // j ∉ ({i} : Finset I)} => x j) := by
    funext j
    exact Function.update_of_ne (by simpa using j.property) _ _
  rw [left, left, right, right]
  ring

private def reset (base : ∀ i, d i) (s : Finset I) (z : ∀ i, d i) : ∀ i, d i :=
  fun i => if i ∈ s then base i else z i

private theorem strip_many (base : ∀ i, d i) (hb : ψ base ≠ 0)
    (s : Finset I) (hs : ∀ i ∈ s, (flatten (· ∈ ({i} : Finset _)) ψ).rank ≤ 1) (z : ∀ i, d i) :
    ψ z = (∏ i ∈ s, ψ (Function.update base i (z i)) / ψ base) *
      ψ (reset base s z) := by
  induction s using Finset.induction_on with
  | empty =>
    have h : reset base ∅ z = z := by funext i; simp [reset]
    simp [h]
  | @insert i s hi ih =>
    have hrest : ∀ j ∈ s, (flatten (· ∈ ({j} : Finset I)) ψ).rank ≤ 1 :=
      fun j hj => hs j (Finset.mem_insert_of_mem hj)
    have hreset : Function.update (reset base s z) i (base i) = reset base (insert i s) z := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [reset]
      · simp [reset, Function.update_of_ne hj, Finset.mem_insert, hj]
    calc
      ψ z = (∏ j ∈ s, ψ (Function.update base j (z j)) / ψ base) *
          ψ (reset base s z) := ih hrest
      _ = _ := by
        rw [strip_one ψ base hb i (hs i (Finset.mem_insert_self i s)) (reset base s z), hreset,
          Finset.prod_insert hi]
        simp only [reset, if_neg hi]
        ring

theorem rank_cut_le_one_of_singletons (s : Finset I) (base : ∀ i, d i) (hb : ψ base ≠ 0)
    (hs : ∀ i ∈ s, (flatten (· ∈ ({i} : Finset _)) ψ).rank ≤ 1) :
    (flatten (· ∈ s) ψ).rank ≤ 1 := by
  let u (x : ∀ i : { i // i ∈ s }, d i) :=
    ∏ i : { i // i ∈ s }, ψ (Function.update base i (x i)) / ψ base
  let v (y : ∀ i : { i // i ∉ s }, d i) :=
    ψ ((Equiv.piEquivPiSubtypeProd (· ∈ s) d).symm ((fun i => base i), y))
  have he : flatten (· ∈ s) ψ = vecMulVec u v := by
    ext x y
    let z := (Equiv.piEquivPiSubtypeProd (· ∈ s) d).symm (x, y)
    have hreset : reset base s z =
        (Equiv.piEquivPiSubtypeProd (· ∈ s) d).symm ((fun i => base i), y) := by
      funext i
      by_cases hi : i ∈ s <;> simp [z, reset, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
    change ψ z = u x * v y
    rw [strip_many ψ base hb s hs z, hreset]
    unfold u v
    congr 1
    rw [Finset.prod_subtype s (fun _ => Iff.rfl)
      (fun i => ψ (Function.update base i (z i)) / ψ base)]
    apply Finset.prod_congr rfl
    intro i _
    simp [z, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
  rw [he]
  exact Matrix.rank_vecMulVec_le _ _

/-- Opposite cuts have transposed flattenings. -/
theorem rank_cut_complement (s : Finset I) :
    (flatten (· ∈ sᶜ) ψ).rank = (flatten (· ∈ s) ψ).rank := by
  let l : (∀ i : {i // i ∉ s}, d i) ≃ (∀ i : {i // i ∈ sᶜ}, d i) :=
    ⟨fun x i => x ⟨i, Finset.mem_compl.mp i.property⟩,
      fun x i => x ⟨i, Finset.mem_compl.mpr i.property⟩, fun _ => rfl, fun _ => rfl⟩
  let r : (∀ i : {i // i ∈ s}, d i) ≃ (∀ i : {i // i ∉ sᶜ}, d i) :=
    ⟨fun x i => x ⟨i, by simpa using i.property⟩,
      fun x i => x ⟨i, by simpa using i.property⟩, fun _ => rfl, fun _ => rfl⟩
  have h : (flatten (· ∈ sᶜ) ψ).submatrix l r = (flatten (· ∈ s) ψ)ᵀ := by
    apply Matrix.ext
    intro x y
    apply congrArg ψ
    funext i
    by_cases hi : i ∈ s <;>
      simp [flatten, Equiv.piEquivPiSubtypeProd_symm_apply, hi, l, r]
  rw [← Matrix.rank_submatrix _ l r, h, Matrix.rank_transpose]

end Stripping

private theorem cluster_half_or_zero {z : Bits} (hz : ∃ i, z i = 0) :
    clusterState z = 0 ∨ clusterState z = 1 / 2 := by
  have hneg (hp : z 0 = z 1 ∧ z 2 = z 3) : ¬(z 0 = 1 ∧ z 2 = 1) := by
    rintro ⟨h0, h2⟩
    obtain ⟨i, hi⟩ := hz
    have h1 : z 1 = 1 := hp.1.symm.trans h0
    have h3 : z 3 = 1 := hp.2.symm.trans h2
    have hall : ∀ i : Fin 4, z i = 1 := by
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    exact (by decide : (0 : Fin 2) ≠ 1) (hi.symm.trans (hall i))
  by_cases hp : z 0 = z 1 ∧ z 2 = z 3
  · right
    simp only [clusterState, cluster, if_pos hp, if_neg (hneg hp)]
    norm_num
  · left
    simp only [clusterState, cluster, if_neg hp, Rat.cast_zero]

theorem cluster_cut_rank_ge_two (s : Finset (Fin 4)) (hs : s.Nonempty)
    (ht : ∃ i, i ∉ s) : 2 ≤ (flatten (· ∈ s) clusterState).rank := by
  let F := flatten (· ∈ s) clusterState
  let row (b : Fin 2) : ∀ i : {i // i ∈ s}, Fin 2 := fun _ => b
  let col (b : Fin 2) : ∀ i : {i // i ∉ s}, Fin 2 := fun _ => b
  let M := F.submatrix row col
  let E := Equiv.piEquivPiSubtypeProd (· ∈ s) (fun _ : Fin 4 => Fin 2)
  have hd (b : Fin 2) : E.symm (row b, col b) = fun _ => b := by
    funext i
    by_cases hi : i ∈ s <;> simp [E, row, col, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  have h00 : M 0 0 = 1 / 2 := by
    change clusterState (E.symm (row 0, col 0)) = _
    rw [hd]
    norm_num [clusterState, cluster]
  have h11 : M 1 1 = -(1 / 2) := by
    change clusterState (E.symm (row 1, col 1)) = _
    rw [hd]
    norm_num [clusterState, cluster]
  have h01 : M 0 1 = 0 ∨ M 0 1 = 1 / 2 := by
    change clusterState (E.symm (row 0, col 1)) = _ ∨ _
    apply cluster_half_or_zero
    obtain ⟨i, hi⟩ := hs
    exact ⟨i, by simp [E, row, Equiv.piEquivPiSubtypeProd_symm_apply, hi]⟩
  have h10 : M 1 0 = 0 ∨ M 1 0 = 1 / 2 := by
    change clusterState (E.symm (row 1, col 0)) = _ ∨ _
    apply cluster_half_or_zero
    obtain ⟨i, hi⟩ := ht
    exact ⟨i, by simp [E, col, Equiv.piEquivPiSubtypeProd_symm_apply, hi]⟩
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_fin_two, h00, h11]
    rcases h01 with h | h <;> rcases h10 with g | g <;> norm_num [h, g]
  have hm : M.rank = 2 := by simpa using Matrix.rank_of_det_ne_zero hdet
  calc 2 = M.rank := hm.symm
    _ ≤ F.rank := Matrix.rank_submatrix_le F row col

theorem cluster_singleton_rank (i : Fin 4) : (flatten (· ∈ ({i} : Finset _)) clusterState).rank = 2 := by
  apply le_antisymm
  · refine (Matrix.rank_le_card_height _).trans ?_
    simp [Fintype.card_pi, Fintype.card_coe]
  · apply cluster_cut_rank_ge_two
    · exact Finset.singleton_nonempty _
    · fin_cases i <;> decide

open CarrozzaChevrierLionniConverseWIP (Tensor qubits)

/-- Eq. (9) in finite orthonormal bases, allowing two independent local embeddings. -/
def ReducibleTensor {D : ℕ} {d : Fin D → ℕ} (ψ : Tensor d) : Prop :=
  ∃ (k : ℕ) (S : Fin k → Finset (Fin D)) (dims : Fin k → Fin D → ℕ)
    (η : (j : Fin k) → Tensor (dims j)) (common : Fin D → ℕ)
    (U : (i : Fin D) → Matrix (Fin (common i)) (Fin (d i)) ℂ)
    (V : (i : Fin D) → Matrix (Fin (common i)) ((j : Fin k) → Fin (dims j i)) ℂ),
    (∀ j, S j ≠ Finset.univ) ∧
    (∀ j i, i ∉ S j → dims j i = 1) ∧
    (∀ j, ∑ x, Complex.normSq (η j x) = 1) ∧
    (∀ i, (U i)ᴴ * U i = 1) ∧ (∀ i, (V i)ᴴ * V i = 1) ∧
    productMap (fun i => Fin (d i)) U *ᵥ ψ =
      productMap (fun i => (j : Fin k) → Fin (dims j i)) V *ᵥ
        (fun x => ∏ j, η j (fun i => x i j))

abbrev Grouped (k : ℕ) (dims : Fin k → Fin 4 → ℕ) (i : Fin 4) :=
  (j : Fin k) → Fin (dims j i)

/-- The four-qubit instance of the proper-support factorization predicate. -/
abbrev Reducible (ψ : Bits → ℂ) : Prop := ReducibleTensor (d := qubits) ψ

/-- The rank-two singleton cuts force effective factor supports to partition the parties.
Any effective support is a rank-one cut of the grouped product. -/
theorem cluster_irreducible : ¬ Reducible clusterState := by
  classical
  rintro ⟨k, S, dims, η, common, U, V, hp, hs, hn, hU, hV, he⟩
  have hcut (p : Fin 4 → Prop) [DecidablePred p] :
      (flatten p clusterState).rank = ∏ j, (flatten p (η j)).rank := by
    rw [← flatten_rank_local_isometries p clusterState U hU, he,
      flatten_rank_local_isometries p _ V hV]
    exact flatten_rank_grouped p k (fun j i => Fin (dims j i)) η
  let r (j : Fin k) (i : Fin 4) := (flatten (· ∈ ({i} : Finset _)) (η j)).rank
  have hr (i : Fin 4) : ∏ j, r j i = 2 := by
    rw [show (∏ j, r j i) = ∏ j, (flatten (· ∈ ({i} : Finset (Fin 4))) (η j)).rank from rfl,
      ← hcut (· ∈ ({i} : Finset (Fin 4))), cluster_singleton_rank]
  choose active ha using fun i => prime_singleton_stripping Nat.prime_two (r · i) (hr i)
  let j₀ := active 0
  let T : Finset (Fin 4) := Finset.univ.filter fun i => active i = j₀
  have hmem (i : Fin 4) : i ∈ T ↔ active i = j₀ := by simp [T]
  have hT : T.Nonempty := ⟨0, (hmem _).mpr rfl⟩
  have hsub : T ⊆ S j₀ := by
    intro i hi
    by_contra h
    have hdim : dims j₀ i = 1 := hs j₀ i h
    have hrow : Subsingleton (∀ a : {a : Fin 4 // a ∈ ({i} : Finset (Fin 4))}, Fin (dims j₀ a)) :=
      ⟨by
        intro x y
        funext a
        obtain ⟨a, ha⟩ := a
        obtain rfl := Finset.mem_singleton.mp ha
        have hd (v : Fin (dims j₀ a)) : v.val = 0 := by have := v.isLt; omega
        exact Fin.ext ((hd _).trans (hd _).symm)⟩
    have hle : r j₀ i ≤ 1 := (Matrix.rank_le_card_height _).trans
      (Fintype.card_le_one_iff_subsingleton.mpr hrow)
    have htwo := (ha i).1
    rw [(hmem i).mp hi] at htwo
    omega
  have hproper : ∃ i, i ∉ T := by
    by_contra! h
    exact hp j₀ (Finset.eq_univ_of_forall fun i => hsub (h i))
  have hfactor (j : Fin k) : (flatten (· ∈ T) (η j)).rank ≤ 1 := by
    obtain ⟨base, hb⟩ : ∃ base, η j base ≠ 0 := by
      by_contra! h
      simpa [h] using hn j
    by_cases hj : j = j₀
    · rw [← rank_cut_complement (η j) T]
      apply rank_cut_le_one_of_singletons (η j) _ base hb
      intro i hi
      have hne : j ≠ active i := fun h => (Finset.mem_compl.mp hi)
        ((hmem i).mpr (h.symm.trans hj))
      exact ((ha i).2 j hne).le
    · apply rank_cut_le_one_of_singletons (η j) _ base hb
      intro i hi
      exact ((ha i).2 j (by rwa [(hmem i).mp hi])).le
  have hle : (flatten (· ∈ T) clusterState).rank ≤ 1 := by
    rw [hcut]
    simpa using Finset.prod_le_prod fun j (_ : j ∈ Finset.univ) => hfactor j
  have htwo := cluster_cut_rank_ge_two T hT hproper
  omega

open CarrozzaChevrierLionniConverseWIP (ordered averaged)

/-- A single normalized irreducible state has both zero readouts at every order n ≥ 2. -/
theorem cluster_counterexample :
    (∑ x : Bits, Complex.normSq (clusterState x)) = 1 ∧ ¬ Reducible clusterState ∧
      ∀ n : ℕ, 2 ≤ n →
        (∀ σ, ordered clusterState σ n = 0) ∧ averaged clusterState n = 0 :=
  ⟨CarrozzaChevrierLionniConverseWIP.cluster_state_normalized, cluster_irreducible,
    fun n hn => ⟨fun σ => CarrozzaChevrierLionniConverseWIP.cluster_ordered_zero σ n hn,
      CarrozzaChevrierLionniConverseWIP.cluster_averaged_zero n hn⟩⟩

end D5.S3.Quantum.Entanglement.CarrozzaChevrierLionniIrreducibilityWIP

end
