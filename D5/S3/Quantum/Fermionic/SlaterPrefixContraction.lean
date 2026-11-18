/- GID: D5/S3/Quantum/Fermionic/SlaterPrefixContraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/SlaterPrefixContraction
   mirror-E: none(waiver:finite-slater-marginal-spectrum)
   anchors: []
   utility: none
   digest: Slater prefix determinant contraction for a diagonal compression -/

import D5.S3.Quantum.Schatten.CompoundMatrices
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin

/-! # Slater prefix determinant contraction for a diagonal compression -/

namespace D5.S3.Quantum.Fermionic.SlaterPrefixContraction
open scoped BigOperators
open Matrix Polynomial

set_option maxHeartbeats 600000 in
private theorem coeff_det_weighted_cauchyBinet {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]
    {k : ℕ} (p : Finset ι) (A : Matrix (Fin k) ι R) (B : Matrix ι (Fin k) R) :
    let weight : ι → R[X] := fun i => X ^ (if i ∈ p then 1 else 0 : ℕ)
    ((A.map C * (Matrix.diagonal weight * B.map C)).det).coeff p.card =
      ∑ S : {S : Finset ι // S.card = k}, if p ⊆ S.val then
        (A.submatrix id (S.val.orderEmbOfFin S.property)).det *
          (B.submatrix (S.val.orderEmbOfFin S.property) id).det else 0 := by
  classical
  intro weight
  rw [cauchyBinet, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro S _
  let f := S.val.orderEmbOfFin S.property
  have hslice : (Matrix.diagonal weight * B.map C).submatrix f id =
      Matrix.diagonal (fun i => weight (f i)) * (B.submatrix f id).map C := by
    ext i j : 1
    simp [Matrix.diagonal_mul]
  have hcard : (∑ i : Fin k, if f i ∈ p then 1 else 0 : ℕ) =
      (S.val ∩ p).card := by
    calc
      _ = ∑ i : S.val, (if (i : ι) ∈ p then 1 else 0 : ℕ) :=
        Fintype.sum_equiv (S.val.orderIsoOfFin S.property).toEquiv _ _ (fun _ => rfl)
      _ = ∑ i ∈ S.val, (if i ∈ p then 1 else 0 : ℕ) := by
        simpa using Finset.sum_attach S.val (fun i => if i ∈ p then (1 : ℕ) else 0)
      _ = _ := by simp
  have hp : (S.val ∩ p).card = p.card ↔ p ⊆ S.val := by
    constructor
    · intro hc i hi
      have he : S.val ∩ p = p := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hc.ge
      exact (Finset.mem_inter.mp (he.symm ▸ hi)).1
    · intro h
      rw [Finset.inter_eq_right.mpr h]
  change (((A.map C).submatrix id f).det *
    ((Matrix.diagonal weight * B.map C).submatrix f id).det).coeff p.card = _
  have hmap : ((A.map C).submatrix id f).det = C (A.submatrix id f).det := by
    change ((A.submatrix id f).map C).det = _
    exact (RingHom.map_det C _).symm
  have hmapB : ((B.submatrix f id).map C).det = C (B.submatrix f id).det :=
    (RingHom.map_det C _).symm
  rw [hslice, hmap, Matrix.det_mul, Matrix.det_diagonal, hmapB]
  rw [show (∏ i : Fin k, weight (f i)) = X ^ (S.val ∩ p).card from by
    simp only [weight, Finset.prod_pow_eq_pow_sum, hcard]]
  rw [← mul_assoc, mul_right_comm, ← map_mul, Polynomial.coeff_C_mul_X_pow]
  simp only [eq_comm (a := p.card), hp]
  rfl

def stackRows {m n k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ)
    (B : Matrix (Fin n) (Fin k) ℂ) : Matrix (Fin (m + n)) (Fin k) ℂ :=
  fun i j => Fin.addCases (fun a => A a j) (fun b => B b j) i

private theorem weighted_stack_gram {m n k : ℕ} (A B : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) :
    let weight : Fin (m + n) → ℂ[X] := fun i => X ^ (if i.val < m then 1 else 0 : ℕ)
    (stackRows A Y).conjTranspose.map C * (Matrix.diagonal weight * (stackRows B Y).map C) =
      (X : ℂ[X]) • (A.conjTranspose * B).map C + (Y.conjTranspose * Y).map C := by
  intro weight
  ext i j : 1
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_add, map_sum, map_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    simp [stackRows, weight, a.isLt, map_mul]
    ac_rfl
  · apply Finset.sum_congr rfl
    intro b _
    have hb : ¬ m + b.val < m := by omega
    simp [stackRows, weight, hb, map_mul]

private def prefixSites (m n : ℕ) : Finset (Fin (m + n)) :=
  Finset.univ.map (Fin.castAddEmb n)

private theorem prefix_tail_disjoint (m n : ℕ) (t : Finset (Fin n)) :
    Disjoint (prefixSites m n) (t.map (Fin.natAddEmb m)) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx hy
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hx
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hy
  have he := congrArg Fin.val (hi.trans hj.symm)
  change i.val = m + j.val at he
  omega

private noncomputable def tailSites {m n : ℕ} (s : Finset (Fin (m + n))) : Finset (Fin n) :=
  s.preimage (Fin.natAddEmb m) (Fin.natAddEmb m).injective.injOn

private theorem prefix_tail_recover {m n : ℕ} (s : Finset (Fin (m + n)))
    (hs : prefixSites m n ⊆ s) :
    (prefixSites m n).disjUnion ((tailSites s).map (Fin.natAddEmb m))
      (prefix_tail_disjoint m n (tailSites s)) = s := by
  ext x
  induction x using Fin.addCases with
  | left i =>
    have h : Fin.castAdd n i ∈ prefixSites m n :=
      Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simp [h, hs h]
  | right j =>
    have hn : Fin.natAdd m j ∉ prefixSites m n := by
      intro h
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
      have he := congrArg Fin.val hi
      change i.val = m + j.val at he
      omega
    change Fin.natAddEmb m j ∈ _ ↔ Fin.natAddEmb m j ∈ s
    simp only [Finset.mem_disjUnion, show Fin.natAddEmb m j ∉ prefixSites m n from hn,
      false_or, Finset.mem_map', tailSites, Finset.mem_preimage]

open scoped BigOperators in
private noncomputable def prefixContainingSubsets (m n k : ℕ) :
    {s : Finset (Fin (m + n)) // s.card = k ∧ prefixSites m n ⊆ s} ≃
      {t : Finset (Fin n) // m + t.card = k} where
  toFun s := ⟨tailSites s.val, by
    have he := congrArg Finset.card (prefix_tail_recover s.val s.property.2)
    simpa only [prefixSites, Finset.card_disjUnion, Finset.card_map, Finset.card_univ,
      Fintype.card_fin, s.property.1] using he⟩
  invFun t := ⟨(prefixSites m n).disjUnion (t.val.map (Fin.natAddEmb m))
    (prefix_tail_disjoint m n t.val), by
      refine ⟨?_, fun i hi => Finset.mem_disjUnion.mpr (Or.inl hi)⟩
      simpa only [prefixSites, Finset.card_disjUnion, Finset.card_map, Finset.card_univ,
        Fintype.card_fin] using t.property⟩
  left_inv s := Subtype.ext (prefix_tail_recover _ s.property.2)
  right_inv t := by
    apply Subtype.ext
    ext i
    have hn : Fin.natAddEmb m i ∉ prefixSites m n := by
      intro hi
      exact Finset.disjoint_left.mp (prefix_tail_disjoint m n ({i} : Finset (Fin n))) hi
        (Finset.mem_map.mpr ⟨i, Finset.mem_singleton_self i, rfl⟩)
    change i ∈ tailSites ((prefixSites m n).disjUnion (t.val.map (Fin.natAddEmb m))
      (prefix_tail_disjoint m n t.val)) ↔ i ∈ t.val
    simp only [tailSites, Finset.mem_preimage, Finset.mem_disjUnion, hn, false_or, Finset.mem_map']

private theorem prefixContaining_order {m n : ℕ} (t : Finset (Fin n)) :
    let s := (prefixSites m n).disjUnion (t.map (Fin.natAddEmb m)) (prefix_tail_disjoint m n t)
    let hs : s.card = m + t.card := by
      simp only [s, prefixSites, Finset.card_disjUnion, Finset.card_map, Finset.card_univ,
        Fintype.card_fin]
    (s.orderEmbOfFin hs : Fin (m + t.card) → Fin (m + n)) =
      Fin.addCases (Fin.castAdd n) (fun j => Fin.natAdd m (t.orderEmbOfFin rfl j)) := by
  intro s hs
  symm
  apply Finset.orderEmbOfFin_unique
  · intro x
    induction x using Fin.addCases with
    | left i =>
      rw [Fin.addCases_left]
      exact Finset.mem_disjUnion.mpr (Or.inl (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    | right j =>
      rw [Fin.addCases_right]
      exact Finset.mem_disjUnion.mpr (Or.inr
        (Finset.mem_map.mpr ⟨_, t.orderEmbOfFin_mem rfl j, rfl⟩))
  · intro i j hij
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.addCases_left]
        exact hij
      | right j =>
        simp only [Fin.addCases_left, Fin.addCases_right]
        change i.val < m + (t.orderEmbOfFin rfl j).val
        omega
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        change m + i.val < j.val at hij
        omega
      | right j =>
        simp only [Fin.addCases_right]
        exact (Fin.natAdd_lt_natAdd_iff m).mpr
          ((t.orderEmbOfFin rfl).strictMono ((Fin.natAdd_lt_natAdd_iff m).mp hij))

private theorem mem_prefixSites {m n : ℕ} (i : Fin (m + n)) :
    i ∈ prefixSites m n ↔ i.val < m := by
  constructor
  · intro h
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp h
    exact a.isLt
  · intro hi
    exact Finset.mem_map.mpr ⟨⟨i.val, hi⟩, Finset.mem_univ _, Fin.ext rfl⟩

def stackMinor {m n k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) (t : Finset (Fin n)) (ht : m + t.card = k) :
    Matrix (Fin k) (Fin k) ℂ :=
  (stackRows A (Y.submatrix (t.orderEmbOfFin rfl) id)).submatrix (Fin.cast ht.symm) id

private theorem prefixMinor_eq_stackMinor {m n k : ℕ} (A : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) (t : Finset (Fin n)) (ht : m + t.card = k) :
    let s := (prefixContainingSubsets m n k).symm ⟨t, ht⟩
    (stackRows A Y).submatrix (s.val.orderEmbOfFin s.property.1) id = stackMinor A Y t ht := by
  subst k
  intro s
  have he := prefixContaining_order (m := m) t
  change (s.val.orderEmbOfFin s.property.1 : Fin (m + t.card) → Fin (m + n)) = _ at he
  ext i j : 1
  change stackRows A Y (s.val.orderEmbOfFin s.property.1 i) j = _
  rw [congrFun he i]
  induction i using Fin.addCases with
  | left a => simp [stackMinor, stackRows]
  | right b => simp [stackMinor, stackRows]

private def containingQualifier {m n k : ℕ} :
    {s : {s : Finset (Fin (m + n)) // s.card = k} // prefixSites m n ⊆ s.val} ≃
      {s : Finset (Fin (m + n)) // s.card = k ∧ prefixSites m n ⊆ s} where
  toFun s := ⟨s.val.val, s.val.property, s.property⟩
  invFun s := ⟨⟨s.val, s.property.1⟩, s.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxHeartbeats 900000 in
private theorem coeff_stackedGram_minor_sum {m n k : ℕ} (A B : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) :
    (((X : ℂ[X]) • (A.conjTranspose * B).map C + (Y.conjTranspose * Y).map C).det).coeff m =
      ∑ t : {t : Finset (Fin n) // m + t.card = k},
        star (stackMinor A Y t.val t.property).det * (stackMinor B Y t.val t.property).det := by
  classical
  let U := stackRows A Y
  let V := stackRows B Y
  let w : Fin (m + n) → ℂ[X] := fun i => X ^ (if i ∈ prefixSites m n then 1 else 0 : ℕ)
  have hm : (prefixSites m n).card = m := by simp [prefixSites]
  have hw : U.conjTranspose.map C * (Matrix.diagonal w * V.map C) =
      (X : ℂ[X]) • (A.conjTranspose * B).map C + (Y.conjTranspose * Y).map C := by
    simpa only [w, mem_prefixSites] using weighted_stack_gram A B Y
  have hweighted := coeff_det_weighted_cauchyBinet (prefixSites m n) U.conjTranspose V
  change (U.conjTranspose.map C * (Matrix.diagonal w * V.map C)).det.coeff _ = _ at hweighted
  rw [hm] at hweighted
  rw [← hw, hweighted, ← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
  let e := (containingQualifier (m := m) (n := n) (k := k)).trans (prefixContainingSubsets m n k)
  have hu : (Finset.univ : Finset {s : {s : Finset (Fin (m + n)) // s.card = k} //
      prefixSites m n ⊆ s.val}) =
      Finset.univ.subtype (fun s : {s : Finset (Fin (m + n)) // s.card = k} =>
        prefixSites m n ⊆ s.val) := by
    ext s
    simp
  rw [← hu]
  apply Fintype.sum_equiv e
  intro s
  let t := e s
  have hs : (prefixContainingSubsets m n k).symm t = containingQualifier s := by
    simp [t, e]
  have ha : U.submatrix (s.val.val.orderEmbOfFin s.val.property) id =
      stackMinor A Y t.val t.property := by
    have h := prefixMinor_eq_stackMinor A Y t.val t.property
    rwa [hs] at h
  have hb : V.submatrix (s.val.val.orderEmbOfFin s.val.property) id =
      stackMinor B Y t.val t.property := by
    have h := prefixMinor_eq_stackMinor B Y t.val t.property
    rwa [hs] at h
  change (U.conjTranspose.submatrix id _).det * (V.submatrix _ id).det = _
  rw [← Matrix.conjTranspose_submatrix, ha, hb, Matrix.det_conjTranspose]

private theorem det_prefixGram_update {m n k : ℕ} (P : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) (E : Matrix (Fin m) (Fin m) ℂ)
    (h : P.conjTranspose * P + Y.conjTranspose * Y = 1) :
    (((X : ℂ[X]) • (P.conjTranspose * E * P).map C + (Y.conjTranspose * Y).map C).det) =
      (((X : ℂ[X]) • (E * (P * P.conjTranspose)).map C + (1 - P * P.conjTranspose).map C).det) := by
  let A := P.conjTranspose.map C
  let B := P.map C
  let F : Matrix (Fin m) (Fin m) ℂ[X] := (X : ℂ[X]) • E.map C - 1
  have hy : (Y.conjTranspose * Y).map C = 1 - A * B := by
    have hY : Y.conjTranspose * Y = 1 - P.conjTranspose * P := eq_sub_of_add_eq' h
    rw [hY, Matrix.map_sub _ (map_sub C), Matrix.map_one _ (map_zero C) (map_one C), Matrix.map_mul]
  have hleft :
      (X : ℂ[X]) • (P.conjTranspose * E * P).map C + (Y.conjTranspose * Y).map C =
        1 + A * (F * B) := by
    rw [hy]
    simp only [F, A, B, Matrix.map_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    abel
  have hright :
      (X : ℂ[X]) • (E * (P * P.conjTranspose)).map C + (1 - P * P.conjTranspose).map C =
        1 + (F * B) * A := by
    simp only [F, A, B, Matrix.map_sub _ (map_sub C), Matrix.map_one _ (map_zero C) (map_one C),
      Matrix.map_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc]
    abel
  rw [hleft, hright, Matrix.det_one_add_mul_comm]


open scoped BigOperators
open Matrix Polynomial

private theorem coeff_det_supported_rows {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (S : Set ι) [Fintype S] [Fintype (Sᶜ : Set ι)]
    (M : Matrix ι ι R) (d : ι → R) (hM : ∀ i, i ∉ S → ∀ j, M i j = 0) :
    (det (((X : R[X]) • M.map C) + (diagonal d).map C)).coeff (Fintype.card S) =
      (M.submatrix (fun i : S => i.1) (fun i : S => i.1)).det *
        ∏ j : (Sᶜ : Set ι), d j := by
  classical
  let e := Equiv.Set.sumCompl S
  let M₀ := M.submatrix (fun i : S => i.1) (fun i : S => i.1)
  let B : Matrix S S R := diagonal fun i => d i
  let D : Matrix (Sᶜ : Set ι) (Sᶜ : Set ι) R[X] := diagonal fun i => C (d i)
  let Q : Matrix ι ι R[X] := (X : R[X]) • M.map C + (diagonal d).map C
  let R₁₂ : Matrix S (Sᶜ : Set ι) R[X] := fun i j => X * C (M i j)
  have hblock : Q.submatrix e e =
      fromBlocks ((X : R[X]) • M₀.map C + B.map C) R₁₂ 0 D := by
    ext i j : 1
    rcases i with i | i <;> rcases j with j | j
    · simp [Q, e, M₀, B, Matrix.diagonal_apply, Subtype.ext_iff]
    · have hne : (i : ι) ≠ j := fun h => j.2 (h ▸ i.2)
      simp only [Q, e, R₁₂, Matrix.submatrix_apply, Equiv.Set.sumCompl_apply_inl,
        Equiv.Set.sumCompl_apply_inr, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
        Matrix.diagonal_apply, ite_eq_right hne, map_zero, add_zero, smul_eq_mul]
      rfl
    · have hne : (i : ι) ≠ j := fun h => i.2 (h ▸ j.2)
      simp [Q, e, hne, hM _ i.2]
    · simp [Q, e, D, Matrix.diagonal_apply, Subtype.ext_iff, hM _ i.2]
  change Q.det.coeff _ = M₀.det * _
  rw [← Matrix.det_submatrix_equiv_self e Q, hblock, Matrix.det_fromBlocks_zero₂₁]
  have hD : D.det = C (∏ j : (Sᶜ : Set ι), d j) := by
    simp [D, Matrix.det_diagonal, map_prod]
  rw [hD, Polynomial.coeff_mul_C, Polynomial.coeff_det_X_add_C_card]

private def selectRows {r m : ℕ} (e : Fin r ↪ Fin m) : Matrix (Fin r) (Fin m) ℂ :=
  fun i j => if e i = j then 1 else 0

private theorem selectRows_mul {r m k : ℕ} (e : Fin r ↪ Fin m) (P : Matrix (Fin m) (Fin k) ℂ) :
    selectRows e * P = P.submatrix e id := by
  ext i j
  simp [Matrix.mul_apply, selectRows]

private theorem selectedCrossGram {r m k : ℕ} (e f : Fin r ↪ Fin m)
    (P : Matrix (Fin m) (Fin k) ℂ) :
    (P.submatrix e id).conjTranspose * P.submatrix f id =
      P.conjTranspose * (selectRows e).conjTranspose * selectRows f * P := by
  rw [← selectRows_mul, ← selectRows_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private theorem selector_support {r m : ℕ} (e f : Fin r ↪ Fin m) (i j : Fin m)
    (h : i ∉ Set.range e ∨ j ∉ Set.range f) :
    ((selectRows e).conjTranspose * selectRows f) i j = 0 := by
  rcases h with h | h
  · have he (a : Fin r) : e a ≠ i := fun ha => h ⟨a, ha⟩
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, selectRows, he]
  · have hf (a : Fin r) : f a ≠ j := fun ha => h ⟨a, ha⟩
    simp [Matrix.mul_apply, selectRows, hf]

private theorem selector_diagonal {r m : ℕ} (e : Fin r ↪ Fin m) :
    (selectRows e).conjTranspose * selectRows e =
      Matrix.diagonal (fun i => if i ∈ Set.range e then (1 : ℂ) else 0) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hi
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, selectRows,
        e.injective.eq_iff]
    · rw [selector_support e e i i (Or.inl hi)]
      simp only [Matrix.diagonal_apply, ite_eq_right hi, ite_self]
  · simp only [Matrix.diagonal_apply, ite_eq_right hij]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hi : e a = i
    · have hj : e a ≠ j := hi ▸ hij
      simp [Matrix.conjTranspose_apply, selectRows, hj]
    · simp [Matrix.conjTranspose_apply, selectRows, hi]

set_option maxHeartbeats 600000 in
private theorem coeff_diag_selection {m r : ℕ} (a b : Finset (Fin m)) (ha : a.card = r)
    (hb : b.card = r) (ν : Fin m → ℂ) :
    let A := selectRows (a.orderEmbOfFin ha).toEmbedding
    let B := selectRows (b.orderEmbOfFin hb).toEmbedding
    (((X : ℂ[X]) • ((A.conjTranspose * B) * Matrix.diagonal ν).map C +
        (Matrix.diagonal fun i => 1 - ν i).map C).det).coeff r =
      if a = b then (∏ i, if i ∈ a then ν i else 1 - ν i) else 0 := by
  classical
  intro A B
  let e := (a.orderEmbOfFin ha).toEmbedding
  let f := (b.orderEmbOfFin hb).toEmbedding
  let M := (A.conjTranspose * B) * Matrix.diagonal ν
  have hr (i : Fin m) (hi : i ∉ (a : Set (Fin m))) (j : Fin m) : M i j = 0 := by
    change ((selectRows e).conjTranspose * selectRows f * Matrix.diagonal ν) i j = 0
    rw [Matrix.mul_diagonal, selector_support e f _ _ (Or.inl fun ⟨q, hq⟩ =>
      hi (hq ▸ a.orderEmbOfFin_mem ha q)), zero_mul]
  have hc := coeff_det_supported_rows (a : Set (Fin m)) M (fun i => 1 - ν i) hr
  have hcard : Fintype.card (a : Set (Fin m)) = r := by simpa using ha
  rw [hcard] at hc
  change (det ((X : ℂ[X]) • M.map C + (Matrix.diagonal fun i => 1 - ν i).map C)).coeff r = _
  rw [hc]
  by_cases hab : a = b
  · subst b
    have hdiag : M.submatrix (fun i : (a : Set (Fin m)) => i.1) (fun i : (a : Set (Fin m)) => i.1) =
        Matrix.diagonal (fun i : (a : Set (Fin m)) => ν i) := by
      ext i j
      change ((selectRows e).conjTranspose * selectRows e * Matrix.diagonal ν) i j = _
      rw [selector_diagonal, Matrix.diagonal_mul_diagonal]
      by_cases hij : i = j
      · subst j
        have hi : i.1 ∈ Set.range e :=
          (a.range_orderEmbOfFin ha).symm ▸ i.2
        simp only [Matrix.diagonal_apply, ite_eq_left hi, ite_true, one_mul]
      · have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
        simp [hij, hne]
    rw [hdiag, Matrix.det_diagonal, ite_eq_left rfl]
    have hleft : (∏ i : (a : Set (Fin m)), ν i) = ∏ i ∈ a, ν i :=
      (Finset.prod_subtype a (fun _ => Iff.rfl) ν).symm
    have hright : (∏ i : ((a : Set (Fin m))ᶜ : Set (Fin m)), (1 - ν i)) = ∏ i ∈ aᶜ, (1 - ν i) :=
      (Finset.prod_subtype aᶜ (fun i => Finset.mem_compl) (fun i => 1 - ν i)).symm
    rw [hleft, hright, ← Finset.prod_mul_prod_compl a]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp [hi]
    · apply Finset.prod_congr rfl
      intro i hi
      simp [Finset.mem_compl.mp hi]
  · obtain ⟨j, hj, hjb⟩ : ∃ j ∈ a, j ∉ b := by
      by_contra! hsub
      exact hab (Finset.eq_of_subset_of_card_le hsub (hb.trans ha.symm).le)
    have hz : (M.submatrix (fun i : (a : Set (Fin m)) => i.1) (fun i : (a : Set (Fin m)) => i.1)).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero ⟨j, hj⟩
      intro i
      change ((selectRows e).conjTranspose * selectRows f * Matrix.diagonal ν) i j = 0
      rw [Matrix.mul_diagonal, selector_support e f _ _ (Or.inr fun ⟨q, hq⟩ =>
        hjb (hq ▸ b.orderEmbOfFin_mem hb q)), zero_mul]
    rw [hz, zero_mul, ite_eq_right hab]

private theorem diagonal_stacked_contraction {m n k r : ℕ} (P : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) (ν : Fin m → ℂ)
    (hV : P.conjTranspose * P + Y.conjTranspose * Y = 1)
    (hdiag : P * P.conjTranspose = Matrix.diagonal ν)
    (a b : Finset (Fin m)) (ha : a.card = r) (hb : b.card = r) :
    let A := P.submatrix (a.orderEmbOfFin ha) id
    let B := P.submatrix (b.orderEmbOfFin hb) id
    (∑ t : {t : Finset (Fin n) // r + t.card = k},
      star (stackMinor A Y t.val t.property).det * (stackMinor B Y t.val t.property).det) =
      if a = b then (∏ i, if i ∈ a then ν i else 1 - ν i) else 0 := by
  classical
  intro A B
  let E := (selectRows (a.orderEmbOfFin ha).toEmbedding).conjTranspose *
    selectRows (b.orderEmbOfFin hb).toEmbedding
  have hcross : A.conjTranspose * B = P.conjTranspose * E * P := by
    change (P.submatrix (a.orderEmbOfFin ha).toEmbedding id).conjTranspose *
      P.submatrix (b.orderEmbOfFin hb).toEmbedding id = _
    rw [selectedCrossGram]
    simp only [E, Matrix.mul_assoc]
  rw [← coeff_stackedGram_minor_sum A B Y, hcross, det_prefixGram_update P Y E hV, hdiag]
  have hbase : 1 - Matrix.diagonal ν = Matrix.diagonal (fun i => 1 - ν i) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub]
  rw [hbase]
  exact coeff_diag_selection a b ha hb ν

theorem stackMinor_cast_selected {m n k r : ℕ} (P : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) (a : Finset (Fin m)) (ha : a.card = r)
    (t : Finset (Fin n)) (h : r + t.card = k) (h' : a.card + t.card = k) :
    stackMinor (P.submatrix (a.orderEmbOfFin rfl) id) Y t h' =
      stackMinor (P.submatrix (a.orderEmbOfFin ha) id) Y t h := by
  subst r
  rfl

noncomputable def prefixAmplitudes {m n k : ℕ} (P : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) : Matrix (Finset (Fin m)) (Finset (Fin n)) ℂ :=
  fun a b => if h : a.card + b.card = k then
    (stackMinor (P.submatrix (a.orderEmbOfFin rfl) id) Y b h).det else 0

theorem diagonal_prefixMarginal {m n k : ℕ} (P : Matrix (Fin m) (Fin k) ℂ)
    (Y : Matrix (Fin n) (Fin k) ℂ) (ν : Fin m → ℂ)
    (hV : P.conjTranspose * P + Y.conjTranspose * Y = 1)
    (hdiag : P * P.conjTranspose = Matrix.diagonal ν) :
    prefixAmplitudes P Y * (prefixAmplitudes P Y).conjTranspose =
      Matrix.diagonal (fun a => ∏ i : Fin m, if i ∈ a then ν i else 1 - ν i) := by
  classical
  ext a b
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.conjTranspose_apply]
  by_cases hab : a.card = b.card
  · let r := a.card
    have hsum :
        (∑ t : Finset (Fin n), prefixAmplitudes P Y a t * star (prefixAmplitudes P Y b t)) =
        ∑ t : {t : Finset (Fin n) // r + t.card = k},
          star (stackMinor (P.submatrix (b.orderEmbOfFin hab.symm) id) Y t.val t.property).det *
            (stackMinor (P.submatrix (a.orderEmbOfFin rfl) id) Y t.val t.property).det := by
      let F : Finset (Fin n) → ℂ := fun t =>
        prefixAmplitudes P Y a t * star (prefixAmplitudes P Y b t)
      calc
        _ = ∑ t ∈ Finset.univ.filter (fun t : Finset (Fin n) => r + t.card = k), F t := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro t _
          by_cases ht : r + t.card = k
          · rw [ite_eq_left ht]
          · have hta : a.card + t.card ≠ k := ht
            simp [F, prefixAmplitudes, hta, ht]
        _ = ∑ t : {t : Finset (Fin n) // r + t.card = k}, F t.val :=
          Finset.sum_subtype _ (by simp) F
        _ = _ := by
          apply Finset.sum_congr rfl
          intro t _
          have ht : a.card + t.val.card = k := t.property
          have ht' : b.card + t.val.card = k := by rw [← hab]; exact ht
          simp only [F, prefixAmplitudes, dite_eq_left ht, dite_eq_left ht']
          rw [stackMinor_cast_selected P Y b hab.symm t.val t.property ht', mul_comm]
    rw [hsum]
    rw [diagonal_stacked_contraction P Y ν hV hdiag b a hab.symm rfl]
    by_cases he : b = a
    · subst b
      simp
    · simp [he, Ne.symm he]
  · have hne : a ≠ b := fun h => hab (congrArg Finset.card h)
    rw [ite_eq_right hne]
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : a.card + t.card = k
    · have hb : b.card + t.card ≠ k := by omega
      simp [prefixAmplitudes, hb]
    · simp [prefixAmplitudes, ht]

end D5.S3.Quantum.Fermionic.SlaterPrefixContraction
