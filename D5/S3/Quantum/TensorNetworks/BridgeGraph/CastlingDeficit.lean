/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/CastlingDeficit
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/CastlingDeficit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: CastlingDeficit for width-three bridge flow. -/

/-
proof_shape: castling_proved: content
escape_witness: castling_proved: CastlingDeficit.assignment_castling
admission_basis: escape-witness (castling_proved)
Module content mechanism: assignment_castling: complementary common-kernel deficit transport.
Direct frozen dependencies: none on the implementation baseline.
Utility: none; symbolic constructions and proofs for arbitrary dimensions,
not bounded enumeration, a checker, numeric reduction, or a certified instance.
Information-escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14762
-/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit
open Matrix Module

open D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open Matrix Module
section

open Module LinearMap

variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H]

variable [FiniteDimensional K H]

end
section

open Module LinearMap

variable {K H A : Type*} [Field K] [AddCommGroup H] [Module K H]
  [FiniteDimensional K H]

private theorem extend_subspace (U : Submodule K H) (n : ℕ)
    (hu : finrank K U ≤ n) (hn : n ≤ finrank K H) :
    ∃ V : Submodule K H, U ≤ V ∧ finrank K V = n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases heq : finrank K U = n
    · exact ⟨U, le_rfl, heq⟩
    · have hlt : finrank K U < n := by omega
      obtain ⟨V, huv, hv⟩ := ih (n - 1) (by omega) (by omega) (by omega)
      have hne : V ≠ ⊤ := by
        intro h
        have hdim : finrank K V = finrank K H := by rw [h, finrank_top]
        omega
      obtain ⟨x, hx⟩ : ∃ x : H, x ∉ V := by
        by_contra h
        push_neg at h
        exact hne (eq_top_iff.mpr (fun x _ => h x))
      refine ⟨V ⊔ Submodule.span K {x}, huv.trans le_sup_left, ?_⟩
      rw [Submodule.finrank_sup_span_singleton hx, hv]
      omega

variable [AddCommGroup A] [Module K A] [FiniteDimensional K A]

private theorem complete_linearMap (f : A →ₗ[K] H) (hd : finrank K A ≤ finrank K H) :
    ∃ (g : A →ₗ[K] H) (p : A →ₗ[K] A), Function.Injective g ∧ f = g.comp p := by
  classical
  obtain ⟨U, hu, hdim⟩ := extend_subspace (range f) (finrank K A) f.finrank_range_le hd
  let e : A ≃ₗ[K] U := LinearEquiv.ofFinrankEq A U hdim.symm
  let g := U.subtype.comp e.toLinearMap
  let p := e.symm.toLinearMap.comp (f.codRestrict U (fun x => hu ⟨x, rfl⟩))
  refine ⟨g, p, U.injective_subtype.comp e.injective, ?_⟩
  ext x
  change f x = ((e (e.symm _)) : H)
  simp

end
section

open Module LinearMap Matrix

variable {K : Type*} [Field K]

private def flatten {a b : ℕ} (M : Fin 3 → Matrix (Fin a) (Fin b) K) :
    Matrix (Fin b × Fin 3) (Fin a) K := fun j i => M j.2 i j.1

private def Concise {a b : ℕ} (M : Fin 3 → Matrix (Fin a) (Fin b) K) : Prop :=
  Function.Injective (flatten M).mulVecLin

private theorem complete_matrix {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (F : Matrix n m K)
    (hd : Fintype.card m ≤ Fintype.card n) :
    ∃ (G : Matrix n m K) (P : Matrix m m K),
      Function.Injective G.mulVecLin ∧ F = G * P := by
  obtain ⟨g, p, hg, hp⟩ := complete_linearMap F.mulVecLin (by simpa using hd)
  refine ⟨LinearMap.toMatrix' g, LinearMap.toMatrix' p, ?_, ?_⟩
  · change Function.Injective (Matrix.toLin' (LinearMap.toMatrix' g))
    rw [Matrix.toLin'_toMatrix']
    exact hg
  · have h := congrArg LinearMap.toMatrix' hp
    change LinearMap.toMatrix' (Matrix.toLin' F) = _ at h
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using h

private theorem complete_slices {a b : ℕ} (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (hab : a ≤ 3 * b) :
    ∃ (M' : Fin 3 → Matrix (Fin a) (Fin b) K) (P : Matrix (Fin a) (Fin a) K),
      Concise M' ∧ ∀ r, M r = P * M' r := by
  classical
  obtain ⟨G, P, hg, hf⟩ := complete_matrix (flatten M) (by simpa [mul_comm] using hab)
  let M' : Fin 3 → Matrix (Fin a) (Fin b) K := fun r i j => G (j,r) i
  refine ⟨M', P.transpose, hg, ?_⟩
  intro r
  ext i j
  have h := congrFun (congrFun hf (j,r)) i
  change M r i j = ∑ x, P x i * G (j,r) x
  simpa [flatten, Matrix.mul_apply, Matrix.transpose_apply, M', mul_comm] using h

private theorem flow_left_mul {a b c d : ℕ}
    (P : Matrix (Fin a) (Fin a) K)
    (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (N : Fin 3 → Matrix (Fin d) (Fin c) K) :
    flow (fun r => P * M r) N = Matrix.kronecker P 1 * flow M N := by
  classical
  simp only [flow, Matrix.mul_sum]
  congr 1
  funext r
  simpa only [Matrix.one_mul, Matrix.kronecker] using Matrix.mul_kronecker_mul P (M r) (1 : Matrix (Fin d) (Fin d) K) (N r)

private theorem flow_right_mul {a b c d : ℕ}
    (P : Matrix (Fin c) (Fin c) K)
    (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (N : Fin 3 → Matrix (Fin d) (Fin c) K) :
    flow M (fun r => N r * P) = flow M N * Matrix.kronecker 1 P := by
  classical
  simp only [flow, Matrix.sum_mul]
  congr 1
  funext r
  simpa only [Matrix.mul_one, Matrix.kronecker] using Matrix.mul_kronecker_mul (M r) (1 : Matrix (Fin b) (Fin b) K) (N r) P

private theorem concise_dominates {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (N : Fin 3 → Matrix (Fin d) (Fin c) K)
    (ha : a ≤ 3 * b) (hc : c ≤ 3 * d) :
    ∃ (M' : Fin 3 → Matrix (Fin a) (Fin b) K)
      (N' : Fin 3 → Matrix (Fin d) (Fin c) K),
      Concise M' ∧ Concise (fun r => (N' r).transpose) ∧
      (flow M N).rank ≤ (flow M' N').rank := by
  classical
  obtain ⟨M', P, hm, hp⟩ := complete_slices M ha
  obtain ⟨Nt, Q, hn, hq⟩ := complete_slices (fun r => (N r).transpose) hc
  let N' : Fin 3 → Matrix (Fin d) (Fin c) K := fun r => (Nt r).transpose
  refine ⟨M', N', hm, ?_, ?_⟩
  · simpa [N'] using hn
  · have heqM : M = fun r => P * M' r := funext hp
    have heqN : N = fun r => N' r * Q.transpose := by
      funext r
      have h := congrArg Matrix.transpose (hq r)
      simpa [N'] using h
    rw [heqM, heqN, flow_left_mul, flow_right_mul]
    exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_left _ _)

private theorem concise_maximizer {a b c d : ℕ} (ha : a ≤ 3 * b) (hc : c ≤ 3 * d) :
    ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      Concise M ∧ Concise (fun r => (N r).transpose) ∧
      (flow M N).rank = QMaxFlow a b c d := by
  obtain ⟨M,N,h⟩ := QMaxFlow_attained a b c d
  obtain ⟨M',N',hm,hn,hr⟩ := concise_dominates M N ha hc
  refine ⟨M',N',hm,hn,le_antisymm (rank_le_QMaxFlow M' N') ?_⟩
  rwa [← h]

end
section

open Module LinearMap Matrix

variable {K : Type*} [Field K]

variable {H A B : Type*} [AddCommGroup H] [Module K H]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

private theorem kernel_comp_finrank (L : A →ₗ[K] H) (P : H →ₗ[K] B)
    (hl : Function.Injective L) :
    finrank K (ker (P.comp L)) = finrank K (range L ⊓ ker P : Submodule K H) := by
  have h := (Submodule.equivMapOfInjective L hl (ker (P.comp L))).finrank_eq
  rwa [LinearMap.ker_comp, Submodule.map_comap_eq] at h

private theorem matrix_common_deficit {h a b c : Type*}
    [Fintype h] [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq h] [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (L : Matrix h a K) (R : Matrix h b K) (S : Matrix h c K)
    {d : Type*} [Fintype d] [DecidableEq d] (T : Matrix h d K)
    (hL : Function.Injective L.mulVecLin) (hT : Function.Injective T.mulVecLin)
    (hrt : range T.mulVecLin = ker R.transpose.mulVecLin)
    (hsl : ker S.transpose.mulVecLin = range L.mulVecLin) :
    (Fintype.card a : ℤ) - (R.transpose * L).rank =
      (Fintype.card d : ℤ) - (S.transpose * T).rank := by
  have hk1 := kernel_comp_finrank L.mulVecLin R.transpose.mulVecLin hL
  have hk2 := kernel_comp_finrank T.mulVecLin S.transpose.mulVecLin hT
  rw [hrt, hsl, inf_comm] at hk2
  have hsame : finrank K (ker (R.transpose * L).mulVecLin) =
      finrank K (ker (S.transpose * T).mulVecLin) := by
    rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul]
    exact hk1.trans hk2.symm
  have hn1 := (R.transpose * L).mulVecLin.finrank_range_add_finrank_ker
  have hn2 := (S.transpose * T).mulVecLin.finrank_range_add_finrank_ker
  change (R.transpose * L).rank + _ = finrank K (a → K) at hn1
  change (S.transpose * T).rank + _ = finrank K (d → K) at hn2
  rw [Module.finrank_pi] at hn1 hn2
  omega

end
section

open Module LinearMap Matrix

variable {K : Type*} [Field K]

private theorem rank_of_injective {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (F : Matrix n m K) (hf : Function.Injective F.mulVecLin) :
    F.rank = Fintype.card m := by
  simpa only [Matrix.rank, Module.finrank_pi, Module.finrank_self, mul_one] using
    F.mulVecLin.finrank_range_of_inj hf

private theorem complement_matrix {m k : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n (Fin m) K) (hf : Function.Injective F.mulVecLin)
    (hsize : k + m = Fintype.card n) :
    ∃ S : Matrix n (Fin k) K,
      Function.Injective S.mulVecLin ∧
      range S.mulVecLin = ker F.transpose.mulVecLin ∧
      ker S.transpose.mulVecLin = range F.mulVecLin := by
  classical
  have hr := rank_of_injective F hf
  have hn := F.rank_le_card_height
  have hk := F.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hdim : finrank K (ker F.transpose.mulVecLin) = k := by
    change F.transpose.rank + _ = finrank K (n → K) at hk
    rw [Matrix.rank_transpose, hr] at hk
    simp only [Module.finrank_pi, Fintype.card_fin] at hk
    omega
  let e : (Fin k → K) ≃ₗ[K] ker F.transpose.mulVecLin :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hdim.symm)
  let g := (ker F.transpose.mulVecLin).subtype.comp e.toLinearMap
  let S := LinearMap.toMatrix' g
  have hs : S.mulVecLin = g := Matrix.toLin'_toMatrix' g
  have hi : Function.Injective S.mulVecLin := by
    rw [hs]
    exact (ker F.transpose.mulVecLin).injective_subtype.comp e.injective
  have hrange : range S.mulVecLin = ker F.transpose.mulVecLin := by
    rw [hs, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Submodule.range_subtype]
  refine ⟨S, hi, hrange, ?_⟩
  have hzero : F.transpose * S = 0 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul]
    simp only [Matrix.toLin'_apply', Matrix.mulVecLin_zero]
    apply LinearMap.ext
    intro x
    have hx : S.mulVecLin x ∈ ker F.transpose.mulVecLin := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    exact hx
  have hzero' : S.transpose * F = 0 := by
    simpa using congrArg Matrix.transpose hzero
  have hle : range F.mulVecLin ≤ ker S.transpose.mulVecLin := by
    rintro x ⟨y,rfl⟩
    change S.transpose *ᵥ (F *ᵥ y) = 0
    rw [Matrix.mulVec_mulVec, hzero']
    simp
  have hd := S.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hrs := rank_of_injective S hi
  have heq : finrank K (range F.mulVecLin) = finrank K (ker S.transpose.mulVecLin) := by
    change S.transpose.rank + _ = finrank K (n → K) at hd
    rw [Matrix.rank_transpose, hrs] at hd
    simp only [Module.finrank_pi, Fintype.card_fin] at hd
    have hd' : S.rank + finrank K (ker S.transpose.mulVecLin) = Fintype.card n := by
      have hh := S.transpose.mulVecLin.finrank_range_add_finrank_ker
      change S.transpose.rank + _ = finrank K (n → K) at hh
      rwa [Matrix.rank_transpose, Module.finrank_pi] at hh
    simp only [Fintype.card_fin] at hr hrs
    change F.rank = _
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle heq).symm

end
section

open Module LinearMap Matrix

variable {K : Type*} [Field K]
variable {a b c d w n : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  [Fintype w] [Fintype n] [DecidableEq a] [DecidableEq b] [DecidableEq c]
  [DecidableEq d] [DecidableEq w] [DecidableEq n]

private def liftRight (G : Matrix (d × w) c K) : Matrix ((b × w) × d) (b × c) K :=
  (Matrix.kronecker (1 : Matrix b b K) G).submatrix
    (fun i => (i.1.1, (i.2, i.1.2))) _root_.id

@[simp]
private theorem liftLeft_mulVec (F : Matrix n a K) (x : a × d → K) (i : n) (l : d) :
    ((Matrix.kronecker F (1 : Matrix d d K)) *ᵥ x) (i,l) = (F *ᵥ fun j => x (j,l)) i := by
  simp [ Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type, mul_ite, ite_mul, eq_comm]

@[simp]
private theorem liftRight_mulVec (G : Matrix (d × w) c K) (x : b × c → K)
    (j : b) (r : w) (l : d) :
    (liftRight G *ᵥ x) ((j,r),l) = (G *ᵥ fun h => x (j,h)) (l,r) := by
  simp [liftRight, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

@[simp]
private theorem liftLeft_transpose_mulVec (F : Matrix n a K) (x : n × d → K)
    (i : a) (l : d) :
    (((Matrix.kronecker F (1 : Matrix d d K))).transpose *ᵥ x) (i,l) = (F.transpose *ᵥ fun j => x (j,l)) i := by
  simp [ Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.one_apply, Matrix.transpose_apply, Fintype.sum_prod_type, mul_ite, ite_mul]

@[simp]
private theorem liftRight_transpose_mulVec (G : Matrix (d × w) c K)
    (x : (b × w) × d → K) (j : b) (h : c) :
    ((liftRight G).transpose *ᵥ x) (j,h) =
      (G.transpose *ᵥ fun lr => x ((j,lr.2),lr.1)) h := by
  simp only [Matrix.mulVec, dotProduct, liftRight, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply,
    Matrix.submatrix_apply, id_eq, Matrix.of_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, ite_mul]
  rw [Finset.sum_comm]
  simp [eq_comm]
  exact Finset.sum_comm

private theorem liftLeft_injective (F : Matrix n a K) (hf : Function.Injective F.mulVecLin) :
    Function.Injective ((Matrix.kronecker F (1 : Matrix (d) (d) K))).mulVecLin := by
  intro x y h
  funext ⟨i,l⟩
  have hs : (fun j => x (j,l)) = (fun j => y (j,l)) := hf (by
    ext j
    simpa only [Matrix.mulVecLin_apply, liftLeft_mulVec] using congrFun h (j,l))
  exact congrFun hs i

private theorem liftRight_injective (G : Matrix (d × w) c K)
    (hg : Function.Injective G.mulVecLin) :
    Function.Injective (liftRight (b := b) G).mulVecLin := by
  intro x y h
  funext ⟨j,h'⟩
  have hs : (fun k => x (j,k)) = (fun k => y (j,k)) := hg (by
    ext lr
    simpa only [Matrix.mulVecLin_apply, liftRight_mulVec] using congrFun h ((j,lr.2),lr.1))
  exact congrFun hs h'

private theorem mem_range_liftLeft (F : Matrix n a K) (y : n × d → K) :
    y ∈ range ((Matrix.kronecker F (1 : Matrix d d K))).mulVecLin ↔
      ∀ l, (fun j => y (j,l)) ∈ range F.mulVecLin := by
  classical
  constructor
  · rintro ⟨x,rfl⟩ l
    refine ⟨fun j => x (j,l), ?_⟩
    ext i
    exact (liftLeft_mulVec F x i l).symm
  · intro h
    choose x hx using h
    refine ⟨fun jl => x jl.2 jl.1, ?_⟩
    funext ⟨i,l⟩
    simpa only [Matrix.mulVecLin_apply, liftLeft_mulVec] using congrFun (hx l) i

private theorem mem_range_liftRight (G : Matrix (d × w) c K) (y : (b × w) × d → K) :
    y ∈ range (liftRight G).mulVecLin ↔
      ∀ j, (fun lr => y ((j,lr.2),lr.1)) ∈ range G.mulVecLin := by
  classical
  constructor
  · rintro ⟨x,rfl⟩ j
    refine ⟨fun k => x (j,k), ?_⟩
    funext ⟨l,r⟩
    exact (liftRight_mulVec G x j r l).symm
  · intro h
    choose x hx using h
    refine ⟨fun jk => x jk.1 jk.2, ?_⟩
    funext ⟨⟨j,r⟩,l⟩
    simpa only [Matrix.mulVecLin_apply, liftRight_mulVec] using congrFun (hx j) (l,r)

private theorem mem_ker_liftLeft_transpose (F : Matrix n a K) (y : n × d → K) :
    y ∈ ker ((Matrix.kronecker F (1 : Matrix d d K))).transpose.mulVecLin ↔
      ∀ l, (fun j => y (j,l)) ∈ ker F.transpose.mulVecLin := by
  simp only [LinearMap.mem_ker, funext_iff, Matrix.mulVecLin_apply,
    Prod.forall, liftLeft_transpose_mulVec, Pi.zero_apply]
  exact forall_comm

private theorem mem_ker_liftRight_transpose (G : Matrix (d × w) c K)
    (y : (b × w) × d → K) :
    y ∈ ker (liftRight G).transpose.mulVecLin ↔
      ∀ j, (fun lr => y ((j,lr.2),lr.1)) ∈ ker G.transpose.mulVecLin := by
  simp only [LinearMap.mem_ker, funext_iff, Matrix.mulVecLin_apply,
    Prod.forall, liftRight_transpose_mulVec, Pi.zero_apply]

private theorem left_complement {a' : Type*} [Fintype a'] [DecidableEq a']
    (F : Matrix n a K) (S : Matrix n a' K)
    (h : range S.mulVecLin = ker F.transpose.mulVecLin) :
    range ((Matrix.kronecker S (1 : Matrix (d) (d) K))).mulVecLin = ker ((Matrix.kronecker F (1 : Matrix (d) (d) K))).transpose.mulVecLin := by
  ext y
  simp only [mem_range_liftLeft, mem_ker_liftLeft_transpose, h]

private theorem right_complement {c' : Type*} [Fintype c'] [DecidableEq c']
    (G : Matrix (d × w) c K) (T : Matrix (d × w) c' K)
    (h : range T.mulVecLin = ker G.transpose.mulVecLin) :
    range (liftRight (b := b) T).mulVecLin = ker (liftRight (b := b) G).transpose.mulVecLin := by
  ext y
  simp only [mem_range_liftRight, mem_ker_liftRight_transpose, h]

end
section

open Module LinearMap Matrix

variable {K : Type*} [Field K]

private theorem flow_lift_factor {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (N : Fin 3 → Matrix (Fin d) (Fin c) K) :
    flow M N = ((Matrix.kronecker (flatten M) (1 : Matrix (Fin d) (Fin d) K))).transpose *
      liftRight (b := Fin b) (flatten (fun r => (N r).transpose)) := by
  classical
  ext i j
  change (∑ r : Fin 3, M r i.1 j.1 * N r i.2 j.2) = _
  simp [Matrix.mul_apply,  liftRight, flatten, Matrix.transpose_apply,
    Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, eq_comm]

private theorem flow_both_transpose {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (N : Fin 3 → Matrix (Fin d) (Fin c) K) :
    flow (fun r => (M r).transpose) (fun r => (N r).transpose) =
      (flow M N).transpose := by
  ext i j
  rfl

private theorem assignment_castling {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (N : Fin 3 → Matrix (Fin d) (Fin c) K)
    (ha : a ≤ 3 * b) (hc : c ≤ 3 * d)
    (hm : Concise M) (hn : Concise (fun r => (N r).transpose)) :
    ∃ (S : Fin 3 → Matrix (Fin b) (Fin (3*b-a)) K)
      (T : Fin 3 → Matrix (Fin (3*d-c)) (Fin d) K),
      Concise (fun r => (S r).transpose) ∧ Concise T ∧
      ((a*d : ℕ) : ℤ) - (flow M N).rank =
        ((b*(3*d-c) : ℕ) : ℤ) - (flow S T).rank := by
  classical
  obtain ⟨S0, hs, hsrange, hsker⟩ := complement_matrix (flatten M) hm
    (k := 3*b-a) (by simpa [mul_comm] using Nat.sub_add_cancel ha)
  obtain ⟨T0, ht, htrange, htker⟩ := complement_matrix
    (flatten (fun r => (N r).transpose)) hn
    (k := 3*d-c) (by simpa [mul_comm] using Nat.sub_add_cancel hc)
  let S : Fin 3 → Matrix (Fin b) (Fin (3*b-a)) K := fun r j i => S0 (j,r) i
  let T : Fin 3 → Matrix (Fin (3*d-c)) (Fin d) K := fun r h l => T0 (l,r) h
  have hflatS : flatten (fun r => (S r).transpose) = S0 := rfl
  have hflatT : flatten T = T0 := rfl
  refine ⟨S,T,hs,ht,?_⟩
  let L := (Matrix.kronecker (flatten M) (1 : Matrix (Fin d) (Fin d) K))
  let R := liftRight (b := Fin b) (flatten (fun r => (N r).transpose))
  let LS := (Matrix.kronecker S0 (1 : Matrix (Fin d) (Fin d) K))
  let RT := liftRight (b := Fin b) T0
  have hL := liftLeft_injective (d := Fin d) (flatten M) hm
  have hRT := liftRight_injective (b := Fin b) T0 ht
  have hrt : range RT.mulVecLin = ker R.transpose.mulVecLin :=
    right_complement _ _ htrange
  have hls : ker LS.transpose.mulVecLin = range L.mulVecLin := by
    exact (left_complement S0 (flatten M) hsker.symm).symm
  have hdef := matrix_common_deficit L R LS RT hL hRT hrt hls
  have hflow : R.transpose * L = (flow M N).transpose := by
    rw [flow_lift_factor, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hpartner : LS.transpose * RT = (flow S T).transpose := by
    rw [← flow_both_transpose S T, flow_lift_factor, hflatS]
    rfl
  rw [hflow, hpartner, Matrix.rank_transpose, Matrix.rank_transpose] at hdef
  simpa using hdef

private theorem QMaxFlow_both_swap (a b c d : ℕ) :
    QMaxFlow a b c d = QMaxFlow b a d c := by
  have lower (a b c d : ℕ) : QMaxFlow a b c d ≤ QMaxFlow b a d c := by
    obtain ⟨M,N,h⟩ := QMaxFlow_attained a b c d
    have hr := rank_le_QMaxFlow (fun r => (M r).transpose) (fun r => (N r).transpose)
    rwa [flow_both_transpose, Matrix.rank_transpose, h] at hr
  exact le_antisymm (lower a b c d) (lower b a d c)

theorem castling_proved : Castling := by
  intro a b c d ha hc
  obtain ⟨M,N,hm,hn,hmax⟩ := concise_maximizer ha hc
  obtain ⟨S,T,hs,ht,hdef⟩ := assignment_castling M N ha hc hm hn
  rw [hmax] at hdef
  have hr := rank_le_QMaxFlow S T
  have ha' : 3*b-a ≤ 3*b := Nat.sub_le _ _
  have hc' : 3*d-c ≤ 3*d := Nat.sub_le _ _
  obtain ⟨P,Q,hp,hq,hmax'⟩ := concise_maximizer ha' hc'
  obtain ⟨R,U,hr',hu',hdef'⟩ := assignment_castling P Q ha' hc' hp hq
  have haa : 3*b-(3*b-a) = a := by omega
  have hcc : 3*d-(3*d-c) = c := by omega
  have hmaxswap : QMaxFlow (3*b-a) b (3*d-c) d =
      QMaxFlow b (3*b-a) d (3*d-c) := QMaxFlow_both_swap _ _ _ _
  have hr2 := rank_le_QMaxFlow R U
  conv_rhs at hr2 => rw [haa, hcc, ← QMaxFlow_both_swap a b c d]
  rw [hmax', hmaxswap] at hdef'
  conv_rhs at hdef' => lhs; rw [hcc]
  have hbalance : (3*b-a)*d+a*d = b*(3*d-c)+b*c := by
    have hb : (3*b-a)+a = 3*b := Nat.sub_add_cancel ha
    have hd : (3*d-c)+c = 3*d := Nat.sub_add_cancel hc
    nlinarith [congrArg (fun x : ℕ => x*d) hb, congrArg (fun x : ℕ => b*x) hd]
  have hbalanceZ : (((3*b-a)*d : ℕ) : ℤ) + ((a*d : ℕ) : ℤ) =
      ((b*(3*d-c) : ℕ) : ℤ) + ((b*c : ℕ) : ℤ) := by exact_mod_cast hbalance
  omega

end

end D5.S3.Quantum.TensorNetworks.BridgeGraph.CastlingDeficit
