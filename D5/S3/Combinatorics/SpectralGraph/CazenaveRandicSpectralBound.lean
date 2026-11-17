/- GID: D5/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/CazenaveRandicSpectralBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Connected graphs satisfy the Randic plus second-Laplacian spectral bound. -/

/-
   admission_basis: open-problem-resolution (#26532; Proved).
   escape_witness: none.
   adjEig: proof_shape: bind-only; consumers: claim, adjacency_degree_bound, result.
   randic: proof_shape: bind-only; consumers: claim, randic_lower, result.
   claim: proof_shape: bind-only; consumers: result.
   spectral_upper_of_supersolution: proof_shape: bind-only; consumers: adjacency_degree_bound.
   rayleigh_le_second: proof_shape: bind-only; consumers: lap_second_degree.
   lap_second_degree: proof_shape: bind-only; consumers: result.
   adjacency_degree_bound: proof_shape: bind-only; consumers: result.
   randic_lower: proof_shape: bind-only; consumers: result.
   result: proof_shape: bind-only; escape_witness: none; consumers: external settlement #26532.
   Direct frozen dependencies:
   D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio.lapEig;
   declaration statement_id: sha256:eda0b70a8c5ea56bbd5dea6f6726ddadf958c9aa40fa7abc33647ba73f8c4369.
   Used by claim, lap_second_degree and result; all other declarations: none.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/29101.
   The adjacency spectrum uses decreasing algebraic order; the edge sum counts each edge once.
-/

import D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio

namespace D5.S3.Combinatorics.SpectralGraph.CazenaveRandicSpectralBound

open scoped BigOperators

/-- Ordinary adjacency eigenvalues in decreasing algebraic order, with multiplicity. -/
noncomputable def adjEig {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i : Fin n) : ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

/-- The source sum over unordered edges, each counted once. -/
noncomputable def randic {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : ℝ :=
  ∑ e ∈ G.edgeFinset,
    Sym2.lift ⟨fun u v : Fin n =>
      1 / Real.sqrt ((G.degree u : ℝ) * (G.degree v : ℝ)),
      fun u v => congrArg (fun t : ℝ => 1 / Real.sqrt t) (mul_comm (G.degree u : ℝ) (G.degree v : ℝ))⟩ e

/-- Conjecture 4 (#112951), with graph order n+2 ranging over every order at least two. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 2))) [DecidableRel G.Adj],
    G.Connected →
      adjEig G (0 : Fin (n + 2)) ≤ randic G +
        D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio.lapEig
          G (1 : Fin (n + 2))

end D5.S3.Combinatorics.SpectralGraph.CazenaveRandicSpectralBound

open Matrix Finset
open scoped InnerProductSpace
noncomputable section
set_option maxHeartbeats 1000000
namespace D5.S3.Combinatorics.SpectralGraph.CazenaveRandicSpectralBound

private theorem spectral_upper_of_supersolution {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsHermitian) (h : V → ℝ) (c : ℝ)
    (hpos : ∀ i, 0 < h i) (hAn : ∀ i j, 0 ≤ A i j)
    (hsup : ∀ i, (A *ᵥ h) i ≤ c * h i) (j : V) : hA.eigenvalues j ≤ c := by
  let x : V → ℝ := hA.eigenvectorBasis j
  have hx : x ≠ 0 := by
    intro hz
    have hv := (hA.eigenvectorBasis).orthonormal.ne_zero j
    apply hv
    exact (WithLp.ofLp_eq_zero 2).mp hz
  obtain ⟨k,hk⟩ : ∃ k, x k ≠ 0 := Function.ne_iff.mp hx
  letI : Nonempty V := ⟨k⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image univ (fun t => |x t| / h t) (by simp : (univ : Finset V).Nonempty)
  have hib (t : V) : |x t| ≤ (|x i| / h i) * h t := by
    exact (div_le_iff₀ (hpos t)).mp (hi t (mem_univ t))
  have hxi : 0 < |x i| := by
    have hkpos : 0 < |x k| / h k := div_pos (abs_pos.mpr hk) (hpos k)
    have hh := hi k (mem_univ k)
    exact (div_pos_iff_of_pos_right (hpos i)).mp (lt_of_lt_of_le hkpos hh)
  have he := congrFun (hA.mulVec_eigenvectorBasis j) i
  change (A *ᵥ x) i = hA.eigenvalues j * x i at he
  have hb : |(A *ᵥ x) i| ≤ (|x i| / h i) * (A *ᵥ h) i := by
    calc
      _ ≤ ∑ t, |A i t * x t| := abs_sum_le_sum_abs _ _
      _ = ∑ t, A i t * |x t| := by simp_rw [abs_mul, abs_of_nonneg (hAn i _)]
      _ ≤ ∑ t, A i t * ((|x i| / h i) * h t) := sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hib t) (hAn i t))
      _ = _ := by simp only [mulVec, dotProduct, Finset.mul_sum]; apply sum_congr rfl; intro t _ <;> ring
  have hc : |(A *ᵥ x) i| ≤ c * |x i| := by
    calc
      _ ≤ (|x i| / h i) * (c * h i) := hb.trans (mul_le_mul_of_nonneg_left (hsup i) (div_nonneg (abs_nonneg _) (hpos i).le))
      _ = _ := by field_simp [(hpos i).ne'] <;> ring
  rw [he, abs_mul] at hc
  exact (le_abs_self _).trans ((mul_le_mul_iff_left₀ hxi).mp hc)


private theorem rayleigh_le_second {n : ℕ} (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ)
    (hA : A.IsHermitian) (x : Fin (n+2) → ℝ)
    (hz : ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
      finrank_euclideanSpace).repr (WithLp.toLp 2 x) 0 = 0) :
    x ⬝ᵥ (A *ᵥ x) ≤ hA.eigenvalues₀ (Fin.cast (Fintype.card_fin (n+2)).symm 1) * (x ⬝ᵥ x) := by
  let T := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let B := T.eigenvectorBasis finrank_euclideanSpace
  let y := WithLp.toLp 2 x
  have he : inner ℝ (A.toEuclideanLin y) y =
      ∑ i, hA.eigenvalues₀ i * (B.repr y i)^2 := by
    rw [← B.repr.inner_map_map (A.toEuclideanLin y) y, PiLp.inner_apply]
    apply sum_congr rfl
    intro i _
    rw [RCLike.inner_apply, T.eigenvectorBasis_apply_self_apply]
    simp only [RCLike.conj_to_real, RCLike.ofReal_real_eq_id, id_eq,
      Matrix.IsHermitian.eigenvalues₀]
    ring
  have hn : ∑ i, (B.repr y i)^2 = inner ℝ y y := by
    rw [← B.repr.inner_map_map y y, PiLp.inner_apply]
    apply sum_congr rfl
    intro i _
    simp [pow_two]
  have hh : (∑ i, hA.eigenvalues₀ i * (B.repr y i)^2) ≤
      ∑ i, hA.eigenvalues₀ (Fin.cast (Fintype.card_fin (n+2)).symm 1) * (B.repr y i)^2 := by
    apply sum_le_sum
    intro i _
    by_cases hi : i = 0
    · subst i
      change hA.eigenvalues₀ 0 * (B.repr y 0)^2 ≤ _
      have hz' : B.repr y 0 = 0 := hz
      simp [hz']
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply hA.eigenvalues₀_antitone
      have hi' : 1 ≤ i.val := by
        have hne : i.val ≠ 0 := by
          exact Fin.val_ne_zero_iff.mpr hi
        omega
      exact hi'
  rw [← mul_sum, hn, ← he] at hh
  simpa only [y, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, star_trivial, dotProduct_comm] using hh

private theorem lap_second_degree {n : ℕ} (G : SimpleGraph (Fin (n+2))) [DecidableRel G.Adj]
    (u v : Fin (n+2)) (huv : u ≠ v) (hd : G.degree v ≤ G.degree u) :
    (G.degree v : ℝ) - 1 ≤
      D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio.lapEig G 1 := by
  let L := G.lapMatrix ℝ
  let hL := G.isHermitian_lapMatrix ℝ
  let B := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hL).eigenvectorBasis finrank_euclideanSpace
  let f : (Fin (n+2) → ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun z => B.repr (WithLp.toLp 2 z) 0
    map_add' := by intro z t; simp
    map_smul' := by intro a z; simp }

  let e : Fin (n+2) → Fin (n+2) → ℝ := fun i => Pi.single i 1
  obtain ⟨a,b,hab,hf⟩ : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ f (a • e u + b • e v) = 0 := by
    by_cases hv : f (e v) = 0
    · exact ⟨0,1,Or.inr one_ne_zero,by simpa using hv⟩
    · refine ⟨f (e v), -f (e u), Or.inl hv, ?_⟩
      simp only [map_add,map_smul,smul_eq_mul] <;> ring
  let x := a • e u + b • e v
  have hxu : x u = a := by simp [x,e,huv,huv.symm]
  have hxv : x v = b := by simp [x,e,huv,huv.symm]
  have hx : x ≠ 0 := by
    intro hx
    have ha : a = 0 := by exact (AddSemiconjBy.eq_zero_iff (x u) (congrFun (congrArg HAdd.hAdd hxu) (x u))).mp (congrFun hx u)
    have hb : b = 0 := by exact (AddSemiconjBy.eq_zero_iff (x v) (congrFun (congrArg HAdd.hAdd hxv) (x v))).mp (congrFun hx v)
    exact hab.elim (fun h => h ha) (fun h => h hb)
  have hn : 0 < x ⬝ᵥ x := by
    simpa only [star_trivial] using (dotProduct_star_self_pos_iff.mpr hx)
  have hnorm : x ⬝ᵥ x = a^2+b^2 := by
    simp [x,e,dotProduct_add,add_dotProduct,dotProduct_smul,smul_dotProduct,
      Pi.single_apply,huv,huv.symm,pow_two]
  have hform : x ⬝ᵥ (L *ᵥ x) =
      (G.degree u : ℝ)*a^2 + (G.degree v : ℝ)*b^2 -
        2*(if G.Adj u v then 1 else 0)*a*b := by
    by_cases hadj : G.Adj u v
    all_goals simp [hadj,x,e,L,add_mulVec,mulVec_add,mulVec_smul,add_dotProduct,dotProduct_add,
      smul_dotProduct,dotProduct_smul,SimpleGraph.lapMatrix,SimpleGraph.degMatrix,
      SimpleGraph.adjMatrix,Matrix.diagonal,huv,huv.symm,G.adj_comm,pow_two]
    <;> ring
  have hlow : ((G.degree v : ℝ)-1)*(x ⬝ᵥ x) ≤ x ⬝ᵥ (L *ᵥ x) := by
    rw [hnorm,hform]
    have hd' : (G.degree v : ℝ) ≤ G.degree u := by exact Nat.cast_le.mpr hd
    by_cases he : G.Adj u v
    · simp only [he,ite_true]
      nlinarith [mul_nonneg (sub_nonneg.mpr hd') (sq_nonneg a),sq_nonneg (a-b)]
    · simp only [he,ite_false]
      nlinarith [mul_nonneg (sub_nonneg.mpr hd') (sq_nonneg a),sq_nonneg a,sq_nonneg b]
  have hh := rayleigh_le_second L hL x (by exact hf)
  change x ⬝ᵥ (L *ᵥ x) ≤
    D5.S3.Combinatorics.SpectralGraph.LinWangCaiBroomSpectralRatio.lapEig G 1 * (x ⬝ᵥ x) at hh
  exact (mul_le_mul_iff_left₀ hn).mp (hlow.trans hh)


private theorem adjacency_degree_bound {n : ℕ} (G : SimpleGraph (Fin (n+2))) [DecidableRel G.Adj]
    (u : Fin (n+2)) (d : ℕ) (hu : 0 < G.degree u) (hd : 1 ≤ d)
    (hsec : ∀ x, x ≠ u → G.degree x ≤ d) :
    adjEig G 0 ≤ Real.sqrt (G.degree u : ℝ) + d - 1 := by
  let r := Real.sqrt (G.degree u : ℝ)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hu)
  have hr1 : 1 ≤ r := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast hu
  have hrsq : r^2 = (G.degree u : ℝ) := Real.sq_sqrt (by positivity)
  let h : Fin (n+2) → ℝ := fun i => if i=u then r else 1
  have hpos (i) : 0 < h i := by dsimp [h]; split_ifs <;> positivity
  have hsum (i : Fin (n+2)) : (G.adjMatrix ℝ *ᵥ h) i =
      (G.degree i : ℝ) + if G.Adj i u then r-1 else 0 := by
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    have he (j : Fin (n+2)) : h j = 1 + if j=u then r-1 else 0 := by dsimp [h]; split_ifs <;> ring
    simp_rw [he,Finset.sum_add_distrib]
    simp [SimpleGraph.card_neighborFinset_eq_degree,G.mem_neighborFinset]
  have hsup (i : Fin (n+2)) : (G.adjMatrix ℝ *ᵥ h) i ≤ (r+d-1)*h i := by
    rw [hsum]
    by_cases hi : i=u
    · subst i
      simp only [G.irrefl,ite_false,add_zero,h,ite_true]
      have hd' : (1 : ℝ) ≤ d := by exact Nat.one_le_cast.mpr hd
      nlinarith [mul_nonneg (sub_nonneg.mpr hd') hr.le]
    · have hd' : (G.degree i : ℝ) ≤ d := by exact Nat.cast_le.mpr (hsec i hi)
      simp only [h,if_neg hi,mul_one]
      split_ifs <;> linarith
  let e : Fin (Fintype.card (Fin (n+2))) ≃ Fin (n+2) := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hb := spectral_upper_of_supersolution (G.adjMatrix ℝ) (G.isHermitian_adjMatrix ℝ) h
    (r+d-1) hpos (fun i j => by simp only [SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num) hsup
    (e (Fin.cast (Fintype.card_fin (n+2)).symm 0))
  simpa only [Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply,adjEig] using hb

private theorem randic_lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) (hmax : ∀ v, G.degree v ≤ G.degree u) (hu : 0 < G.degree u) :
    Real.sqrt (G.degree u : ℝ) ≤ randic G := by
  classical
  let r := Real.sqrt (G.degree u : ℝ)
  have hr : 0 < r := Real.sqrt_pos.mpr (by exact_mod_cast hu)
  let w : Fin n → Fin n → ℝ := fun x y => 1 / Real.sqrt ((G.degree x : ℝ)*(G.degree y : ℝ))
  have wsym : ∀ x y, w x y = w y x :=
    fun x y => congrArg (fun t : ℝ => 1/Real.sqrt t) (mul_comm (G.degree x : ℝ) (G.degree y : ℝ))
  let q : Fin n → Fin n → ℝ := fun x y =>
    if G.Adj u x then (if y=u then 1 else (1/2 : ℝ))*w x y else 0
  have qnn (x y) : 0 ≤ q x y := by dsimp [q]; split_ifs <;> positivity
  have qedge (x y) (hxy : G.Adj x y) : q x y + q y x ≤ w x y := by
    have hwn : 0 ≤ w x y := one_div_nonneg.mpr (Real.sqrt_nonneg _)
    by_cases hx : x=u
    · subst x
      simp [q,G.irrefl,hxy,wsym]
    by_cases hy : y=u
    · subst y
      simp [q,G.irrefl,hxy.symm,wsym]
    dsimp [q]
    split_ifs <;> (try rw [wsym y x]) <;> nlinarith
  have oriented (f : Fin n → Fin n → ℝ) (hsym : ∀ x y, f x y = f y x) :
      (∑ d : G.Dart, f d.fst d.snd) = 2 * ∑ e ∈ G.edgeFinset, e.lift ⟨f,hsym⟩ := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset G.Dart)) (t := G.edgeFinset)
      (g := SimpleGraph.Dart.edge) (fun d _ => G.mem_edgeFinset.mpr d.edge_mem)
      (fun d => f d.fst d.snd),Finset.mul_sum]
    apply sum_congr rfl
    intro e he
    have hf : ∀ d ∈ (univ.filter fun d : G.Dart => d.edge=e),
        f d.fst d.snd = e.lift ⟨f,hsym⟩ := by
      intro d hd; rw [← (mem_filter.mp hd).2]; rfl
    rw [sum_congr rfl hf,sum_const,nsmul_eq_mul,G.dart_edge_fiber_card e (G.mem_edgeFinset.mp he)]
    norm_num
  have reindex (f : Fin n → Fin n → ℝ) :
      (∑ d : G.Dart, f d.fst d.snd) = ∑ x, ∑ y ∈ G.neighborFinset x, f x y := by
    rw [← Finset.sum_fiberwise (univ : Finset G.Dart) (fun d => d.fst)]
    apply sum_congr rfl
    intro x _
    refine sum_bij (fun d _ => d.snd) ?_ ?_ ?_ ?_
    · intro d hd; exact (G.mem_neighborFinset x d.snd).mpr ((mem_filter.mp hd).2 ▸ d.adj)
    · intro d hd e he hde
      apply SimpleGraph.Dart.ext
      exact Prod.ext ((mem_filter.mp hd).2.trans (mem_filter.mp he).2.symm) hde
    · intro y hy
      let d : G.Dart := ⟨(x,y),(G.mem_neighborFinset x y).mp hy⟩
      exact ⟨d,by simp [d],rfl⟩
    · intro d hd; simp only [(mem_filter.mp hd).2]
  have qswap : (∑ d : G.Dart, q d.snd d.fst) = ∑ d : G.Dart, q d.fst d.snd :=
    Fintype.sum_bijective SimpleGraph.Dart.symm SimpleGraph.Dart.symm_involutive.bijective
      (fun d => q d.snd d.fst) (fun d => q d.fst d.snd) (fun _ => rfl)
  have qupper : (∑ d : G.Dart, q d.fst d.snd) ≤ randic G := by
    have h := sum_le_sum (s := (univ : Finset G.Dart)) (fun d _ => qedge d.fst d.snd d.adj)
    rw [sum_add_distrib,qswap,oriented w wsym] at h
    change _ ≤ 2 * randic G at h
    linarith
  have local_lower (x : Fin n) (hux : G.Adj u x) :
      1/r ≤ ∑ y ∈ G.neighborFinset x, q x y := by
    have hx : 0 < (G.degree x : ℝ) := Nat.cast_pos.mpr hux.degree_pos_right
    let s := Real.sqrt (G.degree x : ℝ)
    have hs : 0 < s := Real.sqrt_pos.mpr hx
    have hssq : s^2 = (G.degree x : ℝ) := Real.sq_sqrt hx.le
    have hw (y : Fin n) (hxy : G.Adj x y) : 1/(r*s) ≤ w x y := by
      apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (mul_pos hx (by exact_mod_cast hxy.degree_pos_right)))
      calc
        Real.sqrt ((G.degree x : ℝ)*(G.degree y : ℝ)) ≤ Real.sqrt ((G.degree x : ℝ)*(G.degree u : ℝ)) := by
          apply Real.sqrt_le_sqrt
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmax y) hx.le
        _ = r*s := by rw [Real.sqrt_mul hx.le]; dsimp [r,s] <;> ring
    have hmem : u ∈ G.neighborFinset x := (G.mem_neighborFinset x u).mpr hux.symm
    have coeff : (∑ y ∈ G.neighborFinset x, (if y=u then 1 else (1/2 : ℝ))) = ((G.degree x : ℝ)+1)/2 := by
      have he : ∀ y : Fin n, (if y=u then 1 else (1/2 : ℝ)) = 1/2 + if y=u then 1/2 else 0 := by intro y; split_ifs <;> norm_num
      simp_rw [he,sum_add_distrib]
      simp [hmem,SimpleGraph.card_neighborFinset_eq_degree]
      <;> ring
    have hsum : ((G.degree x : ℝ)+1)/2 * (1/(r*s)) ≤ ∑ y ∈ G.neighborFinset x, q x y := by
      rw [← coeff,Finset.sum_mul]
      apply sum_le_sum
      intro y hy
      dsimp [q]; rw [if_pos hux]
      exact mul_le_mul_of_nonneg_left (hw y ((G.mem_neighborFinset x y).mp hy)) (by split_ifs <;> norm_num)
    have ha : 1/r ≤ ((G.degree x : ℝ)+1)/2 * (1/(r*s)) := by
      rw [mul_one_div]
      apply (le_div_iff₀ (mul_pos hr hs)).mpr
      have he : (1/r)*(r*s) = s := by field_simp [hr.ne'] <;> ring
      rw [he]
      nlinarith [sq_nonneg (s-1)]
    exact ha.trans hsum
  have htotal : (G.degree u : ℝ) / r ≤ ∑ x, ∑ y ∈ G.neighborFinset x, q x y := by
    calc
      _ = ∑ x ∈ G.neighborFinset u, (1/r) := by simp [SimpleGraph.card_neighborFinset_eq_degree] <;> ring
      _ ≤ ∑ x ∈ G.neighborFinset u, ∑ y ∈ G.neighborFinset x, q x y := by
        apply sum_le_sum; intro x hx; exact local_lower x ((G.mem_neighborFinset u x).mp hx)
      _ ≤ ∑ x, ∑ y ∈ G.neighborFinset x, q x y := by
        apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
        intro x hx hnx; exact sum_nonneg (fun y _ => qnn x y)
  have he : (G.degree u : ℝ)/r = r := Real.div_sqrt
  rw [he,← reindex q] at htotal
  exact htotal.trans qupper


theorem result : claim := by
  intro n G _ hG
  classical
  obtain ⟨u,_,hu⟩ := exists_max_image (univ : Finset (Fin (n+2))) (fun x => G.degree x) (by simp)
  have hmax (x : Fin (n+2)) : G.degree x ≤ G.degree u := hu x (mem_univ x)
  have hs : (univ.erase u : Finset (Fin (n+2))).Nonempty := by
    obtain ⟨v,hv⟩ := exists_ne u
    exact ⟨v,by simp [hv]⟩
  obtain ⟨v,hv,hsec⟩ := exists_max_image (univ.erase u) (fun x => G.degree x) hs
  have hvu : v ≠ u := (mem_erase.mp hv).1
  have hpos (x : Fin (n+2)) : 0 < G.degree x := hG.preconnected.degree_pos_of_nontrivial x
  have ha := adjacency_degree_bound G u (G.degree v) (hpos u) (hpos v)
    (fun x hx => hsec x (by simp [hx]))
  have hr := randic_lower G u hmax (hpos u)
  have hl := lap_second_degree G u v hvu.symm (hmax v)
  linarith

end D5.S3.Combinatorics.SpectralGraph.CazenaveRandicSpectralBound
