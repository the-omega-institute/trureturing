/- GID: D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FiedlerResistanceTripartiteOptimizer
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Original labelled tripartite Laplacians and their harmonic resistance ceiling. -/
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer

/-! Weighted Laplacians on the original labelled vertices. -/
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer
open FiedlerResistanceInvariantWeightsRefutation FiedlerResistanceK2mOptimizer

private lemma energy_double {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) :
    2 * dotProduct x (wLap G w *ᵥ x) =
      ∑ i, ∑ j with G.Adj i j, w s(i,j) * (x i - x j)^2 := by
  have hs : (∑ i, ∑ j with G.Adj i j, x j * (w s(i,j) * (x j-x i))) =
      ∑ i, ∑ j with G.Adj i j, x i * (w s(i,j) * (x i-x j)) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [G.adj_comm j i, Sym2.eq_swap]
  have hE : dotProduct x (wLap G w *ᵥ x) =
      ∑ i, ∑ j with G.Adj i j, x i*(w s(i,j)*(x i-x j)) := by
    simp only [dotProduct, lap_mul, Finset.mul_sum]
  rw [hE]
  rw [show (2:ℝ) * (∑ i, ∑ j with G.Adj i j, x i * (w s(i,j)*(x i-x j))) =
    (∑ i, ∑ j with G.Adj i j, x i * (w s(i,j)*(x i-x j))) +
    (∑ i, ∑ j with G.Adj i j, x j * (w s(i,j)*(x j-x i))) by rw [hs]; ring]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma lap_psd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ i j, G.Adj i j → 0 ≤ w s(i,j)) :
    (wLap G w).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (lap_hermitian G w)
  intro x
  have h : 0 ≤ ∑ i, ∑ j with G.Adj i j, w s(i,j)*(x i-x j)^2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact Finset.sum_nonneg fun j hj => mul_nonneg (hw i j (Finset.mem_filter.mp hj).2) (sq_nonneg _)
  rw [← energy_double] at h
  simp only [star_trivial]
  linarith

private lemma rayleigh_lower {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : (wLap G w).PosSemidef)
    (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    lambda2 G w * dotProduct x x ≤ dotProduct x (wLap G w *ᵥ x) := by
  by_cases hz : x = 0
  · subst x; simp
  have hn : 0 < dotProduct x x := by
    simpa only [star_trivial] using (dotProduct_star_self_pos_iff.mpr hz)
  have hB : BddBelow {r : ℝ | ∃ y : Fin n → ℝ, y ≠ 0 ∧ ∑ i, y i=0 ∧
      r=dotProduct y (wLap G w *ᵥ y)/dotProduct y y} := by
    refine ⟨0, ?_⟩
    rintro r ⟨y,hy,hs,rfl⟩
    exact div_nonneg (by simpa only [star_trivial] using hw.dotProduct_mulVec_nonneg y)
      (by simpa only [star_trivial] using dotProduct_star_self_nonneg y)
  exact (le_div_iff₀ hn).mp (csInf_le hB ⟨x,hz,hx,rfl⟩)

private lemma centered_psd {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hR : ∀ x : Fin n → ℝ, ∑ i, x i=0 →
      dotProduct x x ≤ dotProduct x (wLap G w *ᵥ x)) :
    (wLap G w - (1-constProj n)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((lap_hermitian G w).sub ((Matrix.isHermitian_one).sub (proj_hermitian n)))
  intro x
  let c : ℝ := (∑ i, x i)/n
  let y : Fin n → ℝ := x-c • (1 : Fin n → ℝ)
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hy : ∑ i, y i=0 := by
    simp [y,c,Finset.sum_sub_distrib]
    field_simp
    <;> ring
  have hLy : wLap G w *ᵥ y = wLap G w *ᵥ x := by
    simp [y,Matrix.mulVec_sub,Matrix.mulVec_smul,lap_one]
  have hE : dotProduct y (wLap G w *ᵥ y) = dotProduct x (wLap G w *ᵥ x) := by
    rw [hLy]
    simp only [y,sub_dotProduct,smul_dotProduct]
    have hs : dotProduct (1 : Fin n → ℝ) (wLap G w *ᵥ x) = 0 := by
      simpa [dotProduct] using lap_sum G w x
    rw [hs,smul_zero,sub_zero]
  have hN : dotProduct y y = dotProduct x x - (∑ i,x i)^2/n := by
    simp only [y,dotProduct,Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
    simp_rw [show ∀ i, (x i-c)*(x i-c)=x i*x i-2*c*x i+c*c from fun i => by ring]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp [c]
    field_simp
    <;> ring
  have h := hR y hy
  rw [hE,hN] at h
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub]
  rw [proj_energy]
  linarith


private def green {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) := (wLap G w + constProj n)⁻¹

private lemma green_properties {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hB : (wLap G w + constProj n).PosDef) :
    (green G w).PosDef ∧ wLap G w * green G w = 1 - constProj n ∧
    green G w * wLap G w = 1 - constProj n ∧
    green G w * constProj n = constProj n ∧ constProj n * green G w = constProj n := by
  have hN : (green G w).PosDef := hB.inv
  have hBN : (wLap G w + constProj n) * green G w = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)
  have hNB : green G w * (wLap G w + constProj n) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)
  have hBP : (wLap G w + constProj n) * constProj n = constProj n := by
    rw [add_mul, lap_proj, proj_sq hn, zero_add]
  have hNP : green G w * constProj n = constProj n := by
    calc
      _ = green G w * ((wLap G w + constProj n) * constProj n) := by rw [hBP]
      _ = _ := by rw [← mul_assoc,hNB,one_mul]
  have hPN : constProj n * green G w = constProj n := by
    have h := congrArg Matrix.transpose hNP
    simpa only [Matrix.transpose_mul,hN.1.isSymm.eq,(proj_hermitian n).isSymm.eq] using h
  refine ⟨hN, ?_, ?_, hNP, hPN⟩
  · rw [add_mul,hPN] at hBN
    exact eq_sub_iff_add_eq.mpr hBN
  · rw [mul_add,hNP] at hNB
    exact eq_sub_iff_add_eq.mpr hNB

private lemma harmonic_unique {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hL : (wLap G w).PosSemidef) (hB : (wLap G w + constProj n).PosDef)
    (p q : Fin n) (x y : Fin n → ℝ) (hx : Harmonic G w p q x)
    (hy : Harmonic G w p q y) : x = y := by
  have hp : (x-y) p=0 := by simp [hx.1,hy.1]
  have hq : (x-y) q=0 := by simp [hx.2.1,hy.2.1]
  have hE : dotProduct (x-y) (wLap G w *ᵥ (x-y))=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hip : i=p
    · subst i; simp [hp]
    by_cases hiq : i=q
    · subst i; simp [hq]
    simp [Matrix.mulVec_sub,hx.2.2 i hip hiq,hy.2.2 i hip hiq]
  have hz : wLap G w *ᵥ (x-y)=0 :=
    hL.dotProduct_mulVec_zero_iff.mp (by simpa only [star_trivial] using hE)
  have he := congrArg (fun z => green G w *ᵥ z) hz
  rw [Matrix.mulVec_mulVec,(green_properties hn G w hB).2.2.1,
    Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.mulVec_zero] at he
  have hc : x-y = constProj n *ᵥ (x-y) := sub_eq_zero.mp he
  have hsum : (∑ i,(x-y) i)/n=0 := by
    have h := congrFun hc p
    rw [proj_mul,hp] at h
    exact h.symm
  apply sub_eq_zero.mp
  rw [hc]
  ext i
  rw [proj_mul,hsum]
  rfl

private lemma harmonic_green {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hL : (wLap G w).PosSemidef) (hB : (wLap G w + constProj n).PosDef)
    (p q : Fin n) (hpq : p ≠ q) :
    (∃! x, Harmonic G w p q x) ∧
    effRes G w p q = green G w p p + green G w q q - green G w p q - green G w q p := by
  let v := green G w *ᵥ delta p q
  let d := v p-v q
  have hLv : wLap G w *ᵥ v = delta p q := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec,(green_properties hn G w hB).2.1,
      Matrix.sub_mulVec,Matrix.one_mulVec,proj_delta,sub_zero]
  have hd : 0 < d := by
    have h := (green_properties hn G w hB).1.dotProduct_mulVec_pos (delta_ne hpq)
    simpa only [star_trivial,delta_dot] using h
  let h : Fin n → ℝ := fun i => (v i-v q)/d
  have hLp : wLap G w *ᵥ h = d⁻¹ • delta p q := by
    have he : h=d⁻¹ • (v-v q • (1 : Fin n → ℝ)) := by
      ext i; simp [h,div_eq_mul_inv,mul_comm]
    rw [he,Matrix.mulVec_smul,Matrix.mulVec_sub,Matrix.mulVec_smul,
      lap_one,smul_zero,sub_zero,hLv]
  have hh : Harmonic G w p q h := by
    refine ⟨div_self hd.ne',by simp [h],?_⟩
    intro k hkp hkq
    rw [hLp]
    simp [delta,hkp,hkq]
  have he : harmonicExt G w p q=h := by
    unfold harmonicExt
    rw [dif_pos ⟨h,hh⟩]
    exact harmonic_unique hn G w hL hB p q _ h (Classical.choose_spec _) hh
  refine ⟨⟨h,hh,fun y hy => harmonic_unique hn G w hL hB p q y h hy hh⟩,?_⟩
  rw [effRes,if_neg hpq,he,hLp]
  simp only [Pi.smul_apply,smul_eq_mul,delta,Pi.sub_apply,Pi.single_eq_same,
    Pi.single_eq_of_ne hpq,mul_one,sub_zero,one_div,inv_inv]
  dsimp [d,v]
  simp only [delta,Matrix.mulVec_sub,Matrix.mulVec_single_one,Matrix.col_apply,Pi.sub_apply]
  ring

private lemma resistance_trace {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hL : (wLap G w).PosSemidef) (hB : (wLap G w + constProj n).PosDef) :
    totalRes G w = n * ((green G w).trace-1) := by
  have he (p q : Fin n) : effRes G w p q =
      green G w p p+green G w q q-green G w p q-green G w q p := by
    by_cases hpq : p=q
    · subst q; simp [effRes]
    · exact (harmonic_green hn G w hL hB p q hpq).2
  have hp (p q : Fin n) : pairRes G w s(p,q) =
      green G w p p+green G w q q-green G w p q-green G w q p := by
    simp only [pairRes,Sym2.lift_mk,he]
    rcases le_total p q with hpq | hqp
    · rw [min_eq_left hpq,max_eq_right hpq]
    · rw [min_eq_right hqp,max_eq_left hqp]; ring
  let f := fun p q => green G w p p+green G w q q-green G w p q-green G w q p
  have hs : (Finset.univ : Finset (Fin n)).sym2 = Finset.univ := by ext p; simp
  have ht : ((Finset.univ : Finset (Fin n)).offDiag.filter fun p => p.1<p.2) =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1<p.2) := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_offDiag,Finset.mem_univ,
      Finset.mem_product,true_and]
    exact and_iff_right_of_imp fun h => ne_of_lt h
  have htw : 2 * totalRes G w = ∑ p,∑ q,f p q := by
    rw [totalRes,← hs,Finset.sum_sym2_filter_not_isDiag,ht]
    simp only [Finset.sum_filter,Finset.sum_product,hp]
    simpa only [f,Finset.sum_filter] using
      (double_sum_lt f (by intro i j; dsimp [f]; ring) (by intro i; dsimp [f]; ring)).symm
  have hrow (i : Fin n) : ∑ j, green G w i j = 1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i ⟨0,hn⟩)
      (green_properties hn G w hB).2.2.2.1
    simp only [Matrix.mul_apply,constProj,← Finset.sum_mul] at h
    have hn0 : (n:ℝ) ≠ 0 := by positivity
    apply mul_right_cancel₀ (inv_ne_zero hn0)
    simpa only [one_mul] using h
  have hsum : (∑ p,∑ q,green G w p q)=(n:ℝ) := by simp_rw [hrow]; simp
  have hsum' : (∑ p,∑ q,green G w q p)=(n:ℝ) := by rw [Finset.sum_comm]; exact hsum
  dsimp [f] at htw
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_mul,
    ← Finset.mul_sum,hsum,hsum'] at htw
  simp only [Matrix.trace,Matrix.diag_apply]
  nlinarith

private lemma resistance_spectral {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hL : (wLap G w).PosSemidef) (hB : (wLap G w + constProj n).PosDef) :
    totalRes G w = n * ∑ i, ((lap_hermitian G w).eigenvalues i)⁻¹ := by
  let L := wLap G w
  let P := constProj n
  let T := green G w-P
  have hLT : L*T=1-P := by
    dsimp [L,T,P]
    rw [mul_sub,(green_properties hn G w hB).2.1,lap_proj,sub_zero]
  have hPT : P*T=0 := by
    dsimp [P,T]
    rw [mul_sub,(green_properties hn G w hB).2.2.2.2,proj_sq hn,sub_self]
  have h := AlbrightKemenyEdgeDerivativeRefutation.reciprocalRoots_eq_trace
    L P T (lap_hermitian G w) hLT (lap_proj G w) hPT
  rw [AlbrightKemenyEdgeDerivativeRefutation.reciprocalRoots_eq_sum L (lap_hermitian G w)] at h
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hPtr : P.trace=1 := by simp [P,Matrix.trace,constProj,hn0]
  rw [resistance_trace hn G w hL hB]
  congr 1
  rw [h]
  dsimp [T]
  rw [Matrix.trace_sub,hPtr]


private lemma positive_kernel {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.Connected) (w : Sym2 (Fin n) → ℝ)
    (hw : ∀ i j, G.Adj i j → 0 < w s(i,j)) (x : Fin n → ℝ)
    (hx : dotProduct x (wLap G w *ᵥ x)=0) : ∃ c : ℝ, x=fun _ => c := by
  have hsum : (∑ i, ∑ j with G.Adj i j, w s(i,j)*(x i-x j)^2)=0 := by
    rw [← energy_double,hx,mul_zero]
  have hnon (i j : Fin n) (hij : G.Adj i j) : 0 ≤ w s(i,j)*(x i-x j)^2 :=
    mul_nonneg (hw i j hij).le (sq_nonneg _)
  have hedge (i j : Fin n) (hij : G.Adj i j) : x i=x j := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      Finset.sum_nonneg fun l hl => hnon k l (Finset.mem_filter.mp hl).2)).mp hsum i (mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk =>
      hnon i k (Finset.mem_filter.mp hk).2)).mp hi j (by simp [hij])
    have hz := (mul_eq_zero.mp hj).resolve_left (hw i j hij).ne'
    nlinarith [sq_nonneg (x i-x j)]
  have hreach (i j : Fin n) (h : G.Reachable i j) : x i=x j := by
    obtain ⟨v⟩ := h
    induction v with
    | nil => rfl
    | cons ha _ ih => exact (hedge _ _ ha).trans ih
  refine ⟨x ⟨0,hn⟩,?_⟩
  funext i
  exact hreach i ⟨0,hn⟩ (hG i ⟨0,hn⟩)

private lemma positive_shift {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.Connected) (w : Sym2 (Fin n) → ℝ)
    (hw : ∀ i j, G.Adj i j → 0 < w s(i,j)) :
    (wLap G w+constProj n).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos ((lap_hermitian G w).add (proj_hermitian n))
  intro x hx
  simp only [star_trivial,Matrix.add_mulVec,dotProduct_add,proj_energy]
  have hE : 0 ≤ dotProduct x (wLap G w *ᵥ x) := by
    simpa only [star_trivial] using (lap_psd G w (fun i j hij => (hw i j hij).le)).dotProduct_mulVec_nonneg x
  have hP : 0 ≤ (∑ i,x i)^2/(n:ℝ) := by positivity
  by_contra! h
  have hz : dotProduct x (wLap G w *ᵥ x)=0 := by linarith
  obtain ⟨c,rfl⟩ := positive_kernel hn G hG w hw x hz
  have hc : c ≠ 0 := by intro hc; apply hx; ext i; exact hc
  have hh : 0 < ((n:ℝ)*c)^2/n := by positivity
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  linarith

private lemma projection_spectral {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hB : (wLap G w+constProj n).PosDef) :
    let hL := lap_hermitian G w
    Unitary.conjStarAlgAut ℝ _ (star hL.eigenvectorUnitary) (constProj n) =
      diagonal (fun i => if hL.eigenvalues i=0 then 1 else 0) := by
  dsimp only
  let hL := lap_hermitian G w
  let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) (star hL.eigenvectorUnitary)
  have hfL : f (wLap G w)=diagonal hL.eigenvalues := by
    simpa [f] using hL.conjStarAlgAut_star_eigenvectorUnitary
  have hDN := congrArg f (green_properties hn G w hB).2.1
  have hDQ := congrArg f (lap_proj G w)
  simp only [map_mul,map_sub,map_one,hfL] at hDN
  simp only [map_mul,map_zero,hfL] at hDQ
  change f (constProj n)=_
  ext i j
  by_cases hi : hL.eigenvalues i=0
  · have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hDN
    simp only [Matrix.diagonal_mul,hi,zero_mul,Matrix.sub_apply] at h
    simp only [Matrix.diagonal_apply,hi,ite_true,Matrix.one_apply] at ⊢ h
    linarith
  · have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hDQ
    simp only [Matrix.diagonal_mul,Matrix.zero_apply] at h
    have hz := (mul_eq_zero.mp h).resolve_left hi
    simp [Matrix.diagonal_apply,hi,hz]

private lemma zero_count {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hB : (wLap G w+constProj n).PosDef) :
    (univ.filter fun i => (lap_hermitian G w).eigenvalues i=0).card=1 := by
  let hL := lap_hermitian G w
  let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) (star hL.eigenvectorUnitary)
  have htr : (f (constProj n)).trace=(constProj n).trace := trace_map f _
  rw [projection_spectral hn G w hB] at htr
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  simp only [Matrix.trace_diagonal,Matrix.trace,Matrix.diag_apply,constProj,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_inv_cancel₀ hn0] at htr
  simp only [Matrix.diagonal_apply_eq,Finset.sum_boole] at htr
  exact_mod_cast htr

private lemma spectral_center {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hB : (wLap G w+constProj n).PosDef) (t : ℝ)
    (ht : ∀ i, (lap_hermitian G w).eigenvalues i ≠ 0 →
      t ≤ (lap_hermitian G w).eigenvalues i) :
    (wLap G w-t • (1-constProj n)).PosSemidef := by
  let hL := lap_hermitian G w
  let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) (star hL.eigenvectorUnitary)
  have hfL : f (wLap G w)=diagonal hL.eigenvalues := by
    simpa [f] using hL.conjStarAlgAut_star_eigenvectorUnitary
  have hM : f (wLap G w-t • (1-constProj n))=
      diagonal (fun i => hL.eigenvalues i-t*(1-if hL.eigenvalues i=0 then 1 else 0)) := by
    rw [map_sub,map_smul,map_sub,map_one,hfL,projection_spectral hn G w hB]
    ext i j
    by_cases hij : i=j
    · subst j; simp
    · simp [Matrix.diagonal_apply,Matrix.one_apply,hij]
  have hpos : (f (wLap G w-t • (1-constProj n))).PosSemidef := by
    rw [hM,Matrix.posSemidef_diagonal_iff]
    intro i
    by_cases hi : hL.eigenvalues i=0
    · simp [hi]
    · simpa only [hi,ite_false,sub_zero,mul_one] using sub_nonneg.mpr (ht i hi)
  simpa only [f,Unitary.conjStarAlgAut_apply,
    Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff] using hpos

private lemma psd_rayleigh {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (t : ℝ)
    (hP : (wLap G w-t • (1-constProj n)).PosSemidef)
    (x : Fin n → ℝ) (hx : ∑ i,x i=0) :
    t * dotProduct x x ≤ dotProduct x (wLap G w *ᵥ x) := by
  have hp : constProj n *ᵥ x=0 := by ext i; simp [proj_mul,hx]
  have h := hP.dotProduct_mulVec_nonneg x
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,hp,
    sub_zero,dotProduct_sub,dotProduct_smul,smul_eq_mul] at h
  linarith

private lemma lambda_spectral {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hL : (wLap G w).PosSemidef) (hB : (wLap G w+constProj n).PosDef) :
    0 < lambda2 G w ∧
    (wLap G w-lambda2 G w • (1-constProj n)).PosSemidef ∧
    ∀ i, (lap_hermitian G w).eigenvalues i ≠ 0 →
      lambda2 G w ≤ (lap_hermitian G w).eigenvalues i := by
  let hM := lap_hermitian G w
  let e := hM.eigenvalues
  let J := univ.filter fun i => e i ≠ 0
  have hcard : J.card=n-1 := by
    have hc := Finset.card_filter_add_card_filter_not (s := univ) (fun i => e i=0)
    rw [zero_count (by omega) G w hB] at hc
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    dsimp [J]
    omega
  have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i,hi,hmin⟩ := J.exists_min_image e hJ
  have hi0 : e i ≠ 0 := (mem_filter.mp hi).2
  have hepos : 0 < e i := lt_of_le_of_ne (hL.eigenvalues_nonneg i) (Ne.symm hi0)
  have hmin' : ∀ j,e j ≠ 0 → e i ≤ e j := fun j hj => hmin j (mem_filter.mpr ⟨mem_univ _,hj⟩)
  have hP := spectral_center (by omega) G w hB (e i) hmin'
  let v : Fin n → ℝ := ⇑(hM.eigenvectorBasis i)
  have hv : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 (hM.eigenvectorBasis.orthonormal.ne_zero i)
  have heigen : wLap G w *ᵥ v=e i • v := hM.mulVec_eigenvectorBasis i
  have hsum : ∑ j,v j=0 := by
    have hs := lap_sum G w v
    rw [heigen] at hs
    simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum] at hs
    exact (mul_eq_zero.mp hs).resolve_left hi0
  have hval : lambda2 G w=e i := lambda2_eq_of_rayleigh G w _
    (fun x hx => psd_rayleigh G w (e i) hP x hx) v hv hsum heigen
  rw [hval]
  exact ⟨hepos,hP,hmin'⟩

private lemma normalized_shift {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hL : (wLap G w).PosSemidef) (ht : lambda2 G w=1) :
    (wLap G w+constProj n).PosDef := by
  have hP := centered_psd hn G w (fun x hx => by
    simpa [ht] using rayleigh_lower G w hL x hx)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos ((lap_hermitian G w).add (proj_hermitian n))
  intro x hx
  have h := hP.dotProduct_mulVec_nonneg x
  have hxx : 0 < dotProduct x x := by
    simpa only [star_trivial] using (dotProduct_star_self_pos_iff.mpr hx)
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub] at h
  simp only [star_trivial,Matrix.add_mulVec,dotProduct_add]
  linarith


/-- The graph on the same vertices retaining exactly positive original conductances. -/
def support {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ) :
    SimpleGraph (Fin n) where
  Adj i j := G.Adj i j ∧ 0 < w s(i,j)
  symm := ⟨by intro i j h; exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro i h; exact G.irrefl h.1⟩

private lemma connected_of_shift {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hw : ∀ i j, G.Adj i j → 0 ≤ w s(i,j))
    (hB : (wLap G w+constProj n).PosDef) : (support G w).Connected := by
  classical
  rw [SimpleGraph.connected_iff]
  refine ⟨?_,⟨⟨0,hn⟩⟩⟩
  intro p q
  by_contra hq
  let x : Fin n → ℝ := fun i => if (support G w).Reachable p i then 1 else 0
  have hxp : x p=1 := by simp [x]
  have hxq : x q=0 := by simp [x,hq]
  have hLx : wLap G w *ᵥ x=0 := by
    ext i
    rw [lap_mul]
    apply Finset.sum_eq_zero
    intro j hj
    have hij := (mem_filter.mp hj).2
    by_cases hwpos : 0 < w s(i,j)
    · have hadj : (support G w).Adj i j := ⟨hij,hwpos⟩
      have hiff : (support G w).Reachable p i ↔ (support G w).Reachable p j :=
        ⟨fun h => h.trans hadj.reachable,fun h => h.trans hadj.symm.reachable⟩
      simp only [x,hiff,sub_self,mul_zero]
    · have hz : w s(i,j)=0 := le_antisymm (le_of_not_gt hwpos) (hw i j hij)
      rw [hz,zero_mul]
  have he := congrArg (fun z => green G w *ᵥ z) hLx
  rw [Matrix.mulVec_mulVec,(green_properties hn G w hB).2.2.1,
    Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.mulVec_zero] at he
  have hc := sub_eq_zero.mp he
  have hp := congrFun hc p
  have hq' := congrFun hc q
  rw [hxp,proj_mul] at hp
  rw [hxq,proj_mul] at hq'
  linarith

private lemma independent_pair {n m : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) (f : Fin m → Fin n)
    (hf : Function.Injective f) (hI : ∀ i j, ¬ G.Adj (f i) (f j))
    (t : ℝ) (hP : (wLap G w-t • (1-constProj n)).PosSemidef)
    {i j : Fin m} (hij : i ≠ j) : 2*t ≤ wLap G w (f i) (f i)+wLap G w (f j) (f j) := by
  have hne : f i ≠ f j := hf.ne hij
  have hN : dotProduct (delta (f i) (f j)) (delta (f i) (f j))=2 := by
    rw [delta_dot]
    norm_num [delta,hne,Ne.symm hne]
  have hE : dotProduct (delta (f i) (f j)) (wLap G w *ᵥ delta (f i) (f j)) =
      wLap G w (f i) (f i)+wLap G w (f j) (f j) := by
    rw [delta_dot]
    simp only [delta,Matrix.mulVec_sub,Matrix.mulVec_single_one,Matrix.col_apply,Pi.sub_apply]
    have h01 : wLap G w (f i) (f j)=0 := by simp [wLap,hne,hI]
    have h10 : wLap G w (f j) (f i)=0 := by simp [wLap,Ne.symm hne,hI]
    rw [h01,h10]
    ring
  have h := psd_rayleigh G w t hP (delta (f i) (f j)) (delta_sum _ _)
  rw [hN,hE] at h
  linarith

private lemma independent_trace {n m : ℕ} (hm : 2 ≤ m) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) (f : Fin m → Fin n)
    (hf : Function.Injective f) (hI : ∀ i j, ¬ G.Adj (f i) (f j))
    (t : ℝ) (hP : (wLap G w-t • (1-constProj n)).PosSemidef) :
    m*t ≤ ∑ i,wLap G w (f i) (f i) := by
  have hgap : 0 ≤ ∑ i,∑ j,if i=j then 0 else
      wLap G w (f i) (f i)+wLap G w (f j) (f j)-2*t := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    split_ifs with hij
    · rfl
    · linarith [independent_pair G w f hf hI t hP hij]
  rw [pair_gap_sum] at hgap
  have hm1 : (1:ℝ)<m := by exact_mod_cast (show 1<m by omega)
  nlinarith

private lemma independent_annihilation {n m : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ) (f : Fin m → Fin n)
    (hf : Function.Injective f) (hI : ∀ i j, ¬ G.Adj (f i) (f j))
    (t : ℝ) (hP : (wLap G w-t • (1-constProj n)).PosSemidef)
    (htr : (∑ i,wLap G w (f i) (f i))=m*t) (i j : Fin m) :
    (wLap G w-t • (1-constProj n)) *ᵥ delta (f i) (f j)=0 := by
  by_cases hij : i=j
  · subst j; simp [delta]
  let d := fun i => wLap G w (f i) (f i)
  have hnon (i j : Fin m) : 0 ≤ if i=j then 0 else d i+d j-2*t := by
    split_ifs with hij
    · rfl
    · exact sub_nonneg.mpr (independent_pair G w f hf hI t hP hij)
  have hsum : (∑ i,∑ j,if i=j then 0 else d i+d j-2*t)=0 := by
    rw [pair_gap_sum]
    change 2*(m-1:ℝ)*((∑ i,wLap G w (f i) (f i))-m*t)=0
    rw [htr,sub_self,mul_zero]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
    Finset.sum_nonneg fun l _ => hnon k l)).mp hsum i (mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnon i k)).mp hi j (mem_univ j)
  simp only [if_neg hij] at hj
  have hne : f i ≠ f j := hf.ne hij
  apply hP.dotProduct_mulVec_zero_iff.mp
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,
    Matrix.sub_mulVec,Matrix.one_mulVec,proj_delta,sub_zero,dotProduct_sub,dotProduct_smul,
    smul_eq_mul]
  rw [delta_dot,delta_dot]
  simp only [delta,Matrix.mulVec_sub,Matrix.mulVec_single_one,Matrix.col_apply,Pi.sub_apply]
  have h01 : wLap G w (f i) (f j)=0 := by simp [wLap,hne,hI]
  have h10 : wLap G w (f j) (f i)=0 := by simp [wLap,Ne.symm hne,hI]
  simp [Pi.single_apply,hne,Ne.symm hne,h01,h10,d] at ⊢ hj
  linarith

/-- The original labelled parts of sizes a, b and c, with counting measure. -/
def part (a b c : ℕ) (i : Fin (a+b+c)) : ℕ :=
  if i.val<a then 0 else if i.val<a+b then 1 else 2

def K3 (a b c : ℕ) : SimpleGraph (Fin (a+b+c)) where
  Adj i j := part a b c i ≠ part a b c j
  symm := ⟨by intro i j h; exact h.symm⟩
  loopless := ⟨by intro i; exact not_not_intro rfl⟩

instance K3_dec (a b c : ℕ) : DecidableRel (K3 a b c).Adj := by
  unfold K3; infer_instance

private def va (a b c : ℕ) (i : Fin a) : Fin (a+b+c) := (i.castAdd b).castAdd c
private def vb (a b c : ℕ) (i : Fin b) : Fin (a+b+c) := (i.natAdd a).castAdd c
private def vc (a b c : ℕ) (i : Fin c) : Fin (a+b+c) := i.natAdd (a+b)

private lemma sum_parts {a b c : ℕ} (f : Fin (a+b+c) → ℝ) :
    (∑ i,f i)=(∑ i,f (va a b c i))+(∑ i,f (vb a b c i))+(∑ i,f (vc a b c i)) := by
  rw [Fin.sum_univ_add,Fin.sum_univ_add]
  rfl

private lemma part_va {a b c : ℕ} (i : Fin a) : part a b c (va a b c i)=0 := by
  simp [part,va,i.isLt]
private lemma part_vb {a b c : ℕ} (i : Fin b) : part a b c (vb a b c i)=1 := by
  have hi := i.isLt
  change (if a+i.val<a then 0 else if a+i.val<a+b then 1 else 2)=1
  split_ifs <;> omega
private lemma part_vc {a b c : ℕ} (i : Fin c) : part a b c (vc a b c i)=2 := by
  change (if a+b+i.val<a then 0 else if a+b+i.val<a+b then 1 else 2)=2
  split_ifs <;> omega

private lemma trace_bound {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (w : Sym2 (Fin (a+b+c)) → ℝ) (t : ℝ)
    (hP : (wLap (K3 a b c) w-t • (1-constProj (a+b+c))).PosSemidef) :
    (a+b+c:ℕ)*t ≤ (wLap (K3 a b c) w).trace := by
  have hA := independent_trace ha (K3 a b c) w (va a b c)
    (by intro i j h; exact Fin.ext (by simpa [va,Fin.ext_iff] using h))
    (by intro i j; simp [K3,part_va]) t hP
  have hB := independent_trace hb (K3 a b c) w (vb a b c)
    (by intro i j h; exact Fin.ext (by simpa [vb,Fin.ext_iff] using h))
    (by intro i j; simp [K3,part_vb]) t hP
  have hC := independent_trace hc (K3 a b c) w (vc a b c)
    (by intro i j h; exact Fin.ext (by simpa [vc,Fin.ext_iff] using h))
    (by intro i j; simp [K3,part_vc]) t hP
  change (a+b+c:ℕ)*t ≤ ∑ i,wLap (K3 a b c) w i i
  rw [sum_parts]
  push_cast
  linarith


private lemma K3_connected {a b c : ℕ} (ha : 0<a) (hc : 0<c) :
    (K3 a b c).Connected := by
  let u := va a b c ⟨0,ha⟩
  let z := vc a b c ⟨0,hc⟩
  have hreach (i : Fin (a+b+c)) : (K3 a b c).Reachable i u := by
    by_cases hi : part a b c i=0
    · have hiz : (K3 a b c).Adj i z := by simp [K3,z,hi,part_vc]
      have hzu : (K3 a b c).Adj z u := by simp [K3,z,u,part_vc,part_va]
      exact hiz.reachable.trans hzu.reachable
    · have hiu : (K3 a b c).Adj i u := by simpa [K3,u,part_va] using hi
      exact hiu.reachable
  rw [SimpleGraph.connected_iff]
  exact ⟨fun i j => (hreach i).trans (hreach j).symm,⟨u⟩⟩

private lemma reciprocal_ceiling {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (t : ℝ) (ht : 0<t) (hr : ∀ i,t ≤ r i)
    (htrace : ((Fintype.card ι:ℝ)+1)*t ≤ ∑ i,r i) :
    t*(∑ i,(r i)⁻¹) ≤ (Fintype.card ι:ℝ)-1/2 ∧
    (t*(∑ i,(r i)⁻¹)=(Fintype.card ι:ℝ)-1/2 →
      (∑ i,r i)=((Fintype.card ι:ℝ)+1)*t ∧
      ∃ j,r j=2*t ∧ ∀ i,i ≠ j → r i=t) := by
  classical
  let q := fun i => r i/t-1
  let Q := ∑ i,q i
  have hrpos (i : ι) : 0<r i := lt_of_lt_of_le ht (hr i)
  have hq (i : ι) : 0 ≤ q i := by
    dsimp [q]
    rw [sub_nonneg,le_div_iff₀ ht]
    simpa using hr i
  have hQeq : Q=(∑ i,r i)/t-(Fintype.card ι:ℝ) := by
    simp [Q,q,Finset.sum_sub_distrib,← Finset.sum_div]
  have hQ : 1 ≤ Q := by
    have hh : (Fintype.card ι:ℝ)+1 ≤ (∑ i,r i)/t :=
      (le_div_iff₀ ht).mpr htrace
    linarith
  have hQp : 0<1+Q := by linarith
  have hqi (i : ι) : q i ≤ Q :=
    Finset.single_le_sum (fun j _ => hq j) (mem_univ i)
  have hterm (i : ι) : q i/(1+Q) ≤ q i/(1+q i) :=
    div_le_div_of_nonneg_left (hq i) (by linarith [hq i]) (by linarith [hqi i])
  have hsum : Q/(1+Q) ≤ ∑ i,q i/(1+q i) := by
    rw [show Q/(1+Q)=∑ i,q i/(1+Q) from Finset.sum_div _ _ _]
    exact Finset.sum_le_sum fun i _ => hterm i
  have hhalf : (1:ℝ)/2 ≤ Q/(1+Q) := by
    rw [div_le_div_iff₀ (by norm_num) hQp]
    linarith
  have hid (i : ι) : t*(r i)⁻¹=1-q i/(1+q i) := by
    dsimp [q]
    field_simp [ht.ne',(hrpos i).ne']
    <;> ring
  have htot : t*(∑ i,(r i)⁻¹)=(Fintype.card ι:ℝ)-∑ i,q i/(1+q i) := by
    rw [Finset.mul_sum]
    simp_rw [hid]
    simp [Finset.sum_sub_distrib]
  refine ⟨by linarith,?_⟩
  intro heq
  have hfrac : (∑ i,q i/(1+q i))=(1:ℝ)/2 := by linarith
  have hQu : Q/(1+Q) ≤ (1:ℝ)/2 := by linarith
  rw [div_le_div_iff₀ hQp (by norm_num)] at hQu
  have hQone : Q=1 := by linarith
  have htr : (∑ i,r i)=((Fintype.card ι:ℝ)+1)*t := by
    rw [hQeq] at hQone
    apply (div_eq_iff ht.ne').mp
    linarith
  refine ⟨htr,?_⟩
  have hd (i : ι) : 0 ≤ q i/(1+q i)-q i/2 := by
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_left (hq i) (by linarith [hq i])
      (by linarith [hqi i])
  have hzero : (∑ i,(q i/(1+q i)-q i/2))=0 := by
    rw [Finset.sum_sub_distrib,hfrac,← Finset.sum_div]
    change 1/2-Q/2=0
    rw [hQone]
    norm_num
  have hcases (i : ι) : q i=0 ∨ q i=1 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hd j)).mp hzero i (mem_univ i)
    have hp : 1+q i ≠ 0 := by linarith [hq i]
    have he : q i*(1-q i)=0 := by
      have heq := sub_eq_zero.mp hi
      field_simp [hp] at heq
      nlinarith
    rcases mul_eq_zero.mp he with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  obtain ⟨j,hj⟩ : ∃ j,q j ≠ 0 := by
    by_contra! h
    have hz : Q=0 := by simp [Q,h]
    linarith
  have hjq : q j=1 := (hcases j).resolve_left hj
  have hother (i : ι) (hij : i ≠ j) : q i=0 := by
    have hz : (∑ i ∈ univ.erase j,q i)=0 := by
      have hh := Finset.sum_erase_add univ q (mem_univ j)
      change (∑ i ∈ univ.erase j,q i)+q j=Q at hh
      rw [hjq,hQone] at hh
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hq k)).mp hz i
      (Finset.mem_erase.mpr ⟨hij,mem_univ i⟩)
  refine ⟨j,?_,?_⟩
  · dsimp [q] at hjq
    exact (div_eq_iff ht.ne').mp (by linarith)
  · intro i hij
    have hh := hother i hij
    dsimp [q] at hh
    have he : r i/t=1 := by linarith
    simpa using (div_eq_iff ht.ne').mp he

private lemma product_ceiling {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (w : Sym2 (Fin (a+b+c)) → ℝ) (hL : (wLap (K3 a b c) w).PosSemidef)
    (hB : (wLap (K3 a b c) w+constProj (a+b+c)).PosDef) :
    lambda2 (K3 a b c) w*totalRes (K3 a b c) w ≤
      (a+b+c:ℕ)*((a+b+c:ℕ)-(3:ℝ)/2) ∧
    (lambda2 (K3 a b c) w*totalRes (K3 a b c) w =
      (a+b+c:ℕ)*((a+b+c:ℕ)-(3:ℝ)/2) →
      (wLap (K3 a b c) w).trace=(a+b+c:ℕ)*lambda2 (K3 a b c) w ∧
      ∃ j,(lap_hermitian (K3 a b c) w).eigenvalues j=2*lambda2 (K3 a b c) w ∧
        ∀ i,i ≠ j → (lap_hermitian (K3 a b c) w).eigenvalues i=0 ∨
          (lap_hermitian (K3 a b c) w).eigenvalues i=lambda2 (K3 a b c) w) := by
  classical
  let n := a+b+c
  let e := (lap_hermitian (K3 a b c) w).eigenvalues
  let J := {i : Fin n // e i ≠ 0}
  let t := lambda2 (K3 a b c) w
  have hs := lambda_spectral (by omega) (K3 a b c) w hL hB
  have hcard : Fintype.card J=n-1 := by
    rw [Fintype.card_subtype]
    have hz := zero_count (by omega) (K3 a b c) w hB
    have hh := Finset.card_filter_add_card_filter_not (s := univ) (fun i => e i=0)
    rw [hz] at hh
    simp only [Finset.card_univ,Fintype.card_fin] at hh
    dsimp [n] at ⊢ hh
    omega
  have hsum : (∑ i : J,e i)=(wLap (K3 a b c) w).trace := by
    rw [(lap_hermitian (K3 a b c) w).trace_eq_sum_eigenvalues]
    change (∑ i : J,e i)=∑ i,e i
    rw [← Finset.sum_subtype (univ.filter fun i => e i ≠ 0) (by simp) e]
    exact Finset.sum_filter_ne_zero univ
  have hinv : (∑ i : J,(e i)⁻¹)=∑ i,(e i)⁻¹ := by
    rw [← Finset.sum_subtype (univ.filter fun i => e i ≠ 0) (by simp) (fun i => (e i)⁻¹)]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases he : e i=0 <;> simp [he]
  have hn1 : 1 ≤ n := by dsimp [n]; omega
  have hcast : (Fintype.card J:ℝ)=(n:ℝ)-1 := by
    rw [hcard,Nat.cast_sub hn1,Nat.cast_one]
  have htrace : ((Fintype.card J:ℝ)+1)*t ≤ ∑ i : J,e i := by
    rw [hcast,sub_add_cancel,hsum]
    exact trace_bound ha hb hc w t hs.2.1
  have hrec := reciprocal_ceiling (fun i : J => e i) t hs.1
    (fun i => hs.2.2 i i.2) htrace
  have hR : totalRes (K3 a b c) w=(n:ℝ)*∑ i : J,(e i)⁻¹ := by
    rw [resistance_spectral (by omega) (K3 a b c) w hL hB,hinv]
  have hnpos : (0:ℝ)<n := by dsimp [n]; positivity
  rw [hcast] at hrec
  constructor
  · rw [hR]
    nlinarith [mul_le_mul_of_nonneg_left hrec.1 hnpos.le]
  · intro heq
    have he : t*(∑ i : J,(e i)⁻¹)=(n:ℝ)-1-1/2 := by
      rw [hR] at heq
      change t*((n:ℝ)*∑ i : J,(e i)⁻¹)=(n:ℝ)*((n:ℝ)-3/2) at heq
      nlinarith
    obtain ⟨htr,j,hj,hother⟩ := hrec.2 he
    refine ⟨?_,j.val,hj,?_⟩
    · rw [hsum] at htr
      simpa only [sub_add_cancel] using htr
    · intro i hij
      by_cases hi : e i=0
      · exact Or.inl hi
      · exact Or.inr (hother ⟨i,hi⟩ (by intro h; exact hij (congrArg Subtype.val h)))

end D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceTripartiteOptimizer
