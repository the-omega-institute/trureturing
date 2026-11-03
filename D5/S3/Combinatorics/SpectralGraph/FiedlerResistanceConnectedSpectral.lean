/- GID: D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FiedlerResistanceConnectedSpectral
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Connected weighted Laplacians, mean-zero Rayleigh minima and harmonic resistance. -/
import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer

/-! Weighted Laplacians on the original labelled vertices. -/
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceConnectedSpectral
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

lemma lap_psd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
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

lemma resistance_spectral {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
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

lemma positive_shift {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
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

lemma zero_count {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
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

lemma psd_rayleigh {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (t : ℝ)
    (hP : (wLap G w-t • (1-constProj n)).PosSemidef)
    (x : Fin n → ℝ) (hx : ∑ i,x i=0) :
    t * dotProduct x x ≤ dotProduct x (wLap G w *ᵥ x) := by
  have hp : constProj n *ᵥ x=0 := by ext i; simp [proj_mul,hx]
  have h := hP.dotProduct_mulVec_nonneg x
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,hp,
    sub_zero,dotProduct_sub,dotProduct_smul,smul_eq_mul] at h
  linarith

lemma lambda_spectral {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
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

lemma normalized_shift {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
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

lemma connected_of_shift {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
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


private lemma unit_outer_rank {n : ℕ} (v : Fin n → ℝ) (hv : dotProduct v v=1) :
    (Matrix.vecMulVec v v).rank=1 := by
  have hle := Matrix.rank_vecMulVec_le v v
  by_contra hne
  have hz : (Matrix.vecMulVec v v).rank=0 := by omega
  rw [Matrix.rank_eq_finrank_span_cols] at hz
  have hspan : Submodule.span ℝ (Set.range (Matrix.vecMulVec v v).col)=⊥ :=
    Submodule.finrank_eq_zero.mp hz
  have hcol (j : Fin n) : (Matrix.vecMulVec v v).col j=0 := by
    have hm := Submodule.subset_span (R := ℝ) (show (Matrix.vecMulVec v v).col j ∈
      Set.range (Matrix.vecMulVec v v).col from ⟨j,rfl⟩)
    rw [hspan] at hm
    exact hm
  have hM : Matrix.vecMulVec v v=0 := by
    ext i j
    exact congrFun (hcol j) i
  have hh := congrArg Matrix.trace hM
  rw [Matrix.trace_vecMulVec,hv,Matrix.trace_zero] at hh
  norm_num at hh

lemma rankone_of_spectrum {n : ℕ} (hn : 0<n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (w : Sym2 (Fin n) → ℝ)
    (hB : (wLap G w+constProj n).PosDef) (t : ℝ) (ht : 0<t) (j : Fin n)
    (hj : (lap_hermitian G w).eigenvalues j=2*t)
    (he : ∀ i,i ≠ j → (lap_hermitian G w).eigenvalues i=0 ∨
      (lap_hermitian G w).eigenvalues i=t) :
    ∃ v : Fin n → ℝ, (∑ i,v i)=0 ∧ dotProduct v v=1 ∧
      wLap G w-t • (1-constProj n)=t • Matrix.vecMulVec v v ∧
      (wLap G w-t • (1-constProj n)).rank=1 := by
  classical
  let hM := lap_hermitian G w
  let v : Fin n → ℝ := ⇑(hM.eigenvectorBasis j)
  let U : Matrix (Fin n) (Fin n) ℝ := hM.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) (star hM.eigenvectorUnitary)
  have hUU : U*star U=1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hnorm : dotProduct v v=1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j j)
      (Unitary.coe_star_mul_self hM.eigenvectorUnitary)
    simpa only [Matrix.mul_apply,Matrix.star_apply,star_trivial,
      Matrix.one_apply_eq,Matrix.IsHermitian.eigenvectorUnitary_apply,v,dotProduct] using h
  have hsum : (∑ i,v i)=0 := by
    have h := lap_sum G w v
    rw [show wLap G w *ᵥ v=(2*t) • v from by simpa only [v,hj] using hM.mulVec_eigenvectorBasis j] at h
    simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum] at h
    exact (mul_eq_zero.mp h).resolve_left (by positivity)
  let Q := wLap G w-t • (1-constProj n)
  have hfL : f (wLap G w)=diagonal hM.eigenvalues := by
    simpa [f] using hM.conjStarAlgAut_star_eigenvectorUnitary
  have hQ : f Q=diagonal (fun i => if i=j then t else 0) := by
    dsimp only [Q]
    rw [map_sub,map_smul,map_sub,map_one,hfL,projection_spectral hn G w hB]
    ext i k
    by_cases hik : i=k
    · subst k
      by_cases hij : i=j
      · subst i; simp [hj,ne_of_gt ht]; ring
      · rcases he i hij with hi | hi <;> simp [hi,hij,ne_of_gt ht]
    · simp [Matrix.diagonal_apply,Matrix.one_apply,hik]
  have hQ' : star U*Q*U=diagonal (fun i => if i=j then t else 0) := by
    simpa only [f,Unitary.conjStarAlgAut_star_apply] using hQ
  have hfactor : Q=U*diagonal (fun i => if i=j then t else 0)*star U := by
    calc
      Q=(U*star U)*Q*(U*star U) := by rw [hUU]; simp
      _=U*(star U*Q*U)*star U := by noncomm_ring
      _=_ := by rw [hQ']
  have hfinal : Q=t • Matrix.vecMulVec v v := by
    rw [hfactor]
    ext i k
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_diagonal]
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply,Matrix.star_apply,star_trivial]
    rw [Finset.sum_eq_single j]
    · simp [U,v,Matrix.IsHermitian.eigenvectorUnitary_apply] <;> ring
    · intro b hb hbj; simp [hbj]
    · simp
  refine ⟨v,hsum,hnorm,hfinal,?_⟩
  change Q.rank=1
  rw [hfinal,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero ht.ne')]
  exact unit_outer_rank v hnorm

end D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceConnectedSpectral
