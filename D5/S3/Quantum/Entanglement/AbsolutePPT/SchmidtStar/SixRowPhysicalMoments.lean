/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowPhysicalMoments
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Actual rank-six boundary moments, excluding the separate same-vector coupling. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Physical
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.UniformSchmidtHeadCap

/-! The literal APPT diagonal supplies the boundary moments. The head and tail
charges at a common vector are supplied separately by SixRowCoupling.
-/
set_option autoImplicit false
open Matrix Finset
open scoped ComplexOrder BigOperators
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowPhysicalMoments
open UniformSchmidtIncidence UniformSchmidtSpectrum UniformSchmidtBell
open UniformSchmidtDefectMoment UniformSchmidtVarianceConsumer
open QutritPerturbationAttainment
noncomputable section

private theorem six_top_card : a 6 = 15 := by
  have hc := edge_card_real 6
  norm_num at hc
  exact_mod_cast hc

private theorem six_bottom_card : b 6 = 21 := by
  have hc := bottom_card_real 6
  norm_num at hc
  exact_mod_cast hc

/-- Exact raw boundary data; all indices are zero-based. -/
def u {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : ℝ := l ⟨N-21, by omega⟩
def v {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : ℝ := l ⟨14, by omega⟩-u hN l
def heads {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : Fin 15 → ℝ :=
  fun i => l ⟨i.val, by omega⟩-l ⟨14, by omega⟩
def tails {N : ℕ} (hN : 36 ≤ N) (l : Fin N → ℝ) : Fin 21 → ℝ :=
  fun i => u hN l-l ⟨N-21+i.val, by omega⟩

def cap (r : ℝ) : ℝ := (4-8*r-5*r^2)/(2-3*r)

/-- The supplied constraints, with the actual finite lists retained. -/
structure Constraints (r : ℝ) (h : Fin 15 → ℝ) (d : Fin 21 → ℝ) : Prop where
  r_nonneg : 0 ≤ r
  r_le : r ≤ 2/5
  h_nonneg : ∀ i, 0 ≤ h i
  d_nonneg : ∀ i, 0 ≤ d i
  d_le_one : ∀ i, d i ≤ 1
  d_monotone : Monotone d
  h_zero : h 14 = 0
  d_zero : d 0 = 0
  H_nonneg : 0 ≤ ∑ i, h i
  D_nonneg : 0 ≤ ∑ i, d i
  a_nonneg : 0 ≤ ∑ i, (h i)^2
  q_nonneg : 0 ≤ ∑ i, (d i)^2
  mass : 0 ≤ 6-15*r-(∑ i, h i)-(∑ i, d i)
  q_box : (∑ i, (d i)^2) ≤ ∑ i, d i
  q_mass : (∑ i, (d i)^2) ≤ (∑ i, d i)^2
  head_cauchy : (∑ i, h i)^2 ≤ 14*(∑ i, (h i)^2)
  tail_cauchy : (∑ i, d i)^2 ≤ 20*(∑ i, (d i)^2)
  head_sq : (∑ i, (h i)^2) ≤ (∑ i, h i)^2
  head_point_cap : ∀ i, h i ≤ cap r
  head_cap : (∑ i, (h i)^2) ≤ cap r*(∑ i, h i)
  head_box : (∑ i, (h i)^2) ≤ ((∑ i, h i)-cap r)^2+(cap r)^2
  tail_cap : (∑ i, (d i)^2) ≤ max 2 (2*(∑ i, d i)/3)
  variance : (5/7)*((∑ i, (h i)^2)-(∑ i, h i)^2/15)+
    ((∑ i, (d i)^2)-(∑ i, d i)^2/21) ≤
      4*(6-15*r-(∑ i, h i)-(∑ i, d i))-
        (6-15*r-(∑ i, h i)-(∑ i, d i))^2/3

/-- This transports EVERY independently labelled actual pool, not a PSD assumption. -/
private theorem literal_pool_psd (n : ℕ) (hn : 6 ≤ n)
    (e : (Fin 6 × Fin n) ≃ Fin (6*n)) (l : Fin (6*n) → ℝ)
    (happt : APPT (diagonal (fun z => (l (e z) : ℂ))))
    (π : Edge 6 ≃ Fin 15) (σ : BottomSlot 6 ≃ Fin 21) :
    let hN : 36 ≤ 6*n := by omega
    (K (fun E => u hN l+v hN l+heads hN l (π E))
      (fun B => u hN l-tails hN l (σ B))).PosSemidef := by
  dsimp only
  let hN : 36 ≤ 6*n := by omega
  let hp : a 6+b 6 ≤ 6*n :=
    (pool_card_sum 6).trans_le (Nat.mul_le_mul (by rfl) hn)
  let π' : Equiv.Perm (Fin (a 6)) :=
    (Fintype.equivFin (Edge 6)).symm.trans (π.trans (finCongr six_top_card).symm)
  let σ' : Equiv.Perm (Fin (b 6)) :=
    (Fintype.equivFin (BottomSlot 6)).symm.trans (σ.trans (finCongr six_bottom_card).symm)
  have hpsd := literal_assignment_psd (by rfl : 6 ≤ 6) hn e l happt π' σ'
  dsimp only at hpsd
  have ht (E : Edge 6) : u hN l+v hN l+heads hN l (π E) =
      l (assignedTopIndex hp π' E) := by
    have hi : assignedTopIndex hp π' E = ⟨(π E).val, by omega⟩ := by
      apply Fin.ext
      simp [assignedTopIndex, topIndex, π', Equiv.trans_apply]
    rw [hi]
    dsimp [v, heads]
    ring
  have hb (B : BottomSlot 6) : u hN l-tails hN l (σ B) =
      l (assignedBottomIndex hp σ' B) := by
    have hi : assignedBottomIndex hp σ' B = ⟨6*n-21+(σ B).val, by omega⟩ := by
      apply Fin.ext
      simp [assignedBottomIndex, bottomIndex, σ', Equiv.trans_apply]
      change 6*n - b 6 = 6*n - 21
      rw [six_bottom_card]
    rw [hi]
    dsimp [tails]
    ring
  have hid : K (fun E => u hN l+v hN l+heads hN l (π E))
      (fun B => u hN l-tails hN l (σ B)) = assignedK hp l π' σ' := by
    unfold assignedK
    congr 1 <;> funext z
    · exact ht z
    · exact hb z
  rwa [hid]

/-- Singular-safe PSD Cauchy; the mature bilinear-form proof with Fin 6. -/
private theorem psd_entry_square (M : Matrix (Fin 6) (Fin 6) ℝ)
    (hM : M.PosSemidef) (i j : Fin 6) : (M i j)^2 ≤ M i i*M j j := by
  let B : LinearMap.BilinForm ℝ (Fin 6 → ℝ) := Matrix.toLinearMap₂' ℝ M
  have hp : ∀ x, 0 ≤ B x x := by
    intro x
    simpa [B, Matrix.toLinearMap₂'_apply'] using hM.dotProduct_mulVec_nonneg x
  have hs : LinearMap.IsSymm B := by
    constructor
    intro x y
    simpa [B, Matrix.toLinearMap₂'_apply'] using
      hM.isHermitian.star_dotProduct_mulVec_comm x y
  have hcs := B.apply_sq_le_of_symm hp hs (Pi.single i 1) (Pi.single j 1)
  simpa [B, Matrix.toLinearMap₂'_apply', dotProduct, mulVec, Pi.single_apply] using hcs

/-- All 21 labels occur once: diagonals 0,1 get 20,19 and edge 01 gets 18. -/
private def tailPlacement : BottomSlot 6 → Fin 21
  | .inl i => ![20,19,0,1,2,3] i
  | .inr E =>
    if E.val.1 = 0 then ![0,18,4,5,6,7] E.val.2
    else if E.val.1 = 1 then ![0,0,8,9,10,11] E.val.2
    else if E.val.1 = 2 then ![0,0,0,12,13,14] E.val.2
    else if E.val.1 = 3 then ![0,0,0,0,15,16] E.val.2
    else 17

private def tailEquiv : BottomSlot 6 ≃ Fin 21 :=
  Equiv.ofBijective tailPlacement (by decide)

/-- The scalar factorization sums ALL 21 slots. It divides by no minor or entry. -/
private theorem tail_square_cap (z : Fin 21 → ℝ) (m : ℝ)
    (hm : 3 ≤ m) (h0 : ∀ i, 0 ≤ z i) (h1 : ∀ i, z i ≤ 1)
    (ho : Monotone z) (hsum : (∑ i, z i) ≤ m)
    (hp : (z 18)^2 ≤ 4*(1-z 20)*(1-z 19)) :
    (∑ i, (z i)^2) ≤ 2*m/3 := by
  let A := z 20
  let B := z 19
  let C := z 18
  have hA0 : 0 ≤ A := h0 20
  have hB0 : 0 ≤ B := h0 19
  have hC0 : 0 ≤ C := h0 18
  have hA1 : A ≤ 1 := h1 20
  have hB1 : B ≤ 1 := h1 19
  have hCA : C ≤ A := ho (by decide : (18 : Fin 21) ≤ 20)
  have hCB : C ≤ B := ho (by decide : (18 : Fin 21) ≤ 19)
  change C^2 ≤ 4*(1-A)*(1-B) at hp
  have hCS : C ≤ 2-A-B := by
    have hsq : C^2 ≤ (2-A-B)^2 := by nlinarith only [hp, sq_nonneg (A-B)]
    exact (sq_le_sq₀ hC0 (by linarith)).mp hsq
  have hCU : C ≤ 2/3 := by linarith
  have he := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ (2-A-B)-C by linarith)
    (show (2-A-B)-(2-2*C) ≤ 0 by linarith)
  have hAB : A^2+B^2-C*(A+B) ≤ 2-4*C+3*C^2/2 := by
    nlinarith only [hp, he]
  have hpoint (i : Fin 21) : (z i)^2 ≤ C*z i+
      (if i = 20 then A^2-C*A else 0)+(if i = 19 then B^2-C*B else 0) := by
    by_cases hi : i = 20
    · subst i
      simp only [if_pos rfl, if_neg (by decide : (20 : Fin 21) ≠ 19)]
      dsimp [A]
      nlinarith only []
    · by_cases hi' : i = 19
      · subst i
        simp only [if_neg (by decide : (19 : Fin 21) ≠ 20), if_pos rfl]
        dsimp [B]
        nlinarith only []
      · have hic : z i ≤ C := ho (by change i.val ≤ 18; omega)
        have hi0 := mul_nonneg (h0 i) (sub_nonneg.mpr hic)
        simp only [if_neg hi, if_neg hi']
        nlinarith only [hi0]
  have hsq := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 21))) => hpoint i)
  simp only [sum_add_distrib, ← mul_sum] at hsq
  simp only [sum_ite_eq', mem_univ, if_true] at hsq
  have hmass := mul_le_mul_of_nonneg_left hsum hC0
  have hfac := mul_nonneg (show 0 ≤ 2/3-C by linarith)
    (show 0 ≤ m-3+3*C/2 by linarith)
  nlinarith only [hsq, hmass, hAB, hfac]

/-- A true box-mass bound, including the intermediate strip c < H < 2c. -/
private theorem head_box (h : Fin 15 → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ c) :
    (∑ i, (h i)^2) ≤ ((∑ i, h i)-c)^2+c^2 := by
  classical
  let H := ∑ i, h i
  let A := ∑ i, (h i)^2
  have hbound (b : ℝ) (hb : ∀ i, h i ≤ b) : A ≤ b*H := by
    calc
      _ ≤ ∑ i, b*h i := sum_le_sum (fun i _ => by
        nlinarith only [mul_nonneg (h0 i) (sub_nonneg.mpr (hb i))])
      _ = _ := by rw [← mul_sum]
  change A ≤ (H-c)^2+c^2
  by_cases hbig : 2*c ≤ H
  · have hf := mul_nonneg (show 0 ≤ H-c by linarith) (sub_nonneg.mpr hbig)
    nlinarith only [hbound c h1, hf]
  · by_cases hsmall : ∀ i, h i ≤ H-c
    · have hf := mul_nonneg hc (show 0 ≤ 2*c-H by linarith)
      nlinarith only [hbound (H-c) hsmall, hf]
    · push_neg at hsmall
      obtain ⟨j, hj⟩ := hsmall
      have he := sum_sq_le_sq_sum_of_nonneg
        (s := (univ : Finset (Fin 15)).erase j) (f := h) (fun i _ => h0 i)
      have hs := add_sum_erase univ h (mem_univ j)
      have hq := add_sum_erase univ (fun i => (h i)^2) (mem_univ j)
      have hes : (∑ i ∈ univ.erase j, h i) = H-h j := by
        dsimp only [H]
        linarith only [hs]
      rw [hes] at he
      have hpair : A ≤ (h j)^2+(H-h j)^2 := by
        dsimp only [A]
        linarith only [hq, he]
      have hf := mul_nonneg (sub_nonneg.mpr (h1 j))
        (show 0 ≤ c+h j-H by linarith only [hj])
      nlinarith only [hpair, hf]

private theorem top_pool_sum {N : ℕ} (hN : 36 ≤ N)
    (hp : a 6+b 6 ≤ N) (l : Fin N → ℝ) (F : ℝ → ℝ) :
    (∑ k : Fin (a 6), F (l (topIndex hp k))) =
      ∑ i : Fin 15, F (u hN l+v hN l+heads hN l i) := by
  calc
    _ = ∑ k : Fin (a 6), F (u hN l+v hN l+heads hN l (finCongr six_top_card k)) := by
      apply sum_congr rfl
      intro k _
      congr 1
      dsimp [v, heads, topIndex]
      ring
    _ = _ := Equiv.sum_comp (finCongr six_top_card)
      (fun i : Fin 15 => F (u hN l+v hN l+heads hN l i))

private theorem bottom_pool_sum {N : ℕ} (hN : 36 ≤ N)
    (hp : a 6+b 6 ≤ N) (l : Fin N → ℝ) (F : ℝ → ℝ) :
    (∑ k : Fin (b 6), F (l (bottomIndex hp k))) =
      ∑ i : Fin 21, F (u hN l-tails hN l i) := by
  calc
    _ = ∑ k : Fin (b 6), F (u hN l-tails hN l (finCongr six_bottom_card k)) := by
      apply sum_congr rfl
      intro k _
      congr 1
      have hi : bottomIndex hp k =
          (⟨N-21+(finCongr six_bottom_card k).val, by omega⟩ : Fin N) := by
        apply Fin.ext
        change N-b 6+k.val = N-21+k.val
        exact congrArg (fun t : ℕ => N-t+k.val) six_bottom_card
      rw [hi]
      dsimp [tails]
      ring
    _ = _ := Equiv.sum_comp (finCongr six_bottom_card)
      (fun i : Fin 21 => F (u hN l-tails hN l i))

private theorem variance_expansion {k : ℕ} (hk : (k : ℝ) ≠ 0) (z : Fin k → ℝ) :
    variance z = (∑ i, (z i)^2)-(∑ i, z i)^2/(k : ℝ) := by
  unfold variance
  calc
    _ = ∑ i, ((z i)^2-2*((∑ j, z j)/(k : ℝ))*z i+((∑ j, z j)/(k : ℝ))^2) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (z i)^2)-2*((∑ j, z j)/(k : ℝ))*(∑ i, z i)+
        (k : ℝ)*((∑ j, z j)/(k : ℝ))^2 := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
        card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by field_simp [hk] <;> ring

/-- Actual normalized 15/21 moments. This supplies no same-vector coupling
and makes no assertion about the purity maximum or the threshold theorem. -/
theorem literal_moments (n : ℕ) (hn : 23 ≤ n)
    (e : (Fin 6 × Fin n) ≃ Fin (6*n)) (l : Fin (6*n) → ℝ)
    (hl : Antitone l) (h0 : ∀ i, 0 ≤ l i) (hmass : (∑ i, l i) = 1)
    (happt : APPT (diagonal (fun z => (l (e z) : ℂ)))) :
    let hN : 36 ≤ 6*n := by omega
    let U := u hN l
    let r := v hN l/U
    let h : Fin 15 → ℝ := fun i => heads hN l i/U
    let d : Fin 21 → ℝ := fun i => tails hN l i/U
    0 < U ∧ Constraints r h d := by
  classical
  dsimp only
  let hN : 36 ≤ 6*n := by omega
  let hp : a 6+b 6 ≤ 6*n :=
    (pool_card_sum 6).trans_le (Nat.mul_le_mul (by rfl) (by omega : 6 ≤ n))
  let U := u hN l
  let V := v hN l
  let eta := heads hN l
  let delta := tails hN l
  let L := l ⟨0, by omega⟩
  let HH := ∑ i, eta i
  let DD := ∑ i, delta i
  let AA := ∑ i, (eta i)^2
  let QQ := ∑ i, (delta i)^2
  let S := 6*U-15*V-HH-DD
  let r := V/U
  let h : Fin 15 → ℝ := fun i => eta i/U
  let d : Fin 21 → ℝ := fun i => delta i/U
  let H := ∑ i, h i
  let D := ∑ i, d i
  let A := ∑ i, (h i)^2
  let Q := ∑ i, (d i)^2
  let s := 6-15*r-H-D
  have hsupply : 0 < U ∧ 0 ≤ V ∧ 15*V ≤ 6*U ∧ 0 ≤ L-U-V ∧
      8*V^2 ≤ (3*U-L)*(2*U-3*V) ∧
      L-U-V ≤ 2*U-V-8*V^2/(2*U-3*V) := by
    simpa only [U, V, L, u, v, bottomStart, topIndex, six_bottom_card] using
      (UniformSchmidtHeadCap.literal_rank_six_head_cap (by rfl : 6 ≤ 6)
        (by omega : 6 ≤ n) e l hl h0 hmass happt)
  have hu : 0 < U := hsupply.1
  have hU : U ≠ 0 := ne_of_gt hu
  have hU2 : 0 < U^2 := sq_pos_of_pos hu
  have hr0 : 0 ≤ r := div_nonneg hsupply.2.1 hu.le
  have hrle : r ≤ 2/5 := (div_le_iff₀ hu).mpr (by linarith only [hsupply.2.2.1])
  have heta (i : Fin 15) : 0 ≤ eta i := by
    exact sub_nonneg.mpr (hl (by change i.val ≤ 14; omega))
  have hdelta0 (i : Fin 21) : 0 ≤ delta i := by
    exact sub_nonneg.mpr (hl (by change 6*n-21 ≤ 6*n-21+i.val; omega))
  have hdelta1 (i : Fin 21) : delta i ≤ U := by
    dsimp [delta, tails]
    linarith only [h0 ⟨6*n-21+i.val, by omega⟩]
  have hh (i : Fin 15) : 0 ≤ h i := div_nonneg (heta i) hu.le
  have hd0 (i : Fin 21) : 0 ≤ d i := div_nonneg (hdelta0 i) hu.le
  have hd1 (i : Fin 21) : d i ≤ 1 := (div_le_one hu).mpr (hdelta1 i)
  have hdo : Monotone d := by
    intro i j hij
    apply (div_le_div_iff_of_pos_right hu).mpr
    have ho := hl (show (⟨6*n-21+i.val, by omega⟩ : Fin (6*n)) ≤
      ⟨6*n-21+j.val, by omega⟩ by exact Nat.add_le_add_left hij _)
    dsimp [delta, tails]
    linarith only [ho]
  have hhzero : h 14 = 0 := by simp [h, eta, heads]
  have hdzero : d 0 = 0 := by simp [d, delta, tails, U, u]
  have hH0 : 0 ≤ H := sum_nonneg (fun i _ => hh i)
  have hD0 : 0 ≤ D := sum_nonneg (fun i _ => hd0 i)
  have hA0 : 0 ≤ A := sum_nonneg (fun i _ => sq_nonneg _)
  have hQ0 : 0 ≤ Q := sum_nonneg (fun i _ => sq_nonneg _)
  have ht : (∑ k : Fin (a 6), l (topIndex hp k)) = 15*(U+V)+HH := by
    rw [top_pool_sum hN hp l (fun x => x)]
    simp [sum_add_distrib, U, V, HH, eta]
    ring
  have hb : (∑ k : Fin (b 6), l (bottomIndex hp k)) = 21*U-DD := by
    rw [bottom_pool_sum hN hp l (fun x => x)]
    simp [sum_sub_distrib, U, DD, delta]
  have hK := literal_assignment_psd (by rfl : 6 ≤ 6) (by omega : 6 ≤ n)
    e l happt (Equiv.refl _) (Equiv.refl _)
  dsimp only at hK
  have hcharge : 0 ≤ uniformCharge (assignedK hp l (Equiv.refl _) (Equiv.refl _)) := by
    simpa [uniformCharge, rowSum, dotProduct, mulVec] using
      hK.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  rw [assignedK_charge, ht, hb] at hcharge
  have hS : 0 ≤ S := by dsimp [S]; linarith only [hcharge]
  have hH : H = HH/U := by simp only [H, h, HH, ← sum_div]
  have hD : D = DD/U := by simp only [D, d, DD, ← sum_div]
  have hA : A = AA/U^2 := by simp only [A, h, AA, div_pow, ← sum_div]
  have hQ : Q = QQ/U^2 := by simp only [Q, d, QQ, div_pow, ← sum_div]
  have hsn : s = S/U := by
    dsimp only [s, S]
    rw [hH, hD]
    dsimp only [r]
    field_simp [hU] <;> ring
  have hs : 0 ≤ s := by rw [hsn]; exact div_nonneg hS hu.le
  have hqbox : Q ≤ D := by
    exact sum_le_sum (fun i _ => by
      nlinarith only [mul_nonneg (hd0 i) (sub_nonneg.mpr (hd1 i))])
  have hqmass : Q ≤ D^2 := sum_sq_le_sq_sum_of_nonneg (fun i _ => hd0 i)
  have hheadsq : A ≤ H^2 := sum_sq_le_sq_sum_of_nonneg (fun i _ => hh i)
  have hhcauchy : H^2 ≤ 14*A := FiveRowP2Physical.zero_slot_cauchy (m := 14) h 14 hhzero
  have hdcauchy : D^2 ≤ 20*Q := FiveRowP2Physical.zero_slot_cauchy (m := 20) d 0 hdzero
  have hetaz : eta 0 = L-U-V := by dsimp [eta, heads, L, V, v]; ring
  have hpoly : 8*r^2 ≤ (2-r-h 0)*(2-3*r) := by
    apply (mul_le_mul_iff_of_pos_right hU2).mp
    have hi : (8*r^2)*U^2 = 8*V^2 := by dsimp [r]; field_simp [hU] <;> ring
    have hj : ((2-r-h 0)*(2-3*r))*U^2 = (3*U-L)*(2*U-3*V) := by
      dsimp only [r, h]
      rw [hetaz]
      field_simp [hU] <;> ring
    rw [hi, hj]
    exact hsupply.2.2.2.2.1
  have hden : 0 < 2-3*r := by linarith only [hrle]
  have hpoint0 : h 0 ≤ cap r := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hpoly]
  have hpoint (i : Fin 15) : h i ≤ cap r := by
    apply le_trans _ hpoint0
    apply (div_le_div_iff_of_pos_right hu).mpr
    have ho := hl (show (⟨0, by omega⟩ : Fin (6*n)) ≤
      ⟨i.val, by omega⟩ by change 0 ≤ i.val; omega)
    dsimp [eta, heads]
    linarith only [ho]
  have hc0 : 0 ≤ cap r := (hh 0).trans hpoint0
  have hheadcap : A ≤ cap r*H := by
    calc
      _ ≤ ∑ i, cap r*h i := sum_le_sum (fun i _ => by
        nlinarith only [mul_nonneg (hh i) (sub_nonneg.mpr (hpoint i))])
      _ = _ := by rw [← mul_sum]
  have hheadbox : A ≤ (H-cap r)^2+(cap r)^2 := head_box h (cap r) hc0 hh hpoint
  let π : Edge 6 ≃ Fin 15 := (Fintype.equivFin (Edge 6)).trans (finCongr six_top_card)
  let e01 : Edge 6 := ⟨(0,1), by decide⟩
  let M := K (fun E => U+V+eta (π E)) (fun B => U-delta (tailEquiv B))
  have hM : M.PosSemidef := literal_pool_psd n (by omega) e l happt π tailEquiv
  have hcs := psd_entry_square M hM 0 1
  have h00 : M 0 0 = 2*(U-delta 20) := by
    norm_num [M, K, tailEquiv, tailPlacement]
  have h11 : M 1 1 = 2*(U-delta 19) := by
    norm_num [M, K, tailEquiv, tailPlacement]
  have h01 : M 0 1 = -(V+eta (π e01)+delta 18) := by
    simp [M, K, edge, e01, tailEquiv, tailPlacement]
    ring
  rw [h00, h11, h01] at hcs
  have hx : 0 ≤ V+eta (π e01) := add_nonneg hsupply.2.1 (heta _)
  have hminor : (delta 18)^2 ≤ 4*(U-delta 20)*(U-delta 19) := by
    nlinarith only [hcs, mul_nonneg hx
      (show 0 ≤ V+eta (π e01)+2*delta 18 by linarith only [hx, hdelta0 18])]
  have hminorN : (d 18)^2 ≤ 4*(1-d 20)*(1-d 19) := by
    apply (mul_le_mul_iff_of_pos_left hU2).mp
    have hi : U^2*(d 18)^2 = (delta 18)^2 := by
      dsimp [d]; field_simp [hU] <;> ring
    have hj : U^2*(4*(1-d 20)*(1-d 19)) = 4*(U-delta 20)*(U-delta 19) := by
      dsimp [d]; field_simp [hU] <;> ring
    rwa [hi, hj]
  have htail : Q ≤ max 2 (2*D/3) := by
    have hc := tail_square_cap d (max D 3) (le_max_right _ _) hd0 hd1 hdo
      (le_max_left _ _) hminorN
    by_cases hD3 : D ≤ 3
    · rw [max_eq_right hD3] at hc
      rw [max_eq_left (by linarith : 2*D/3 ≤ 2)]
      norm_num at hc
      exact hc
    · rw [max_eq_left (le_of_not_ge hD3)] at hc
      rw [max_eq_right (by linarith : 2 ≤ 2*D/3)]
      exact hc
  have ht2 : (∑ k : Fin (a 6), (l (topIndex hp k))^2) =
      15*(U+V)^2+2*(U+V)*HH+AA := by
    rw [top_pool_sum hN hp l (fun x => x^2)]
    simp_rw [add_sq]
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, U, V, HH, AA, eta]
    ring
  have hb2 : (∑ k : Fin (b 6), (l (bottomIndex hp k))^2) =
      21*U^2-2*U*DD+QQ := by
    rw [bottom_pool_sum hN hp l (fun x => x^2)]
    simp_rw [sub_sq]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, U, DD, QQ, delta]
    ring
  have hleft : momentLHS hp l = (5/7)*(AA-HH^2/15)+(QQ-DD^2/21) := by
    unfold momentLHS
    rw [variance_expansion (k := a 6) (by rw [six_top_card]; norm_num)
        (fun k => l (topIndex hp k)),
      variance_expansion (k := b 6) (by rw [six_bottom_card]; norm_num)
        (fun k => l (bottomIndex hp k)), ht, hb, ht2, hb2]
    norm_num only [six_top_card, six_bottom_card]
    ring
  have hstart : l (bottomStart hp (bottom_pos (by norm_num : 2 ≤ 6))) = U := by
    change l (bottomStart hp (bottom_pos (by norm_num : 2 ≤ 6))) = l ⟨6*n-21, by omega⟩
    congr 1 <;> simp only [bottomStart, six_bottom_card]
  have hvm := literal_variance_moment (by norm_num : 2 ≤ 6) (by rfl : 6 ≤ 6)
    (by omega : 6 ≤ n) e l hl happt
  dsimp only [momentRHS] at hvm
  norm_num only [Nat.cast_ofNat, show (6 : ℝ) + 1 = 7 by norm_num] at hvm
  change momentLHS hp l ≤ 4*((∑ k : Fin (b 6), l (bottomIndex hp k))-
    (∑ k : Fin (a 6), l (topIndex hp k)))*
      min ((∑ k : Fin (b 6), l (bottomIndex hp k))/7)
        (l (bottomStart hp (bottom_pos (by norm_num : 2 ≤ 6))))-
          2*((∑ k : Fin (b 6), l (bottomIndex hp k))-
            (∑ k : Fin (a 6), l (topIndex hp k)))^2/6 at hvm
  rw [hleft, ht, hb, hstart] at hvm
  have hdiff : (21*U-DD)-(15*(U+V)+HH) = S := by dsimp [S]; ring
  rw [hdiff] at hvm
  have hmin := mul_le_mul_of_nonneg_left (min_le_right ((21*U-DD)/7) U)
    (show 0 ≤ 4*S by positivity)
  have hvarraw : (5/7)*(AA-HH^2/15)+(QQ-DD^2/21) ≤ 4*U*S-S^2/3 := by
    nlinarith only [hvm, hmin]
  have hvscale : ((5/7)*(A-H^2/15)+(Q-D^2/21))*U^2 =
      (5/7)*(AA-HH^2/15)+(QQ-DD^2/21) := by
    rw [hA, hQ, hH, hD]
    field_simp [hU] <;> ring
  have hrscale : (4*s-s^2/3)*U^2 = 4*U*S-S^2/3 := by
    rw [hsn]
    field_simp [hU] <;> ring
  have hvariance : (5/7)*(A-H^2/15)+(Q-D^2/21) ≤ 4*s-s^2/3 := by
    apply (mul_le_mul_iff_of_pos_right hU2).mp
    rwa [hvscale, hrscale]
  refine ⟨hu, ?_⟩
  exact {
    r_nonneg := hr0, r_le := hrle, h_nonneg := hh, d_nonneg := hd0,
    d_le_one := hd1, d_monotone := hdo, h_zero := hhzero, d_zero := hdzero,
    H_nonneg := hH0, D_nonneg := hD0, a_nonneg := hA0, q_nonneg := hQ0,
    mass := hs, q_box := hqbox, q_mass := hqmass,
    head_cauchy := hhcauchy, tail_cauchy := hdcauchy, head_sq := hheadsq,
    head_point_cap := hpoint, head_cap := hheadcap, head_box := hheadbox,
    tail_cap := htail, variance := hvariance }

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowPhysicalMoments
