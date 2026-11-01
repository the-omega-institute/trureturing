/- GID: D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityPauliWeight
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Pauli-weight formula and alternating truncation bounds for qubit SIC k-fidelities. -/
import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.PureState.PureStateHandshake
/-! # Pauli-weight formula and alternating truncation bounds for qubit SIC `k`-fidelities -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
open D5.S3.Quantum.FiniteDimensional D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.PureState.PureStateHandshake Finset Matrix Complex
abbrev QubitIndex (n : ℕ) : Type := Fin n → Fin 2
abbrev PauliLabel (n : ℕ) : Type := Fin n → Fin 4
abbrev QubitMap (n : ℕ) : Type := MatrixMap (QubitIndex n) (QubitIndex n) ℂ
def pauli1 : Fin 4 → QubitMatrix | 0 => 1 | 1 => qubitX | 2 => !![0, -I; I, 0] | 3 => qubitZ
def pauliN (n : ℕ) (β : PauliLabel n) : Matrix (QubitIndex n) (QubitIndex n) ℂ := fun x y => ∏ i :
    Fin n, pauli1 (β i) (x i) (y i)
def hammingWeight {n : ℕ} (β : PauliLabel n) : ℕ := (Finset.univ.filter (fun i => β i ≠ 0)).card
def processMatrix {n : ℕ} (Λ : QubitMap n) (β γ : PauliLabel n) : ℂ := ((4 : ℂ) ^ n)⁻¹ * ∑ u, ∑ x, ∑
    v, ∑ y, pauliN n β x u * Λ (single x y 1) u v * pauliN n γ v y
def pauliTwirlWeight {n : ℕ} (Λ : QubitMap n) (β : PauliLabel n) : ℂ := processMatrix Λ β β
def pauliWeightSum {n : ℕ} (Λ : QubitMap n) (w : ℕ) : ℂ := ∑ β ∈ univ.filter (fun β => hammingWeight
    β = w), pauliTwirlWeight Λ β
def maxEntangledVec (n : ℕ) : QubitIndex n × QubitIndex n → ℂ := fun p => if p.1 = p.2 then
    (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℝ) : ℂ) else 0
def maxEntangledProj (n : ℕ) := vecMulVec (maxEntangledVec n) (star (maxEntangledVec n))
def processFidelity {n : ℕ} (Λ : QubitMap n) : ℂ := star (maxEntangledVec n) ⬝ᵥ ((MatrixMap.kron
    (LinearMap.id : QubitMap n) Λ) (maxEntangledProj n)).mulVec (maxEntangledVec n)
def pauliChannel {n : ℕ} (q : PauliLabel n → ℝ) : QubitMap n :=
  { toFun X := ∑ β, (q β : ℂ) • (pauliN n β * X * pauliN n β), map_smul' c _ := by
      simp [smul_sum, smul_comm c], map_add' _ _ := by simp [mul_add, add_mul, sum_add_distrib] }
def complexPauliTwirl {n : ℕ} (Λ : QubitMap n) : QubitMap n :=
  { toFun X := ∑ β, pauliTwirlWeight Λ β • (pauliN n β * X * pauliN n β), map_smul' c _ := by
      simp [smul_sum, smul_comm c], map_add' _ _ := by simp [mul_add, add_mul, sum_add_distrib] }
def realTwirlWeight {n : ℕ} (Λ : QubitMap n) (β : PauliLabel n) : ℝ := (pauliTwirlWeight Λ β).re
def realWeightSum {n : ℕ} (Λ : QubitMap n) (w : ℕ) : ℝ := (pauliWeightSum Λ w).re
def realProcessFidelity {n : ℕ} (Λ : QubitMap n) : ℝ := (processFidelity Λ).re
def IsQubitSICProjector (ρ : Fin 4 → QubitMatrix) : Prop := (∀ a, (ρ a).IsHermitian ∧
    ρ a * ρ a = ρ a ∧ trace (ρ a) = 1) ∧ ∀ a b, a ≠ b → trace (ρ a * ρ b) = (3 : ℂ)⁻¹
def IsUnitVectorQubitSIC (ψ : Fin 4 → Fin 2 → ℂ) : Prop := (∀ a : Fin 4, star (ψ a) ⬝ᵥ ψ a = 1) ∧ ∀
    a b : Fin 4, a ≠ b → Complex.normSq (star (ψ a) ⬝ᵥ ψ b) = (3 : ℝ)⁻¹
def sicOverlapB : Matrix (Fin 4) (Fin 4) ℂ := fun a b => if a = b then 1 else (3 : ℂ)⁻¹
def sicMatrixA : Matrix (Fin 4) (Fin 4) ℂ := fun a b => if a = b then -(4 : ℂ)⁻¹ else (4 : ℂ)⁻¹
def productSIC {n : ℕ} (ρ : Fin n → Fin 4 → QubitMatrix) (a : PauliLabel n) : Matrix (QubitIndex n)
    (QubitIndex n) ℂ := fun x y => ∏ i : Fin n, ρ i (a i) (x i) (y i)
def sicSubsetKernel (n : ℕ) (T : Finset (Fin n)) (a b : PauliLabel n) : ℂ := ∏ i : Fin n, if i ∈ T
    then sicMatrixA (a i) (b i) else (1 : Matrix (Fin 4) (Fin 4) ℂ) (a i) (b i)
def kFidelity {n : ℕ} (ρ : Fin n → Fin 4 → QubitMatrix) (k : ℕ) (Λ : QubitMap n) : ℂ := ((4 : ℂ) ^
    n)⁻¹ * ∑ T ∈ univ.filter (fun T : Finset (Fin n) => T.card ≤ k), (-1 : ℂ) ^ T.card * ∑ a, ∑ b,
    sicSubsetKernel n T a b * trace (productSIC ρ b * Λ (productSIC ρ a))
def realKFidelity {n : ℕ} (ρ : Fin n → Fin 4 → QubitMatrix) (k : ℕ) (Λ : QubitMap n) : ℝ :=
    (kFidelity ρ k Λ).re
def sicE (ρ : Fin 4 → QubitMatrix) (β γ : Fin 4) : ℂ := (4 : ℂ)⁻¹ * ∑ a, trace (ρ a * pauli1 β * ρ a
    * pauli1 γ)
def sicAlpha (ρ : Fin 4 → QubitMatrix) (β γ : Fin 4) : ℂ := (4 : ℂ)⁻¹ * ∑ a, ∑ b, sicMatrixA a b *
    trace (ρ b * pauli1 β * ρ a * pauli1 γ)
private abbrev pN := pauliN
private abbrev pMx {n} := @processMatrix n
private abbrev pTW {n} := @pauliTwirlWeight n
private abbrev pWS {n} := @pauliWeightSum n
private abbrev hWt {n} := @hammingWeight n
private abbrev rWS {n} := @realWeightSum n
private def pM {n} (M : Fin n → QubitMatrix) : Matrix (QubitIndex n) (QubitIndex n) ℂ :=
  fun x y => ∏ i, M i (x i) (y i)
private abbrev sE0 (b g : Fin 4) : ℂ := if b = g then (if b = 0 then 1 else (3 : ℂ)⁻¹) else 0
private abbrev sA0 (b g : Fin 4) : ℂ := if b = g then (if b = 0 then 0 else (3 : ℂ)⁻¹) else 0
private abbrev fss {α} [Fintype α] {f : α → ℂ} := @Fintype.sum_eq_single α ℂ _ _ f
private theorem sc2 {α β M} [Fintype α] [Fintype β] [AddCommMonoid M] {f g : α → β → M}
  (h : ∀ a b, f a b = g a b) : (∑ a, ∑ b, f a b) = ∑ a, ∑ b, g a b := by simp_rw [h]
private theorem sc4 {α β γ δ M} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M] {f
    g : α → β → γ → δ → M} (h : ∀ a b c d, f a b c d = g a b c d) : (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)
    = ∑ a, ∑ b, ∑ c, ∑ d, g a b c d := sc2 fun a b => sc2 fun c d => h a b c d
private theorem p1_tr (b c : Fin 4) : trace (pauli1 b * pauli1 c) = if b = c then 2 else 0 := (by
  fin_cases b <;> fin_cases c <;> simp [pauli1, qubitX, qubitZ, trace, Matrix.diag, mul_apply,
    Fin.sum_univ_two] <;> norm_num)
private theorem p1_comp (x u v y : Fin 2) : ∑ b : Fin 4, pauli1 b x u * pauli1 b v y = if x = y ∧ u
  = v then 2 else 0 := (by fin_cases x <;> fin_cases u <;> fin_cases v <;> fin_cases y <;>
  simp [pauli1, qubitX, qubitZ, Fin.sum_univ_four] <;> norm_num)
private theorem pM_mul {n} (M N : Fin n → QubitMatrix) : pM M * pM N = pM (fun i => M i * N i) :=
  (by ext x z; simp only [mul_apply, pM]; rw [Fintype.prod_sum]; simp_rw [← prod_mul_distrib])
private theorem pM_tr {n} (M : Fin n → QubitMatrix) : trace (pM M) = ∏ i, trace (M i) :=
  (by simp only [trace, Matrix.diag, pM]; exact (Fintype.prod_sum fun i a => M i a a).symm)
private theorem pN_tr (n : ℕ) (β γ : PauliLabel n) : trace (pN n β * pN n γ) = if β = γ then (2 : ℂ)
  ^ n else 0 := by
  change trace (pM (fun i => pauli1 (β i)) * pM (fun i => pauli1 (γ i))) = _; rw [pM_mul, pM_tr]
  simp_rw [p1_tr]; split_ifs with h; (· subst h; simp)
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h; exact prod_eq_zero (mem_univ i) (by simp [hi])
private theorem scomm21 {α β M} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α → α → β → M) :
  (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := (sum_congr rfl fun _ _ => sum_comm).trans
    sum_comm
private theorem scomm22 {α β M} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α → α → β → β → M) :
  (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d :=
    (scomm21 _).trans (sum_congr rfl fun _ _ => scomm21 _)
private theorem s_hw {n : ℕ} (f : ℕ → ℂ) (g : PauliLabel n → ℂ) : ∑ β, g β * f (hWt β) = ∑ w ∈ range
  (n + 1), f w * ∑ β ∈ univ.filter (fun β => hWt β = w), g β := (by
  have hle (β : PauliLabel n) : hWt β < n + 1 := Nat.lt_succ_of_le (le_trans (card_filter_le _ _)
    (by simp)); rw [← sum_fiberwise_of_maps_to (fun β _ => mem_range.mpr (hle β))]; exact sum_congr
    rfl fun w _ => (by rw [mul_sum]; exact sum_congr rfl fun β hβ =>
      (by rw [(mem_filter.mp hβ).2, mul_comm])))
theorem pauli_process_matrix_and_fidelity_characterization (n : ℕ) : (∀ (Λ : QubitMap n), (∀ X, Λ X
  = ∑ β : PauliLabel n, ∑ γ : PauliLabel n, processMatrix Λ β γ • (pauliN n β * X * pauliN n γ)) ∧
  (∀ c : PauliLabel n → PauliLabel n → ℂ, (∀ X, Λ X = ∑ β : PauliLabel n, ∑ γ : PauliLabel n, c β γ
  • (pauliN n β * X * pauliN n γ)) → ∀ β γ, c β γ = processMatrix Λ β γ)) ∧ (∀ (Λ : QubitMap n),
  processFidelity Λ = pauliTwirlWeight Λ 0 ∧ pauliWeightSum Λ 0 = pauliTwirlWeight Λ 0 ∧ ∑ w ∈
  Finset.range (n + 1), pauliWeightSum Λ w = ∑ β : PauliLabel n, pauliTwirlWeight Λ β) ∧ (∀ (Λ :
  QubitMap n), (Λ.IsTracePreserving ↔ ∑ β : PauliLabel n, ∑ γ : PauliLabel n, processMatrix Λ β γ •
  (pauliN n γ * pauliN n β) = 1) ∧ (Λ.IsTracePreserving → ∑ β : PauliLabel n, pauliTwirlWeight Λ β =
  1 ∧ ∑ w ∈ Finset.range (n + 1), pauliWeightSum Λ w = 1)) ∧ (∀ (Λ : QubitMap n),
  Λ.IsCompletelyPositive → (∀ β : PauliLabel n, (pauliTwirlWeight Λ β).im = 0 ∧ 0 ≤
  (pauliTwirlWeight Λ β).re) ∧ (∀ w : ℕ, ((realWeightSum Λ w : ℝ) : ℂ) = pauliWeightSum Λ w ∧ 0 ≤
  realWeightSum Λ w) ∧ ((realProcessFidelity Λ : ℝ) : ℂ) = processFidelity Λ) ∧ (∀ (q : PauliLabel n
  → ℝ), (∀ β γ : PauliLabel n, processMatrix (pauliChannel q) β γ = if β = γ then (q β : ℂ) else 0)
  ∧ ((∀ β : PauliLabel n, 0 ≤ q β) → (pauliChannel q).IsCompletelyPositive) ∧ (∑ β : PauliLabel n, q
  β = 1 → (pauliChannel q).IsTracePreserving)) := (by
  have pN_zero : pN n 0 = 1 := (by ext x y; simp [pN, pauliN, pauli1, one_apply, prod_boole,
    funext_iff]); have mul_sng (A B : Matrix (QubitIndex n) (QubitIndex n) ℂ) (x y u v) :
    (A * single x y (1 : ℂ) * B) u v = A u x * B y v :=
    (by simp [mul_apply, single_apply, ite_and, ite_mul, mul_ite]); have pN_cT (β) :
    (pN n β)ᴴ = pN n β := (by
    ext x y; simp only [conjTranspose_apply, pN, pauliN, star_prod]; exact prod_congr rfl fun i _ =>
      (by generalize β i = b, x i = u, y i = v; fin_cases b <;> fin_cases u <;> fin_cases v <;> simp
            [pauli1, qubitX, qubitZ])); have pN_sq (β) : pN n β * pN n β = 1 := (by
    change pM (fun i => pauli1 (β i)) * pM (fun i => pauli1 (β i)) = 1; rw [pM_mul]; simp_rw [show ∀
      b, pauli1 b * pauli1 b = 1 from fun b => (by
      ext i j; fin_cases b <;> fin_cases i <;> fin_cases j <;> simp [pauli1, qubitX, qubitZ,
        mul_apply, Fin.sum_univ_two])]; exact pN_zero); have pN_comp (x u v y) : ∑ β, pN n β x u *
    pN n β v y = if x = y ∧ u = v then (2 : ℂ) ^ n else 0 := (by
    trans (∏ i : Fin n, ∑ b : Fin 4, pauli1 b (x i) (u i) * pauli1 b (v i) (y i));
    (· rw [Fintype.prod_sum]; exact sum_congr rfl fun _ _ => (by simp [pauliN, ← prod_mul_distrib]))
    (· simp_rw [p1_comp]; by_cases h : x = y ∧ u = v; (· rcases h with ⟨rfl, rfl⟩; simp);
       (· have h' := h; simp only [funext_iff, ← forall_and, not_forall] at h'; obtain ⟨i, hi⟩ := h'
          simpa [h] using prod_eq_zero (mem_univ i) (by simp [hi]))));
    have i4m2 (z) : ((4 : ℂ) ^ n)⁻¹ * (z * (2 : ℂ) ^ n * (2 : ℂ) ^ n) = z := (by
    have h4 : ((2 : ℂ) ^ n) * ((2 : ℂ) ^ n) = (4 : ℂ) ^ n := (by rw [← mul_pow]; norm_num); rw [show
      z * (2 : ℂ) ^ n * (2 : ℂ) ^ n = (4 : ℂ) ^ n * z from (by rw [← h4]; ring), ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero n (by norm_num)), one_mul]); have pMat_eq (Λ β γ) : pMx Λ β γ =
    ((4 : ℂ) ^ n)⁻¹ * ∑ x, ∑ y, (pN n β * Λ (single x y 1) * pN n γ) x y := (by
    unfold pMx processMatrix; congr 1; simp only [mul_apply, sum_mul, mul_assoc]; rw [sum_comm];
      exact sum_congr rfl fun x _ => (by rw [scomm21]; exact sum_congr rfl fun y _ => sum_comm));
    have pMat_rec (c : PauliLabel n → PauliLabel n → ℂ) (Λ : QubitMap n) (hΛ : ∀ X, Λ X = ∑ β, ∑ γ,
    c β γ • (pN n β * X * pN n γ)) (β γ) : pMx Λ β γ = c β γ := (by
    rw [pMat_eq, ← i4m2 (c β γ)]; congr 1; simp_rw [hΛ, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ←
      Matrix.mul_assoc, Matrix.mul_assoc (_ * single _ _ _), mul_sng]; rw [scomm22]; simp_rw [←
      mul_sum, ← sum_mul]; have ht (M : Matrix (QubitIndex n) (QubitIndex n) ℂ) : ∑ x, M x x = trace
      M := rfl; simp_rw [ht, pN_tr]; simp [ite_mul, mul_ite, eq_comm, ← mul_assoc]); have pMat_exp
    (Λ X) : Λ X = ∑ β, ∑ γ, pMx Λ β γ • (pN n β * X * pN n γ) := (by
    have m_sng (Y : Matrix (QubitIndex n) (QubitIndex n) ℂ) : Y = ∑ x, ∑ y, Y x y • single x y 1 :=
      (by ext i j; simp [single_apply, Matrix.sum_apply, ite_and]); have hs (x₀ y₀) :
      Λ (single x₀ y₀ 1) = ∑ β, ∑ γ, pMx Λ β γ • (pN n β * single x₀ y₀ 1 * pN n γ) := (by
      ext u₀ v₀; simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pMx, processMatrix,
        mul_sng]; rw [← i4m2 (Λ (single x₀ y₀ 1) u₀ v₀)]; simp_rw [mul_assoc ((4 : ℂ) ^ n)⁻¹, ←
        mul_sum]; congr 1; symm; simp_rw [sum_mul]; rw [scomm22, sc2 fun _ _ => scomm22 _]; refine
        Eq.trans (sc4 fun u x v y => show _ = Λ (single x y 1) u v * ((∑ β, pN n β x u * pN n β u₀
        x₀) * (∑ γ, pN n γ v y * pN n γ y₀ v₀)) from (by
          simp_rw [sum_mul, mul_sum]; exact sc2 fun _ _ => (by ring)))
        (by simp_rw [pN_comp]; simp [ite_and, mul_ite, ite_mul]; ring)); rw [m_sng X]; simp only
        [map_sum, map_smul, hs, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
        smul_sum]; rw [scomm22]; exact sc4 fun _ _ _ _ => smul_comm _ _ _); have hF0 (Λ :
    QubitMap n) : processFidelity Λ = pTW Λ 0 := (by
    unfold processFidelity; change _ = pMx Λ 0 0; rw [pMat_eq, pN_zero]; let c := (((Real.sqrt ((2 :
      ℝ) ^ n))⁻¹ : ℝ) : ℂ); have hc2 : c * c = ((2 : ℂ) ^ n)⁻¹ := (by
      dsimp [c]; rw [← ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by positivity)]; push_cast; rfl);
      have hc4 : c * c * c * c = ((4 : ℂ) ^ n)⁻¹ :=
        (by rw [mul_assoc (c * c), hc2, ← mul_inv, ← mul_pow]; norm_num); have hme (a b c₁ d) :
      maxEntangledProj n (a, b) (c₁, d) = if a = b ∧ c₁ = d then c * c else 0 := (by
      by_cases h1 : a = b <;> by_cases h2 : c₁ = d <;> simp [maxEntangledProj, maxEntangledVec,
        vecMulVec_apply, c, h1, h2]); have hkron (u v) : ((MatrixMap.kron LinearMap.id Λ)
      (maxEntangledProj n)) (u, u) (v, v) = c * c * Λ (single u v 1) u v := Eq.trans (b := ∑ x, ∑ y,
      single x y (1 : ℂ) u v * Λ (single x y 1) u v * (c * c))
      (by rw [MatrixMap.kron_def]; simp [hme, ite_and, mul_ite] <;> ring)
      (by rw [fss u fun x hx => (by simp [hx]), fss v fun y hy => (by simp [hy])]; simp; ring);
      simp only [Matrix.one_mul, Matrix.mul_one, dotProduct, mulVec, Fintype.sum_prod_type, ← hc4,
      mul_sum]; exact sum_congr rfl fun u _ => (by
      rw [fss u fun d₁ h => (by simp [maxEntangledVec, h.symm])]; simp only [Pi.star_apply,
        maxEntangledVec, ↓reduceIte, star_def, conj_ofReal]; exact sum_congr rfl fun v _ =>
        (by rw [fss v fun d₂ h => (by simp [h.symm]), hkron]; simp [c]; ring))); have hWsum (Λ) :
    ∑ w ∈ range (n + 1), pWS Λ w = ∑ β, pTW Λ β :=
    (by simpa [pWS, pauliWeightSum] using (s_hw (fun _ => 1) (pTW Λ)).symm); refine ⟨fun Λ =>
    ⟨pMat_exp Λ, fun c hc β γ => (pMat_rec c Λ hc β γ).symm⟩, fun Λ => ⟨hF0 Λ, (by
    unfold pauliWeightSum; rw [show univ.filter (fun β : PauliLabel n => hWt β = 0) = {0} from
      (by ext β; simp [hWt, hammingWeight, card_eq_zero, filter_eq_empty_iff, funext_iff]),
      sum_singleton]), hWsum Λ⟩, fun Λ => (by
    have htr_f (X) : trace (Λ X) = trace ((∑ β, ∑ γ, pMx Λ β γ • (pN n γ * pN n β)) * X) := (by
      rw [pMat_exp Λ X]; simp only [trace_sum, trace_smul, smul_eq_mul, Matrix.sum_mul,
        Matrix.smul_mul]; exact sc2 fun β γ => congrArg (pMx Λ β γ * ·) (trace_mul_cycle _ X _));
    have hiff : Λ.IsTracePreserving ↔ ∑ β, ∑ γ, pMx Λ β γ • (pN n γ * pN n β) = 1 := ⟨fun hTP => (by
      ext x y; have hxy := hTP (single y x 1); rw [htr_f] at hxy; simpa [trace, Matrix.diag,
        mul_apply, single_apply, one_apply, ite_and, eq_comm] using hxy), fun h1 X =>
      (by rw [htr_f, h1, Matrix.one_mul])⟩; refine ⟨hiff, fun hTP => ?_⟩; have htr1 := congrArg
      trace (hiff.mp hTP); simp only [trace_sum, trace_smul, smul_eq_mul, pN_tr, trace_one,
      Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, mul_ite, mul_zero,
      sum_ite_eq', mem_univ, ↓reduceIte, ← sum_mul] at htr1; have hsum1 := mul_right_cancel₀
      (pow_ne_zero n (by norm_num)) (htr1.trans (one_mul _).symm); exact
      ⟨hsum1, (hWsum Λ).trans hsum1⟩), fun Λ hCP => (by
    have htw β : (pTW Λ β).im = 0 ∧ 0 ≤ (pTW Λ β).re ∧ (realTwirlWeight Λ β : ℂ) = pTW Λ β := (by
      obtain ⟨K, hK⟩ := MatrixMap.IsCompletelyPositive.exists_kraus Λ hCP; let z (k) := trace (pN n
        β * K k); have heq : pTW Λ β = ((((4 : ℝ) ^ n)⁻¹ * ∑ k, normSq (z k) : ℝ) : ℂ) := (by
          rw [hK]; change pMx (MatrixMap.of_kraus K K) β β = _; rw [pMat_eq]; push_cast; congr 1
          simp_rw [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
            Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, ← Matrix.mul_assoc,
            Matrix.mul_assoc (_ * single _ _ _), mul_sng, show ∀ k, (K k)ᴴ * pN n β =
            (pN n β * K k)ᴴ from fun k => (by rw [conjTranspose_mul, pN_cT]), conjTranspose_apply]
          rw [scomm21]; exact sum_congr rfl fun k _ => (by
            rw [sum_comm, ← Complex.mul_conj, ← star_def]
            simp [z, trace, Matrix.diag, star_sum, sum_mul, mul_sum]))
      change (pTW Λ β).im = 0 ∧ 0 ≤ (pTW Λ β).re ∧ ((pTW Λ β).re : ℂ) = pTW Λ β; rw [heq, ofReal_re]
      exact ⟨ofReal_im _, mul_nonneg (by positivity) (sum_nonneg fun _ _ => normSq_nonneg _), rfl⟩)
    refine ⟨fun β => ⟨(htw β).1, (htw β).2.1⟩, fun w => (by
      rw [show realWeightSum Λ w = ∑ β ∈ univ.filter (fun β : PauliLabel n => hWt β = w),
        realTwirlWeight Λ β from (by simp [realWeightSum, pauliWeightSum, realTwirlWeight, hWt])];
      exact ⟨(by unfold pauliWeightSum; push_cast; exact sum_congr rfl fun β _ => (htw β).2.2),
        sum_nonneg fun β _ => (htw β).2.1⟩),
      (by unfold realProcessFidelity; rw [hF0 Λ]; exact (htw 0).2.2)⟩), fun q => (by
    refine ⟨fun β γ => pMat_rec (fun β γ => if β = γ then (q β : ℂ) else 0) (pauliChannel q) (fun X
      => (by change (∑ β', (q β' : ℂ) • _) = _; simp [ite_smul])) β γ, fun hq => (by
      let K (β) := ((Real.sqrt (q β) : ℝ) : ℂ) • pN n β; rw [show pauliChannel q =
        MatrixMap.of_kraus K K from (by
        ext X u v; simp only [pauliChannel, MatrixMap.of_kraus, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.sum_apply, Matrix.sum_apply, K, conjTranspose_smul, pN_cT, Matrix.smul_mul,
          Matrix.mul_smul, smul_smul, Matrix.smul_apply, smul_eq_mul, star_def, conj_ofReal]
        exact sum_congr rfl fun β _ => (by rw [← ofReal_mul, Real.mul_self_sqrt (hq β)]))]
      exact MatrixMap.of_kraus_isCompletelyPositive K), fun hsum X => (by
      change trace (∑ β, (q β : ℂ) • (pN n β * X * pN n β)) = _; have htr (β) : trace (pN n β * X *
        pN n β) = trace X := (by rw [trace_mul_cycle (pN n β) X (pN n β), pN_sq, Matrix.one_mul]);
        simp only [trace_sum, trace_smul, smul_eq_mul, htr, ← sum_mul]; rw [show (∑ β, (q β : ℂ)) =
        1 from (by exact_mod_cast hsum), one_mul])⟩)⟩)
theorem isQubitSICProjector_iff_exists_unitVectorQubitSIC (ρ : Fin 4 → QubitMatrix) :
  IsQubitSICProjector ρ ↔ ∃ ψ : Fin 4 → Fin 2 → ℂ, IsUnitVectorQubitSIC ψ ∧ ∀ a : Fin 4, ρ a =
  rankOneDensity (ψ a) := (by
  have htr_rod (u v : Fin 2 → ℂ) : trace (rankOneDensity u * rankOneDensity v) =
    (Complex.normSq (star u ⬝ᵥ v) : ℂ) := (by
    rw [← Complex.mul_conj]; simp only [rankOneDensity, trace, Matrix.diag, mul_apply,
      vecMulVec_apply, Pi.star_apply, dotProduct, Fin.sum_univ_two, star_def, map_add, map_mul,
      RingHomCompTriple.comp_apply, RingHom.id_apply]; ring); refine ⟨fun ⟨hp, hov⟩ => (by
    have hex (a) : ∃ v, star v ⬝ᵥ v = 1 ∧ ρ a = rankOneDensity v := (by
      obtain ⟨hH, hId, hTr⟩ := hp a; let M := ρ a; have htr : M 0 0 + M 1 1 = 1 :=
        (by simpa [M, trace, Matrix.diag, Fin.sum_univ_two] using hTr); obtain ⟨k, hk⟩ : ∃ k, 0 < (M
        k k).re := if h : 0 < (M 0 0).re then ⟨0, h⟩ else ⟨1, (by
        have := congrArg Complex.re htr; simp at this; linarith)⟩; have hkk : ((M k k).re : ℂ) = M k
        k := (by
          have h := congrArg Complex.im (congrFun (congrFun hH k) k); simp only
            [conjTranspose_apply, star_def, Complex.conj_im] at h
          exact Complex.ext rfl (by simp; linarith)); let s := ((Real.sqrt (M k k).re : ℝ) : ℂ)
      let v (i) := M i k / s; have hss : s * (starRingEnd ℂ) s = M k k := (by
        dsimp [s]; rw [conj_ofReal, ← ofReal_mul, Real.mul_self_sqrt (le_of_lt hk), hkk]); have hMv
        : M = rankOneDensity v := (by
        have h00 := congrFun (congrFun hId 0) 0; simp only [mul_apply, Fin.sum_univ_two] at h00;
          have hdet : M 0 1 * M 1 0 = M 0 0 * M 1 1 := (by linear_combination h00 - M 0 0 * htr);
          have hcomm := (mul_comm (M 1 0) (M 0 1)).trans hdet; ext i j; simp only [rankOneDensity,
          vecMulVec_apply, Pi.star_apply, v, star_def, map_div₀, div_mul_div_comm, hss, show
          (starRingEnd ℂ) (M j k) = M k j from congrFun (congrFun hH k) j]; exact (eq_div_iff
          (by rw [← hkk]; exact_mod_cast ne_of_gt hk)).mpr (by
          fin_cases k <;> fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, hdet,
            hcomm] <;> ring)); refine ⟨v, ?_, hMv⟩; rw [show star v ⬝ᵥ v = trace (rankOneDensity v)
        from (by simp [dotProduct, rankOneDensity, trace, Matrix.diag, vecMulVec_apply,
          Fin.sum_univ_two, mul_comm]), ← hMv]; exact hTr); choose ψ hu hρ using hex;
      refine ⟨ψ, ⟨hu, fun a b hab => ofReal_inj.mp ?_⟩, hρ⟩; rw [← htr_rod, ← hρ a, ← hρ b, hov a b
      hab]; push_cast; rfl), fun ⟨ψ, ⟨hu, hov⟩, hρ⟩ => ⟨fun a => (by
    rw [hρ a]; refine ⟨(by ext i j; simp [rankOneDensity, conjTranspose_apply, vecMulVec_apply,
      mul_comm]), (pure_state_handshake (ψ a) (hu a) 1).1, ?_⟩; have h3 :=
      (pure_state_handshake (ψ a) (hu a) 1).2.2; rw [Matrix.one_mul, Matrix.one_mulVec] at h3; exact
      h3.symm.trans (hu a)), fun a b hab => (by
    rw [hρ a, hρ b, htr_rod, hov a b hab]; push_cast; rfl)⟩⟩)
private theorem p_split {n} (T : Finset (Fin n)) (f g : Fin n → ℂ) : (∏ i, if i ∈ T then f i else g
  i) = (∏ i ∈ T, f i) * (∏ i ∈ Tᶜ, g i) := (by
  rw [← prod_compl_mul_prod T, mul_comm]; exact congrArg₂ (· * ·) (prod_congr rfl fun i hi =>
    (by simp [hi])) (prod_congr rfl fun i hi => (by simp [mem_compl.mp hi])))
theorem qubit_sic_matrices_and_per_qubit_traces (n : ℕ) : (sicOverlapB * (1 - sicMatrixA) = 1 ∧ (1 -
  sicMatrixA) * sicOverlapB = 1) ∧ (∀ a : Fin 4, (sicOverlapB * (1 - Matrix.of (fun i j : Fin 4 =>
  (1 - if i = j then (5 : ℂ) else 0) / 4))) a a = 7 / 4) ∧ (∀ a b : PauliLabel n, (∏ i : Fin n, (1 -
  sicMatrixA) (a i) (b i)) = ∑ T : Finset (Fin n), (-1 : ℂ) ^ T.card * sicSubsetKernel n T a b ∧ (∏
  i : Fin n, (1 - sicMatrixA) (a i) (b i)) = (-1 : ℂ) ^ (Finset.univ.filter (fun i : Fin n => a i ≠
  b i)).card * (5 : ℂ) ^ (n - (Finset.univ.filter (fun i : Fin n => a i ≠ b i)).card) / (4 : ℂ) ^ n)
  ∧ (∀ ρ₀ : Fin 4 → QubitMatrix, IsQubitSICProjector ρ₀ → (∀ x₁ x₂ y₁ y₂ : Fin 2, ∑ a : Fin 4, ρ₀ a
  x₁ y₁ * ρ₀ a x₂ y₂ = (2 / 3 : ℂ) * ((if x₁ = y₁ ∧ x₂ = y₂ then 1 else 0) + (if x₁ = y₂ ∧ x₂ = y₁
  then 1 else 0))) ∧ ∑ a : Fin 4, ρ₀ a = (2 : ℂ) • (1 : QubitMatrix) ∧ (∀ X Y : QubitMatrix, ∑ a :
  Fin 4, Matrix.trace (ρ₀ a * X) * Matrix.trace (ρ₀ a * Y) = (2 / 3 : ℂ) * (Matrix.trace (X * Y) +
  Matrix.trace X * Matrix.trace Y)) ∧ (∀ β γ : Fin 4, sicE ρ₀ β γ = if β = γ then (if β = 0 then 1
  else (3 : ℂ)⁻¹) else 0) ∧ (∀ β γ : Fin 4, sicAlpha ρ₀ β γ = if β = γ then (if β = 0 then 0 else (3
  : ℂ)⁻¹) else 0)) ∧ (∀ (ρ : Fin n → Fin 4 → QubitMatrix) (T : Finset (Fin n)) (β γ : PauliLabel n),
  ((4 : ℂ) ^ n)⁻¹ * ∑ a : PauliLabel n, ∑ b : PauliLabel n, sicSubsetKernel n T a b * Matrix.trace
  (productSIC ρ b * pauliN n β * productSIC ρ a * pauliN n γ) = ∏ i : Fin n, if i ∈ T then sicAlpha
  (ρ i) (β i) (γ i) else sicE (ρ i) (β i) (γ i)) ∧ (∀ (ρ : Fin n → Fin 4 → QubitMatrix), (∀ i : Fin
  n, IsQubitSICProjector (ρ i)) → ∀ (k : ℕ) (Λ : QubitMap n), kFidelity ρ k Λ = ∑ β : PauliLabel n,
  pauliTwirlWeight Λ β * ∑ T ∈ @Finset.filter _ (fun T : Finset (Fin n) => T.card ≤ k)
  (Classical.decPred _) Finset.univ, (-1 : ℂ) ^ T.card * (∏ i ∈ T, sicAlpha (ρ i) (β i) (β i)) *
  (∏ i ∈ Tᶜ, sicE (ρ i) (β i) (β i)) ∧ kFidelity ρ k Λ = kFidelity ρ k (complexPauliTwirl Λ)) ∧ (∀
  (ρ₁ ρ₂ : Fin n → Fin 4 → QubitMatrix), (∀ i : Fin n, IsQubitSICProjector (ρ₁ i)) → (∀ i : Fin n,
  IsQubitSICProjector (ρ₂ i)) → ∀ (k : ℕ) (Λ : QubitMap n), kFidelity ρ₁ k Λ = kFidelity ρ₂ k Λ) :=
  (by
  have hpm := (pauli_process_matrix_and_fidelity_characterization n).1; have hs1 {ρ} (hρ :
    IsQubitSICProjector ρ) : ∑ a, ρ a = (2 : ℂ) • (1 : QubitMatrix) ∧ (∀ X Y, ∑ a, trace (ρ a * X) *
    trace (ρ a * Y) = (2 / 3 : ℂ) * (trace (X * Y) + trace X * trace Y)) ∧ (∀ β γ, sicE ρ β γ = sE0
    β γ) ∧ (∀ β γ, sicAlpha ρ β γ = sA0 β γ) := (by
    let c (a b : Fin 4) := (2 : ℂ)⁻¹ * trace (ρ a * pauli1 b); have hρ_e (a) : ρ a = ∑ b, c a b •
      pauli1 b := (by
      ext x y; fin_cases x <;> fin_cases y <;> simp [c, pauli1, qubitX, qubitZ, trace, Matrix.diag,
        mul_apply, Fin.sum_univ_four, Fin.sum_univ_two] <;> ring_nf <;> simp [I_sq] <;> ring); have
      hc0 (a) : c a 0 = (2 : ℂ)⁻¹ := (by simp [c, pauli1, (hρ.1 a).2.2]); have hci (a a') :
      2 * ∑ b, c a b * c a' b = sicOverlapB a a' := (by
      have hob : trace (ρ a * ρ a') = sicOverlapB a a' := (by
        unfold sicOverlapB; by_cases h : a = a'; (· subst h; simp [(hρ.1 a).2.1, (hρ.1 a).2.2]);
          (· simp [h, hρ.2 a a' h])); rw [← hob, hρ_e a, hρ_e a']; simp_rw [Matrix.sum_mul,
        Matrix.mul_sum]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_sum,
        trace_smul, smul_eq_mul, p1_tr, mul_sum]; exact sum_congr rfl fun b _ => (by
        rw [fss b fun b' hb' => (by simp [hb'.symm])]; simp; ring)); let C := Matrix.of c; let D :
      Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun b b' => if b = b' then (if b = 0 then 1 else 3) else
      0; have hCDCt : (C * D) * C.transpose = 1 := (by
      ext a a'; have h := hci a a'; unfold sicOverlapB at h; simp only [C, D, mul_apply,
        transpose_apply, of_apply, Fin.sum_univ_four, Fin.isValue, ↓reduceIte, hc0] at h ⊢; by_cases
        ha : a = a' <;> simp [ha, one_apply] at h ⊢ <;> linear_combination (3 / 2 : ℂ) * h); have
      hco (β γ) : ∑ a, c a β * c a γ = sE0 β γ := (by
      have h1 : (C.transpose * C) * D = 1 :=
        (by rw [Matrix.mul_assoc]; exact mul_eq_one_comm.mp hCDCt); have h := congrArg (fun M :
        Matrix (Fin 4) (Fin 4) ℂ => M β γ) h1; simp only [C, D, sE0, mul_apply, transpose_apply,
        of_apply, one_apply, mul_ite, mul_zero] at h ⊢; fin_cases β <;> fin_cases γ <;> simp at h ⊢
        <;> (try exact h) <;> linear_combination (3 : ℂ)⁻¹ * h); have hcs (b) : ∑ a, c a b = if b =
      0 then 2 else 0 := (by
      have h := hco 0 b; simp_rw [hc0, ← mul_sum, sE0] at h; exact mul_left_cancel₀
        (by norm_num : (2 : ℂ)⁻¹ ≠ 0) (h.trans (by by_cases hb : b = 0 <;> simp [hb, eq_comm])));
      have hsum_ρ : ∑ a, ρ a = (2 : ℂ) • (1 : QubitMatrix) := (by
      simp_rw [hρ_e]; rw [sum_comm, show (∑ b : Fin 4, ∑ a, c a b • pauli1 b) = ∑ b, (∑ a, c a b) •
        pauli1 b from sum_congr rfl fun _ _ => sum_smul.symm]; simp_rw [hcs]; simp [ite_smul,
        pauli1]); have hdes (X Y) : ∑ a, trace (ρ a * X) * trace (ρ a * Y) = (2 / 3 : ℂ) * (trace (X
      * Y) + trace X * trace Y) := (by
      have htrM (a M) : trace (ρ a * M) = ∑ b, trace (M * pauli1 b) * c a b := (by
        rw [hρ_e a]; simp only [Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul,
          smul_eq_mul]; exact sum_congr rfl fun b _ => (by
          rw [trace_mul_comm (pauli1 b) M, mul_comm])); refine Eq.trans (b := ∑ β, ∑ γ, trace (X *
        pauli1 β) * trace (Y * pauli1 γ) * ∑ a, c a β * c a γ) (by
        simp_rw [htrM, sum_mul, mul_sum]; rw [sum_comm]; exact sum_congr rfl fun _ _ =>
          (by rw [sum_comm]; exact sc2 fun _ _ => (by ring))) (by
        simp_rw [hco]; simp [sE0, Fin.sum_univ_four, Fin.sum_univ_two, trace, Matrix.diag,
          mul_apply, pauli1, qubitX, qubitZ]; ring_nf; simp [Complex.I_sq]; ring)); obtain ⟨ψ, hψ,
      hρψ⟩ := (isQubitSICProjector_iff_exists_unitVectorQubitSIC ρ).mp hρ; have hsicE (β γ) : sicE ρ
      β γ = sE0 β γ := (by
      unfold sicE; rw [← hco β γ]; have hfac a : trace (ρ a * pauli1 β * ρ a * pauli1 γ) =
        4 * (c a β * c a γ) := (by
        obtain ⟨_, hm, he⟩ := pure_state_handshake (ψ a) (hψ.1 a) (pauli1 β); rw [hρψ a, hm,
          Matrix.smul_mul, trace_smul, smul_eq_mul, he, ← hρψ a, trace_mul_comm (pauli1 β)]
        dsimp [c]; ring); simp_rw [hfac, ← mul_sum]; ring)
    have hsicA (β γ) : sicAlpha ρ β γ = sA0 β γ := (by
      unfold sicAlpha; simp_rw [show ∀ a b, sicMatrixA a b = (4 : ℂ)⁻¹ - if a = b then (2 : ℂ)⁻¹
        else 0 from fun a b => (by unfold sicMatrixA; split_ifs <;> norm_num), sub_mul,
        sum_sub_distrib, mul_sub]; refine Eq.trans (b := (16 : ℂ)⁻¹ * trace ((∑ b, ρ b) * pauli1 β *
        (∑ a, ρ a) * pauli1 γ) - (2 : ℂ)⁻¹ * sicE ρ β γ) (congrArg₂ (· - ·) (by
        simp only [Matrix.sum_mul, trace_sum, mul_sum]; exact sc2 fun _ _ => (by ring))
        (by unfold sicE; simp [ite_mul, mul_sum, mul_left_comm])) (by
        rw [hsum_ρ, hsicE]; fin_cases β <;> fin_cases γ <;> simp [sE0, sA0, p1_tr] <;> norm_num));
      exact ⟨hsum_ρ, hdes, hsicE, hsicA⟩); have hpst (ρ T β γ) : ((4 : ℂ) ^ n)⁻¹ * ∑ a, ∑ b,
    sicSubsetKernel n T a b * trace (productSIC ρ b * pN n β * productSIC ρ a * pN n γ) = ∏ i, if i
    ∈ T then sicAlpha (ρ i) (β i) (γ i) else sicE (ρ i) (β i) (γ i) := (by
    have htr (a b) : trace (productSIC ρ b * pN n β * productSIC ρ a * pN n γ) = ∏ i, trace (ρ i (b
      i) * pauli1 (β i) * ρ i (a i) * pauli1 (γ i)) := (by
      change trace (pM (fun i => ρ i (b i)) * pM (fun i => pauli1 (β i)) * pM (fun i => ρ i (a i)) *
        pM (fun i => pauli1 (γ i))) = _; rw [pM_mul, pM_mul, pM_mul, pM_tr]); have hi (i) : (if i ∈
      T then sicAlpha (ρ i) (β i) (γ i) else sicE (ρ i) (β i) (γ i)) = (4 : ℂ)⁻¹ * ∑ u : Fin 4, ∑ v
      : Fin 4, (if i ∈ T then sicMatrixA u v else (1 : Matrix (Fin 4) (Fin 4) ℂ) u v) * trace (ρ i v
      * pauli1 (β i) * ρ i u * pauli1 (γ i)) := (by
        by_cases h : i ∈ T <;> simp [h, sicAlpha, sicE, one_apply, ite_mul]); symm;
      simp_rw [hi, prod_mul_distrib, prod_const, card_fin, inv_pow]; congr 1; rw [Fintype.prod_sum];
      refine sum_congr rfl fun a _ => ?_; rw [Fintype.prod_sum]; refine sum_congr rfl fun b _ => ?_;
      rw [prod_mul_distrib, htr]; rfl); have hkft (ρ)
    (hρ : ∀ i, IsQubitSICProjector (ρ i)) (k Λ) : kFidelity ρ k Λ = ∑ β, pTW Λ β * ∑ T ∈
      @Finset.filter _ (fun T : Finset (Fin n) => T.card ≤ k) (Classical.decPred _) univ, (-1 : ℂ) ^
      T.card * (∏ i ∈ T, sicAlpha (ρ i) (β i) (β i)) * (∏ i ∈ Tᶜ, sicE (ρ i) (β i) (β i)) := (by
    symm; simp_rw [mul_sum]; rw [sum_comm]; symm; unfold kFidelity; rw [mul_sum]; refine sum_congr
      (by ext; simp) fun T _ => ?_; simp_rw [(hpm Λ).1 (productSIC ρ _), Matrix.mul_sum,
      Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul]; refine Eq.trans (b := ∑ β, ∑ γ, pMx Λ β
      γ * (-1 : ℂ) ^ T.card * (((4 : ℂ) ^ n)⁻¹ * ∑ a, ∑ b, sicSubsetKernel n T a b * trace
      (productSIC ρ b * pN n β * productSIC ρ a * pN n γ))) (by
        simp_rw [mul_sum]; rw [scomm22]; exact sc4 fun _ _ _ _ =>
          (by simp only [Matrix.mul_assoc]; ring)) (by
      simp_rw [hpst]; exact sum_congr rfl fun β _ => (by
        rw [fss β fun γ hγ => (by
          obtain ⟨i, hi⟩ := Function.ne_iff.mp (Ne.symm hγ); rw [prod_eq_zero (mem_univ i) (by
            obtain ⟨_, _, hE, hA⟩ := hs1 (hρ i); by_cases hiT : i ∈ T <;> simp [hiT, hE, hA, sE0,
              sA0, hi]), mul_zero]), p_split]; dsimp [pTW, pauliTwirlWeight]; ring))); refine ⟨(by
    constructor <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [sicOverlapB, sicMatrixA,
      mul_apply, Fin.sum_univ_four] <;> norm_num), (by
    intro a; fin_cases a <;> simp [sicOverlapB, mul_apply, Fin.sum_univ_four] <;> norm_num), (by
    intro a b; refine ⟨(by
      simp_rw [show ∀ i, (1 - sicMatrixA) (a i) (b i) = (1 : Matrix _ _ ℂ) (a i) (b i) + (-1 : ℂ) *
        sicMatrixA (a i) (b i) from fun i => (by simp; ring)]; rw [prod_add, show (univ : Finset
        (Fin n)).powerset = univ from (by ext; simp)]; let e : Equiv.Perm (Finset (Fin n)) := ⟨(·ᶜ),
        (·ᶜ), compl_compl, compl_compl⟩; rw [← Equiv.sum_comp e]; exact sum_congr rfl fun T _ => (by
        dsimp [e]; simp only [← compl_eq_univ_sdiff, compl_compl]; rw [prod_mul_distrib, prod_const,
          ← mul_left_comm]; congr 1; unfold sicSubsetKernel; rw [p_split, mul_comm])), (by
      let D := univ.filter (fun i => a i ≠ b i); let S := univ.filter (fun i => ¬ a i ≠ b i); have
        hDS : D.card + S.card = n :=
        (by simpa [D, S] using card_filter_add_card_filter_not (s := univ) (fun i => a i ≠ b i)); rw
        [← prod_filter_mul_prod_filter_not univ (fun i => a i ≠ b i), prod_congr (s₁ := D) rfl fun i
        hi => show _ = (-1 : ℂ) / 4 from (by simp [sicMatrixA, (mem_filter.mp hi).2]; ring),
        prod_congr (s₁ := S) rfl fun i hi => show _ = (5 : ℂ) / 4 from
        (by simp [sicMatrixA, Classical.not_not.mp (mem_filter.mp hi).2]; norm_num), prod_const,
        prod_const, show S.card = n - D.card from (by omega), div_pow, div_pow, div_mul_div_comm, ←
        pow_add, Nat.add_sub_of_le (by omega)])⟩), fun ρ₀ hρ₀ => ⟨(by
    intro x₁ x₂ y₁ y₂; have h := (hs1 hρ₀).2.1 (single y₁ x₁ 1) (single y₂ x₂ 1); have htr (M :
      QubitMatrix) (x y) : trace (M * single y x 1) = M x y := (by
      fin_cases x <;> fin_cases y <;> simp [trace, Matrix.diag, Fin.sum_univ_two])
    simp_rw [htr] at h; rw [h]; congr 1; fin_cases x₁ <;> fin_cases x₂ <;> fin_cases y₁ <;>
      fin_cases y₂ <;> simp [trace, Matrix.diag, single_apply]), hs1 hρ₀⟩, hpst, (by
    intro ρ hρ k Λ; refine ⟨hkft ρ hρ k Λ, ?_⟩; rw [hkft ρ hρ k Λ, hkft ρ hρ k (complexPauliTwirl
      Λ)]; exact sum_congr rfl fun β _ => congrArg (· * _) (by
      simpa [pTW, pauliTwirlWeight] using (hpm (complexPauliTwirl Λ)).2 (fun b g => if b = g then
        pTW Λ b else 0) (fun _ => (by change (∑ b, _ • _) = _; simp [ite_smul])) β β)), (by
    intro ρ₁ ρ₂ hρ₁ hρ₂ k Λ; have hA (i b) : sicAlpha (ρ₁ i) b b = sicAlpha (ρ₂ i) b b :=
      (by rw [(hs1 (hρ₁ i)).2.2.2, (hs1 (hρ₂ i)).2.2.2]); have hE (i b) : sicE (ρ₁ i) b b = sicE (ρ₂
      i) b b := (by rw [(hs1 (hρ₁ i)).2.2.1, (hs1 (hρ₂ i)).2.2.1]); rw [hkft ρ₁ hρ₁ k Λ, hkft ρ₂ hρ₂
      k Λ]; simp_rw [hA, hE])⟩)
theorem kFidelity_eq_pauliWeight_alternating_sum (n k : ℕ) (ρ : Fin n → Fin 4 → QubitMatrix) (hρ : ∀
  i : Fin n, IsQubitSICProjector (ρ i)) (Λ : QubitMap n) : kFidelity ρ k Λ = pauliWeightSum Λ 0 +
  (-1 : ℂ) ^ k * ∑ w ∈ Finset.Icc 1 n, ((3 : ℂ)⁻¹ ^ w * (Nat.choose (w - 1) k : ℂ)) * pauliWeightSum
  Λ w ∧ (n ≤ k → kFidelity ρ k Λ = processFidelity Λ) ∧ kFidelity ρ 0 Λ = ∑ β : PauliLabel n, (3 :
  ℂ)⁻¹ ^ hammingWeight β * pauliTwirlWeight Λ β ∧ (Λ.IsCompletelyPositive → ((realKFidelity ρ k Λ :
  ℝ) : ℂ) = kFidelity ρ k Λ ∧ realKFidelity ρ k Λ = realWeightSum Λ 0 + (-1 : ℝ) ^ k * ∑ w ∈
  Finset.Icc 1 n, ((3 : ℝ)⁻¹ ^ w * (Nat.choose (w - 1) k : ℝ)) * realWeightSum Λ w) := (by
  have hqs := qubit_sic_matrices_and_per_qubit_traces n; have halt {w} (hw : 1 ≤ w) (m) : ∑ j ∈
    range (m + 1), (-1 : ℂ) ^ j * (w.choose j : ℂ) = (-1 : ℂ) ^ m * ((w - 1).choose m : ℂ) := (by
    obtain ⟨r, rfl⟩ : ∃ r, w = r + 1 := ⟨w - 1, (Nat.sub_add_cancel hw).symm⟩; simp only
      [Nat.add_sub_cancel]; exact Nat.rec (by simp) (fun m ih => (by
      rw [sum_range_succ, ih, Nat.choose_succ_succ r m]; push_cast; rw [pow_succ]; ring)) m); have
    hlbl (k' β) : ∑ T ∈ @Finset.filter _ (fun T : Finset (Fin n) => T.card ≤ k')
    (Classical.decPred _) univ, (-1 : ℂ) ^ T.card * (∏ i ∈ T, sicAlpha (ρ i) (β i) (β i)) *
    (∏ i ∈ Tᶜ, sicE (ρ i) (β i) (β i)) = (3 : ℂ)⁻¹ ^ hWt β * ∑ j ∈ range (k' + 1), (-1 : ℂ) ^ j *
    ((hWt β).choose j : ℂ) := (by
    let W := univ.filter (fun i : Fin n => β i ≠ 0); have hAv (i) : sicAlpha (ρ i) (β i) (β i) = if
      β i = 0 then 0 else (3 : ℂ)⁻¹ := (by
      simpa using (hqs.2.2.2.1 (ρ i) (hρ i)).2.2.2.2 (β i) (β i)); have hEv (i) : sicE (ρ i) (β i)
      (β i) = if β i = 0 then 1 else (3 : ℂ)⁻¹ := (by
      simpa using (hqs.2.2.2.1 (ρ i) (hρ i)).2.2.2.1 (β i) (β i)); have hprod (T) : (∏ i ∈ T, if β i
      = 0 then (0 : ℂ) else (3 : ℂ)⁻¹) * (∏ i ∈ Tᶜ, if β i = 0 then (1 : ℂ) else (3 : ℂ)⁻¹) = if T
      ⊆ W then (3 : ℂ)⁻¹ ^ W.card else 0 := (by
      rw [← p_split, ← prod_filter_mul_prod_filter_not univ (fun i => β i ≠ 0), prod_congr rfl fun i
        hi => show _ = (3 : ℂ)⁻¹ from (by by_cases hiT : i ∈ T <;> simp [hiT, (mem_filter.mp
          hi).2]), prod_const]; by_cases hTW : T ⊆ W <;> simp only [hTW, ↓reduceIte]
      · rw [prod_eq_one fun i hi => (by
          have h0 := Classical.not_not.mp (mem_filter.mp hi).2
          have hnT : i ∉ T := fun hT => (mem_filter.mp (hTW hT)).2 h0; simp [h0, hnT]), mul_one]
      · obtain ⟨i, hiT, hiW⟩ := not_subset.mp hTW; have h0 : β i = 0 := (by simpa [W] using hiW)
        rw [prod_eq_zero (mem_filter.mpr ⟨mem_univ i, Classical.not_not.mpr h0⟩)
          (by simp [h0, hiT]), mul_zero])
    let P := W.powerset.filter (fun T => T.card ≤ k'); simp_rw [hAv, hEv, mul_assoc, hprod, mul_ite,
      mul_zero, ← sum_filter]; rw [show (@Finset.filter _ (fun T : Finset (Fin n) =>
      T.card ≤ k') (Classical.decPred _) univ).filter (· ⊆ W) = P from
      (by ext T; simp [P, mem_powerset, and_comm]), ← sum_fiberwise_of_maps_to (fun T hT =>
      mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hT).2)), mul_sum]; exact sum_congr rfl fun j
      hj => (by
      rw [show P.filter (fun T => T.card = j) = powersetCard j W from (by
        ext T; simp only [P, mem_filter, mem_powerset, mem_powersetCard]; have := mem_range.mp hj
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, (by omega)⟩, h2⟩⟩), sum_congr
        rfl (g := fun _ => (-1 : ℂ) ^ j * (3 : ℂ)⁻¹ ^ W.card) (fun T hT => (by
        rw [(mem_powersetCard.mp hT).2])), sum_const, card_powersetCard, nsmul_eq_mul]
      dsimp [W, hWt, hammingWeight]; ring))
  have hmain : kFidelity ρ k Λ = pWS Λ 0 + (-1 : ℂ) ^ k * ∑ w ∈ Icc 1 n,
      ((3 : ℂ)⁻¹ ^ w * ((w - 1).choose k : ℂ)) * pWS Λ w := (by
    rw [(hqs.2.2.2.2.2.1 ρ hρ k Λ).1]; simp_rw [hlbl k]; rw [s_hw (fun w => (3 : ℂ)⁻¹ ^ w *
      ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j * (w.choose j : ℂ)) (pTW Λ)]
    change ∑ w ∈ range (n + 1), _ * pWS Λ w = _; rw [show range (n + 1) = insert 0 (Icc 1 n) from
      (by ext w; simp only [mem_range, mem_insert, mem_Icc]; omega), sum_insert (by simp)]; congr 1
    · rw [sum_eq_single 0 (fun j _ hj => by cases j; contradiction; simp) (by simp)]; simp
    · rw [mul_sum]; exact sum_congr rfl fun w hw => (by rw [halt (mem_Icc.mp hw).1 k]; ring))
  refine ⟨hmain, fun hnk => (by
    rw [hmain, sum_eq_zero fun w hw => (by
      simp [Nat.choose_eq_zero_of_lt (by have := mem_Icc.mp hw; omega : w - 1 < k)]),
      mul_zero, add_zero]; have h0 := (pauli_process_matrix_and_fidelity_characterization n).2.1 Λ
    exact h0.2.1.trans h0.1.symm), (by
    rw [(hqs.2.2.2.2.2.1 ρ hρ 0 Λ).1]; exact sum_congr rfl fun β _ => (by
      rw [hlbl 0 β]; simp [mul_comm])), fun hCP => (by
    have hcpw := ((pauli_process_matrix_and_fidelity_characterization n).2.2.2.1 Λ hCP).2.1
    have hrv : kFidelity ρ k Λ = ((rWS Λ 0 + (-1 : ℝ) ^ k * ∑ w ∈ Icc 1 n, ((3 : ℝ)⁻¹ ^ w *
      ((w - 1).choose k : ℝ)) * rWS Λ w : ℝ) : ℂ) := (by
      rw [hmain]; push_cast; exact congrArg₂ (· + ·) (hcpw 0).1.symm
        (congrArg (_ * ·) (sum_congr rfl fun w _ => by rw [(hcpw w).1])))
    unfold realKFidelity; rw [hrv, ofReal_re]; exact ⟨rfl, rfl⟩)⟩)
theorem cp_kFidelity_alternating_truncation_bound (n k : ℕ) (ρ : Fin n → Fin 4 → QubitMatrix) (hρ :
  ∀ i : Fin n, IsQubitSICProjector (ρ i)) (Λ : QubitMap n) (hCP : Λ.IsCompletelyPositive) : (-1 : ℝ)
  ^ k * (realKFidelity ρ k Λ - realProcessFidelity Λ) = ∑ w ∈ Finset.Icc (k + 1) n, ((3 : ℝ)⁻¹ ^ w *
  (Nat.choose (w - 1) k : ℝ)) * realWeightSum Λ w ∧ 0 ≤ ∑ w ∈ Finset.Icc (k + 1) n, ((3 : ℝ)⁻¹ ^ w *
  (Nat.choose (w - 1) k : ℝ)) * realWeightSum Λ w ∧ (Odd k → realKFidelity ρ k Λ ≤
  realProcessFidelity Λ) ∧ (Even k → realProcessFidelity Λ ≤ realKFidelity ρ k Λ) ∧ (∀ i j : ℕ, Odd
  j → Even i → realKFidelity ρ j Λ ≤ realKFidelity ρ i Λ) ∧ ((realKFidelity ρ k Λ =
  realProcessFidelity Λ ↔ ∀ w ∈ Icc (k + 1) n, realWeightSum Λ w = 0) ∧ (realKFidelity ρ k Λ =
  realProcessFidelity Λ ↔ ∀ β : PauliLabel n, k < hammingWeight β → realTwirlWeight Λ β = 0)) := by
  let S (m) := ∑ w ∈ Icc (m + 1) n, ((3 : ℝ)⁻¹ ^ w * ((w - 1).choose m : ℝ)) * rWS Λ w; have hch :=
    pauli_process_matrix_and_fidelity_characterization n; have hcpw := (hch.2.2.2.1 Λ hCP).2.1; have
    hQ0 : realWeightSum Λ 0 = realProcessFidelity Λ := ofReal_inj.mp (by
    rw [(hcpw 0).1, (hch.2.2.2.1 Λ hCP).2.2, (hch.2.1 Λ).2.1, (hch.2.1 Λ).1]); have herr (m) : (-1 :
    ℝ) ^ m * (realKFidelity ρ m Λ - realProcessFidelity Λ) = S m := (by
    dsimp [S]; rw [((kFidelity_eq_pauliWeight_alternating_sum n m ρ hρ Λ).2.2.2 hCP).2, hQ0,
      add_sub_cancel_left, ← mul_assoc, ← mul_pow, show (-1 : ℝ) * (-1 : ℝ) = 1 from (by norm_num),
      one_pow, one_mul]; exact (sum_subset (Icc_subset_Icc_left (by omega)) fun w hw hnot => (by
      simp [Nat.choose_eq_zero_of_lt (by simp only [mem_Icc] at hw hnot; omega : w - 1 < m)])).symm)
  have hnn (m) : 0 ≤ S m := sum_nonneg fun w _ => mul_nonneg (by positivity) (hcpw w).2
  have hodd (m) (hm : Odd m) : realKFidelity ρ m Λ ≤ realProcessFidelity Λ := (by
    have h := herr m; rw [hm.neg_one_pow] at h; linarith [hnn m])
  have hevn (m) (hm : Even m) : realProcessFidelity Λ ≤ realKFidelity ρ m Λ := (by
    have h := herr m; rw [hm.neg_one_pow] at h; linarith [hnn m])
  refine ⟨herr k, hnn k, hodd k, hevn k, fun i j hj hi => le_trans (hodd j hj) (hevn i hi), ?_⟩
  have heq : realKFidelity ρ k Λ = realProcessFidelity Λ ↔ S k = 0 := (by
    rw [← herr k, mul_eq_zero, or_iff_right (pow_ne_zero k (by norm_num)), sub_eq_zero])
  have hs0 : S k = 0 ↔ ∀ w ∈ Icc (k + 1) n, rWS Λ w = 0 := (by
    dsimp [S]; rw [sum_eq_zero_iff_of_nonneg (fun w _ => mul_nonneg (by positivity) (hcpw w).2)]
    exact forall₂_congr fun w hw => mul_eq_zero.trans (or_iff_right (ne_of_gt (mul_pos
      (by positivity) (by exact_mod_cast Nat.choose_pos (by have := mem_Icc.mp hw; omega))))))
  have hwβ : (∀ w ∈ Icc (k + 1) n, rWS Λ w = 0) ↔ ∀ β : PauliLabel n, k < hWt β →
      realTwirlWeight Λ β = 0 := (by
    have hws w : rWS Λ w = ∑ β ∈ univ.filter (fun β : PauliLabel n => hWt β = w),
      realTwirlWeight Λ β := (by simp [rWS, realWeightSum, pauliWeightSum, realTwirlWeight, hWt])
    refine ⟨fun hall β hβ => (by
      have hz := hall (hWt β) (mem_Icc.mpr ⟨hβ, le_trans (card_filter_le _ _) (by simp)⟩)
      rw [hws] at hz; exact (sum_eq_zero_iff_of_nonneg (fun γ _ =>
        ((hch.2.2.2.1 Λ hCP).1 γ).2)).mp hz β (by simp)), fun hall w hw => (by
      rw [hws]; exact sum_eq_zero fun β hβ => hall β ((mem_filter.mp hβ).2.symm ▸
        (mem_Icc.mp hw).1))⟩); exact ⟨heq.trans hs0, (heq.trans hs0).trans hwβ⟩
end D5.S3.Quantum.QuantumChannels.SicKFidelity.SicKFidelityPauliWeight
