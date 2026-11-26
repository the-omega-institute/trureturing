/- GID: D5/S3/Zeros/GRH/New/Seesaw/NamesAtSplitLevel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/NamesAtSplitLevel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.NamesAtSplitLevel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/NamesAtSplitLevel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Lift.Staircase
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: dictionaries between two encodings of the same objects.

Part of: Trading denominators at the level prime for a column operator (see
New.Columns.TwistedHeckeType).

This file: Abstract lift laws mod N; Gauss-sum Hecke operator slides through a chain of lifts.
Jointly invariant chain of lifts is a plain sum over tuples of classes. Translates with denominator
N on a pair rewritten as named data modulo N. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section

section


open Matrix Finset Function MulAction GeneralLinearGroup SemilocalField Valued WithZero MatMul Fint
  Ring
variable {E n n' : Type} [Field E] [CMType E] [WeilData E] {P S :
  Finset (FinPlace E)} {N : ℕ} [Fact N.Prime] [Fintype n] [Fintype n'] (y : P → ZMod N)

/-- P is disjoint from its conjugate, each w in P has norm N and uniformiser N, and the places
dividing N are exactly those of P ∪ P̄. -/
class IsSplitLevel (P : Finset (FinPlace E)) (N : outParam ℕ) where
  star_notMem : ∀ w ∈ P, star w ∉ P
  q_eq : ∀ w ∈ P, w.q = N
  protected v_natCast : ∀ w ∈ P, v (N : LocField w) = exp (-1)
  natCast_mem_iff w : ↑N ∈ w.1 ↔ w ∈ P ∨ star w ∈ P

/-- For y in (ℤ/N)^P, the finite adele with component ỹ_w/N at w in P, ỹ_w the least
non-negative representative, and 0 at the other places. -/
def residueOverN {E : Type} [Field E] [NumberField E] {P : Finset (FinPlace E)} {N : ℕ}
    (y : P → ZMod N) := adeleOfLocal P fun w ↦ (y w).val / N

omit [WeilData E] [Fact N.Prime] in
@[simp] lemma residueOverN_apply w : residueOverN y w = if h : w ∈ P then ((y ⟨w, h⟩).val / N :
  LocField w) else 0 := rfl

omit [WeilData E] in
lemma idem_mul_residueOverN : idem P * residueOverN y = residueOverN y := by aesop

namespace IsSplitLevel

variable (n S) in
/-- The element of GL_{n+1}(∏_{w∈P} E_w) equal to diag(1, …, 1, N) at the places of P lying in S
and to the identity at the others. -/
def diagN [Λ : IsSplitLevel P N] : GL (n ⊕ Unit) (LocProd P) :=
  diagGL (ite ·.isLeft 1 (MulEquiv.piUnits.symm fun w ↦ ite (↑w ∈ S) (.mk0 N NeZero.out) 1))

variable [Λ : IsSplitLevel P N] (π : Rep ℂ (GL (n ⊕ Unit) (LocProd P))) (π' :
  Rep ℂ (GL (n' ⊕ Unit) (LocProd P)))

/-- For w in P, a ring isomorphism from the residue field of E_w, which has prime order N, to
ℤ/N. -/
def residueEquiv (w : P) :=
  (ZMod.ringEquivOfPrime (ResField w.1) ‹Fact _›.1 (by simp [← card_ResField, ← Λ.q_eq w])).symm

/-- The ring homomorphism from the integral elements of ∏_{w∈P} E_w to (Z/N)^P reducing each
component to its residue field, identified with Z/N. -/
def reduction := RingHom.pi fun w ↦ (Λ.residueEquiv w).toRingHom.comp (residueAt w)

omit [WeilData E] in
lemma reduction_eq_iff {x c} : Λ.reduction x = c ↔ ∀ w, v ((x.1 w - (c w).val) /
  N) ≤ 1 := by simpa [funext_iff, reduction, Λ.v_natCast, div_le_iff₀, ← exp_add,
  ← lt_mul_exp_iff_le, ↓ZMod.natCast_zmod_val, -ZMod.natCast_val] using (forall_congr' fun w ↦
  (residueEquiv w).map_eq_zero_iff.trans (residueAt_eq_zero w (u := x - (c w).val)))

instance : IsLocalHom Λ.reduction := ⟨by simp [reduction, Pi.isUnit_iff]⟩

/-- The inclusion of GL_n(O) in GL_n(∏_{w∈P} E_w), with O the ring of integral elements. -/
abbrev inclGL {E n : Type} [Field E] [NumberField E] {P : Finset (FinPlace E)} [Fintype n] :=
  map (n := n) (O (F := LocProd P)).subtype

/-- Entrywise reduction modulo N: the homomorphism from GL_n(O) to GL_n((ℤ/N)^P), with O the
ring of integral elements of ∏_{w∈P} E_w. -/
abbrev reductionGL := map (n := n) Λ.reduction

/-- A chosen set-theoretic section of the reduction map GL_n(O) → GL_n((ℤ/N)^P). -/
abbrev liftGL := surjInv (GL_map_surjective (n := n) Λ.reduction fun y ↦ ⟨⟨(y · |>.val),
  fun _ _ ↦ _root_.natCast_mem ..⟩, by simp [reduction_eq_iff]⟩)

attribute [-simp] Subtype.forall Subtype.exists

/-- The invertible matrix u₀ of rank n + 1 over ∏_{w∈P} E_w that is diag(1, …, 1, N⁻¹) at every
place of P. -/
abbrev diagNInv := (Λ.diagN n P)⁻¹

/-- The value ψ_f(−ȷαᾱ y/N) for y in (ℤ/N)^P, with y/N the finite adele `residueOverN` y supported
on P. -/
def psiN := stdLattice.psi₀ E (-residueOverN y)

/-- The last standard basis vector (0, …, 0, 1) of length n + 1 over the ring (ℤ/N)^P. -/
abbrev lastBasisVector : n ⊕ Unit → P → ZMod N := Pi.single (.inr ()) 1

/-- Over a commutative ring R, every vector y of length n + 1 whose last entry is a unit is both
the last column and the last row of some k(y) in GL_{n+1}(R). -/
lemma exists_GL_last_col_and_row {R} [CommRing R] : ∃ k : _ → GL (n ⊕ _) R, ∀ y,
  IsUnit (y (.inr ())) → (k y).1.col (.inr
  ()) = y ∧ (k y).1.row (.inr ()) = y := ⟨fun y ↦ let C := updateCol 1 (.inr ()) y
  if h : IsUnit (y (.inr ())) then mk'' (h.unit⁻¹ • C * Cᵀ) (by simpa [C, ← cramer_apply]) else 1,
    by simp_all [funext_iff, mul_apply, ↓inv_smul_eq_iff, mul_comm]⟩

/-- The operator π(u₀) ∑_y `IsSplitLevel.psiN`(y_last) π(κ_y), over y mod N with unit last entry,
κ_y a chosen integral invertible matrix with last row and last column ≡ y. -/
def fourierOp := π.ρ diagNInv * ∑ y with IsUnit (y (.inr ())),
  psiN (y (.inr ())) • π.ρ (inclGL (liftGL (exists_GL_last_col_and_row.choose y)))

/-- The group of integral invertible matrices over ∏_{w∈P} E_w whose last column is congruent to
e₁ = (0, …, 0, 1) modulo N. -/
def mirabolic := ((stabilizer (GL (n ⊕ Unit) _) (lastBasisVector : n ⊕ _ → P → ZMod N)).comap
  Λ.reductionGL).map inclGL

/-- Ramified vectors: the φ lying, for each w ∈ P, in the image of 1 − π(x) for some integral
unit scalar x ≡ 1 mod N at the other places of P. -/
def ramified :=
  {φ | ∀ w, ∃ x : Oˣ, (∀ v ≠ w, Λ.reduction x v = 1) ∧ φ ∈ (1 - π.ρ (inclGL (scalar _ x))).range}

/-- The linear map sending a function f on matrices over (ℤ/N)^P to the function equal to f(S
mod N) on integral matrices S over ∏_{w∈P} E_w and 0 elsewhere. -/
@[simps! -isSimp] abbrev liftFn := liftIntegralFn (m := n') (n := n) Λ.reduction

seal liftIntegralFn

/-- The indicator function, on matrices S over ∏_{w∈P} E_w, of those S that are integral with
last row congruent to the last basis vector modulo N. -/
def lastRowDatum :=
  Λ.liftFn (n' := n' ⊕ _) (if · (.inr ()) = lastBasisVector (n := n) then 1 else 0)

/-- The indicator function, on matrices S over ∏_{w∈P} E_w, of those S that are integral with
last column congruent to y modulo N. -/
def lastColDatum y := Λ.liftFn fun T : Matrix n' (n ⊕ _) _ ↦ ite (Tᵀ (.inr ()) = y) 1 0

/-- The function on matrices S over ∏_{w∈P} E_w equal to `IsSplitLevel.psiN`(r·y) for integral S
with last row r modulo N, and to 0 for non-integral S. -/
def charDatum y := Λ.liftFn (n := n) (n' := n' ⊕ _) (psiN <| · (.inr ()) ⬝ᵥ y)

/-- Two rules for L: π'(b)L[f(b̄ · ā)]π(a) = L[f] for integral invertible a, b and functions f
of residues, and π'(u₀)L[𝐞] = γL[𝐛]π(u₀), 𝐞 = `IsSplitLevel.lastRowDatum`, 𝐛 =
`IsSplitLevel.lastColDatum` e₁. -/
structure LiftLaw (L :
  (Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P) → ℂ) →ₗ[ℂ] π →ₗ[ℂ] π') (γ : ℂ) where
  integral_equivariant a b f φ : π'.ρ (inclGL b) (L (liftFn (f <|
    (reductionGL b).1 * · * (reductionGL a).1)) (π.ρ (inclGL a) φ)) = L (liftFn f) φ
  diagNInv_law φ : π'.ρ diagNInv (L lastRowDatum φ) =
    γ • L (lastColDatum lastBasisVector) (π.ρ diagNInv φ)

variable {π} {π'} {φ : ↑π} {L : (Matrix (n' ⊕ Unit) (n ⊕ Unit) (LocProd P) → ℂ) →ₗ[ℂ] ↑π →ₗ[ℂ] ↑π'}
  {γ : ℂ} (H : LiftLaw π π' L γ)

attribute [local simp] Units.smul_def smul_smul lastColDatum lastRowDatum fourierOp liftFn_apply
  mulVec_apply_eq_sum mul_apply_eq_vecMul

section

omit [WeilData E]

/-- For u₀ = diag(1, …, 1, N⁻¹): u₀⁻¹Su₀ is integral with last row ≡ e₁ mod N exactly when S is
integral with last column ≡ e₁ mod N; that is, 𝐞(u₀⁻¹Su₀) = 𝐛(S) for the two indicator
functions. -/
lemma lastRowDatum_conj_u₀ (S : Matrix (n' ⊕ _) (n ⊕ _) (LocProd P)) : lastRowDatum
  ((Λ.diagNInv (n := n'))⁻¹.1 * S * Λ.diagNInv (n := n).1) = lastColDatum lastBasisVector S := by
  simp [diagNInv, diagN, ← map_inv, reduction_eq_iff, @funext_iff (_ ⊕ _), ↓mem_O_locProd,
    Λ.v_natCast, field, mul_left_comm, -WithZero.exp_neg]
  grind [mul_le_one', show exp (-1) ≤ 1 by tauto]

lemma exists_inclGL_eq {f} {g : GL n (LocProd P)} (a : Λ.liftFn f g ≠ 0) (b : liftFn f ↑g⁻¹ ≠ 0) :
    ∃ k, f (reductionGL k).1 ≠ 0 ∧ inclGL k = g := (mem_intGL.2 (by aesop) : g ∈ _).imp (by aesop)

lemma lastColDatum_ne_zero {g} : g ∈ Λ.mirabolic (n := n) → lastColDatum lastBasisVector g.1 ≠ 0 :=
  (·.rec (by aesop))

end

/-- Let g lie in `IsSplitLevel.mirabolic` and let T be a linear endomorphism of π with π(a)Tπ(b)φ =
φ whenever agb lies in `IsSplitLevel.mirabolic`. Then T fixes 𝖥φ, for 𝖥 = `IsSplitLevel.fourierOp`
(Fourier transform followed by u₀). -/
lemma mirabolic_fix_fourierOp (T : π →ₗ[ℂ] π) {g} (G : g ∈ mirabolic) (h : ∀ a b,
  a * g * b ∈ mirabolic → π.ρ a (T (π.ρ b φ)) = φ) : T (fourierOp π φ) = fourierOp π φ := by
  have ⟨k, c, r⟩ := exists_inclGL_eq (g :=
    _ * g * _) ((lastRowDatum_conj_u₀ _).trans_ne (lastColDatum_ne_zero G))
    (by simpa using (lastRowDatum_conj_u₀ _).trans_ne (lastColDatum_ne_zero (inv_mem G)))
  simp [← map_mul, mul_sum, @funext_iff (_ ⊕ _)] at *
  use sum_equiv (toPerm (reductionGL k)) (by simp [c]) fun y a ↦ congrArg₂ _ (by simp [c])
    (π.ρ.inv_apply_eq_iff.1 (h _ _ ⟨(liftGL (exists_GL_last_col_and_row.choose
    (reductionGL k • y)))⁻¹ * k * liftGL (exists_GL_last_col_and_row.choose y), by
    simp [inv_smul_eq_iff, -Units.smul_def, surjInv_eq,
      ← smul_smul]; simp_all [exists_GL_last_col_and_row.choose_spec], by simp [r, mul_assoc]⟩))

omit [WeilData E] in
lemma liftFn_comp_eq_sum_smul {ι} [Fintype ι] (r : _ → ι) (g : ι → ℂ) :
    L (liftFn (g <| r ·)) φ = ∑ y, g y • L (liftFn fun T ↦ ite (r T = y) 1 0) φ := by
  simpa [@eq_comm ι] using! (L.flip φ ∘ₗ liftFn ∘ₗ .funLeft ..).pi_apply_eq_sum_univ g

include H

omit [WeilData E] in
lemma LiftLaw.eq_zero_of_smul_invariant (h : φ ∈ ramified π) w {f} (a : ∀ c : P → ZMod N,
  (∀ t y, y w = 0 →
  (c * t = y ↔ t = y)) → ∀ T, f (c • T) = f T) : L (liftFn f) φ = 0 := have ⟨x, e, ψ, b⟩ := h w
  by simp [← b, ← smul_eq_mul_diagonal, ← H.integral_equivariant (scalar _ x) 1 f ψ, a _ fun t y
    h ↦ by convert (x.isUnit.map reduction).mul_right_inj; ext v; by_cases v = w <;> aesop]

omit [WeilData E] in
lemma LiftLaw.inclGL_lastColDatum k y : π'.ρ (inclGL k) (L (lastColDatum y) φ) =
  L (lastColDatum (reductionGL k • y)) φ := .trans (by simp [← smul_eq_mulVec, vecMul_transpose,
  IsUnit.smul_left_cancel, -val_map_apply]) (H.integral_equivariant 1 k ..)

/-- For a law L with constant γ and ramified φ: π'(u₀)L[𝐜]φ = 𝖥L[𝐛]φ = γL[𝐛]𝖥φ. Here 𝖥 =
`IsSplitLevel.fourierOp`, u₀ = diag(1, …, 1, N⁻¹), and 𝐛, 𝐜 are `IsSplitLevel.lastColDatum`,
`IsSplitLevel.charDatum` at the last basis vector. -/
lemma LiftLaw.u₀_charDatum_eq_fourierOp (h :
  φ ∈ ramified π) : let C := π'.ρ Λ.diagNInv (L (charDatum lastBasisVector) φ)
  C = fourierOp _ (L (lastColDatum lastBasisVector) φ) ∧ C =
    γ • L (lastColDatum lastBasisVector) (fourierOp π φ) := by
  let g (t : P → ZMod N) := ite (IsUnit t) (psiN t) 0
  erw [← H.diagNInv_law, liftFn_comp_eq_sum_smul, (sum_congr rfl fun t _ ↦ by simpa [g,
    Pi.isUnit_iff] using (fun w c ↦ .inr (H.eq_zero_of_smul_invariant h w (by aesop)))).trans
    (liftFn_comp_eq_sum_smul (· (.inr ()) (.inr ())) g : L _ φ = _).symm, liftFn_comp_eq_sum_smul
    (·ᵀ _) (g <| · _), and_iff_right, ← liftFn_comp_eq_sum_smul, liftFn_comp_eq_sum_smul (· _)
    (g <| · _)] <;> simp [g, H.inclGL_lastColDatum, -lastColDatum, sum_ite, surjInv_eq] <;>
    congr! 2 with y <;>
    (try rw [← H.integral_equivariant (liftGL (exists_GL_last_col_and_row.choose y)) 1]) <;>
    simp_all [surjInv_eq, exists_GL_last_col_and_row.choose_spec, ← (vecMul_injective_of_isUnit
    (exists_GL_last_col_and_row.choose y).isUnit).eq_iff (b := lastBasisVector)]

omit H

/-- For composable laws L_j with constants γ_j and ramified φ, the chain of the p maps d_i u₀
∑_y L_{2i+1}[𝐜_y]L_{2i}[𝐛_y] sends φ to ∏_{i<p}(d_i o_i ∏_{l≤2i+1} γ_l) ·
L_{2p−1}[𝐛]⋯L_0[𝐛]F^p φ, with F = `IsSplitLevel.fourierOp` and o_i the number of y non-zero at every
w ∈ P. -/
lemma compUpTo_pairs_eq_smul {X : ℕ → _} [∀ j, Fintype (X j)] (π : ∀ j, Rep ℂ (GL (X j ⊕ _)
  (LocProd P))) {L γ : ∀ j, _} (R : ∀ j, LiftLaw _ (π (j + 1)) (L j) (γ j)) {φ} {d : ℕ → ℂ} (h :
  φ ∈ ramified (π 0)) p : compUpTo (M := (π <| 2 * ·)) (d · • (π _).ρ diagNInv ∘ₗ ∑ y, L _
  (charDatum y) ∘ₗ L _ (lastColDatum y)) p φ = (∏ i ∈ range p, d i * #{y : X (2 * i + 1) ⊕ Unit →
  P → ZMod N | ∀ w, ∃ a, IsUnit (y a w)} • ∏ l ∈ range (2 * i + 2), γ l) • compUpTo
  (L · (lastColDatum lastBasisVector)) _ ((fourierOp _ ^ p) φ) := p.rec (by simp!) fun q ih ↦ by
  let B q ψ j := compUpTo (L · (lastColDatum lastBasisVector)) j ((fourierOp _ ^ q) ψ)
  have a j : B q φ j ∈ ramified _ := (h · |>.imp fun c ⟨a, ψ, r⟩ ↦ ⟨a, B q ψ j, by
    simpa [← r, B] using j.rec congr($((by simp [commute_iff_eq, mul_sum, sum_mul, ← map_mul,
      map_scalar, GeneralLinearGroup.scalar_commute] : Commute ((π _).ρ (inclGL (scalar _ c)))
      (fourierOp _)).pow_right q) ψ) fun j r ↦ .trans (r ▸ by simp! [← smul_eq_diagonal_mul,
      smul_eq_mul_diagonal]) ((R j).integral_equivariant (scalar _ c)⁻¹ (scalar _ c) ..)⟩)
  erw [prod_range_succ, mul_smul, mul_smul, smul_assoc, LinearMap.comp_apply, ih,
    map_smul _ _ (B ..), ← fun j ↦ (j.rec (by simp! [B, pow_succ']) fun j ih ↦ by
    erw [((R j).u₀_charDatum_eq_fourierOp (a j)).elim (·.symm.trans ·), ih]; simp! [B,
      prod_range_succ_comm] : fourierOp (π j) (B q φ j) = (∏ l ∈ range j, γ l) • B (q + 1) φ j),
    ← ((R _).u₀_charDatum_eq_fourierOp (a _)).1,
    ← sum_eq_card_nsmul fun y h ↦ .symm ?_, sum_filter_of_ne]; simp; rfl
  · intros; by_contra; simp_all [(R _).eq_zero_of_smul_invariant (a _) ‹_›, funext_iff]
  choose g r using (exists_GL_smul_single <| (mem_filter.1 h).2 ·)
  have ⟨k, c⟩ := (Pi.isUnit_iff.2 (g · (.inr ()) |>.isUnit)).map piRingEquiv.symm
  erw [show y = k • lastBasisVector by simp_all [funext_iff],
    ← (R _).integral_equivariant (liftGL k) 1, (R _).inclGL_lastColDatum]; simp [surjInv_eq]; rfl

end IsSplitLevel

open Pointwise TensorProduct
variable {E : Type} {M : Type _} [Field E] [CMType E] [AddCommGroup M] [Module ℚ M]
  [Module ℂ M] {n S : ℕ → Type} [∀ j, Fintype (n j)] [∀ j, AddCommGroup (S j)] [∀ j, Module ℂ (S j)]
  {κ : NumberField.InfinitePlace E → ℕ → ℕ} {e : ℕ → _} {K : ∀ j, _}
  {φ : AlgForm (E := E) (n 0) κ (e 0)}
  (k : ∀ j, Kernel (n j) (n (j + 1)) κ (e j) (e (j + 1)) (K j) (S j)) [∀ j, IsLevel (K j)]
  (a : ∀ j, Gf E (n j)) (Φ : ∀ j, _)

/-- The chain of j theta lifts with data Φ_0, …, Φ_{j−1}: the composite linear map from smooth
forms of stage 0 to smooth forms of stage j. -/
def chain := compUpTo (k · |>.lift (Φ _))

attribute [local simp] Kernel.lift_equivariant Kernel.ω_ω chain compUpTo

/-- Let φ be fixed by K_0 and a_i ∈ K_i for all i. Replacing each datum Φ_i by ω(a_i,
a_{i+1})Φ_i turns the value at φ of the chain of j lifts into its right translate by a_j. -/
lemma chain_equivariant (h : φ ∈ levelSpace (algFormRep ..) (K 0)) (a : ∀ j, K j) Φ j :
  chain k (fun j ↦ (k j).ω
  (a j, (a _).1) (Φ j)) j φ = algFormRep _ _ (a j).1 (chain k Φ j φ) := by induction j <;> simp_all

/-- The chain of p pairs of theta lifts, the i-th pair with datum Φ_i in S_{2i} ⊗ S_{2i+1}: a
linear map from forms of stage 0 to forms of stage 2p. -/
def chain₂ := compUpTo fun i ↦ TensorChain.liftInPairs (k · |>.lift) i (Φ i)

/-- The operator ω(a_{2i}, a_{2i+1}) ⊗ ω(a_{2i+1}, a_{2i+2}) on S_{2i} ⊗ S_{2i+1}, the data of
two consecutive kernels. -/
def twoKernelAction i := map ((k (2 * i)).ω (a _, a _)) ((k (2 * i + 1)).ω (a _, a _))

/-- Equivariance of the chain of p pairs of lifts: for a_j in G_j, moving the data t_i by
ω(a_{2i}, a_{2i+1}) ⊗ ω(a_{2i+1}, a_{2i+2}) and right-translating φ by a_0 right-translates
the output by a_{2p}. -/
lemma chain₂_equivariant t p φ : chain₂ k (fun i ↦ twoKernelAction k a i (t i)) p
  (algFormRep _ _ (a 0) φ) = algFormRep _ _ (a _) (chain₂ k t p φ) := by
  induction p <;> simp_all [chain₂]
  induction t _ <;> simp_all [TensorChain.liftInPairs, twoKernelAction]; rfl

lemma exists_linear_chain_eq_pure j φ g : ∃ β : _ →ₗ[ℂ] _, ∀ Φ, (chain k Φ j φ).1 g =
  β (TensorChain.pure Φ j) := by use! (TensorChain.lift (k · |>.lift) φ j · |>.1 g) <;> simp

/-- Joint invariance: the tensor ∑_{x∈s} L_x ⊗ Φ_{x,m−1} ⊗ ⋯ ⊗ Φ_{x,0} is unchanged by the joint
action of every tuple a with a_j ∈ K_j and a_j = 1 for j ≥ m. -/
def IsJointlyInvariant {X} m s (L : X → (WeylIndex (n m) κ → ℂ) →ₗ[ℂ] M) (Φ : X → ∀ j, _) := ∀ a :
    ∀ j, K j, (∀ j ≥ m, a j = 1) → ∀ β : _ →ₗ[ℂ] _, ∑ x ∈ s, L x (β (TensorChain.pure (fun j ↦
  (k j).ω (a j, a (j + 1)) (Φ x j)) m)) = ∑ x ∈ s, L x (β (TensorChain.pure (Φ x) m))

/-- A jointly invariant combination of chains at free levels, applied to a K_0-fixed φ and
evaluated at h, is a sum over tuples of classes of elements of A, provided A contains ∑ L_x
v_x whenever the v_x have a property P that φ has and the kernels propagate. -/
lemma IsJointlyInvariant.sum_chain_mem_nsmul {X m s L Φ} (H : IsJointlyInvariant k m s L Φ) (fr :
  ∀ j < m, ∀ g, classAut stdRatPoints (K j) g = ⊥) (hφ : φ ∈ levelSpace (algFormRep ..) (K 0)) (P :
  ∀ j, _ → _ → Prop) (hs : ∀ x ∈ s, ∀ j < m, ∀ g h v, P j g v → P _ h ((k j).jetMatrix ((k j).ω (g,
  h) (Φ x j)) v)) (hB : ∀ g, P 0 g (φ.1 g)) {h} {A : Set M} (hL : ∀ β : _ →ₗ[ℂ] _,
  let v (x : X) := β (TensorChain.pure (Φ x) m); (∀ x ∈ s, P m h (v x)) → ∑ x ∈ s, L x (v x) ∈ A) :
  ∑ x ∈ s, L x ((chain k (Φ x) m φ).1 h) ∈ (∏ j ∈ .range m, Nat.card (StdClasses (K j))) • A := by
  choose B hb using exists_linear_chain_eq_pure k
  induction' m with j ih; simpa [← hb, *] using hL (B 0 φ h)
  let T g β : TensorChain S j.succ →ₗ[ℂ] _ :=
    TensorProduct.lift ((k j).jetMatrix.compl₁₂ ((k j).ω (g, h)) β)
  have (g) β f : T g β (TensorChain.pure f _) = _ := TensorProduct.lift.tmul _ (TensorChain.pure ..)
  erw [Finset.prod_range_succ, mul_nsmul, ← classIntegral_sum _ (L · |>.toAddMonoidHom) (fun _ ↦ 1)
    (by simp) (by tauto)]
  refine classIntegral_mem_nsmul ?_ (fun a ha g ↦ ?_) fun _ ↦ ih (L := (L · ∘ₗ _)) (fun a _ β ↦ by
    simpa [*] using H a (by bound) (T ..)) ?_ ?_ fun β _ ↦ hL (T ..) ?_ <;> try tauto
  simpa [*, ← hb, ↓chain_equivariant] using
    H (Pi.mulSingle j ⟨a, ha⟩) (by simp_all [ne_of_gt]) (T g (B j φ g))

end

open Matrix GeneralLinearGroup Fintype WeilData Finset Gf stdLattice Space ContinuousLinearMap
  SemilocalField NeZero

variable {E n n' : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n']
  {P S : Finset (FinPlace E)} {N : ℕ} [Fact N.Prime] {m : Type} [Fintype m]

omit [WeilData E] in
@[simp] lemma scalarFin_atPlace ν (w : FinPlace E) : ((scalarFin n ν).atPlace w).1 =
  diagonal fun _ ↦ ν.1 w := diagonal_map rfl

lemma pairWeilFinite_scalarFin (a b : AutChar E) ν ν' : pairWeilFinite (stdSpace ..) (stdSpace ..) a
  b (scalarFin n ν, scalarFin n' ν') = pairChar (s := 1) (s' := 1) a b ((1, scalarFin n ν), 1,
  scalarFin n' ν') • pairWeilFinite _ _ 1 1 (1, scalarFin _ (ν' / ν)) := by
  ext; simp [pairWeil, G.onHom_scalarFin, ← map_one (scalarFin n), -map_one, -map_div]

variable (n n' P N m) in
/-- The operator τ_N = ∑_y ϱ_f(−y/N as last column) ⊗ ϱ_f(−ȳ/N as last row) on finite data of
two consecutive Hom spaces, y over n'-vectors of residues mod N at P. -/
def translateSum := ∑ y : n' → P → ZMod N, TensorProduct.map (((stdSpace E (n ⊕ Unit)).hom
  (stdSpace ..)).heisFinPart fun p ↦ ite p.2.isRight (-residueOverN (y p.1)) 0) (((stdSpace ..).hom
  (stdSpace E (m ⊕ Unit))).heisFinPart fun p ↦ ite p.1.isRight (-star (residueOverN (y p.2))) 0)

/-- The projection `Space.projOn` on the vectors that are vacua above S, restricted to an
endomorphism of the finite part `Space.finitePart` of 𝒮(V). -/
abbrev Space.projOnFinPart {s} (V : Space E n s) S := (V.projOn S).1.restrict fun _ ↦
  projOn_mem_finitePart

namespace IsSplitLevel

/-- For a Hecke character χ, the character g ↦ ∏_{w∈P} χ_w(det g_w) |det g_w|^(−k/2) of
GL_n(∏_{w∈P} E_w), with values in ℂ^×. -/
def detCharAt χ (k : ℕ) := (localChar P χ (-k)).toUnitHom.comp (det (n := n))

variable [h : IsSplitLevel P N] (g : GL n (LocProd P))

attribute [local simp] mem_O_locProd idem_mul_mem_Ô detCharAt idem_apply ne dotProduct mul_sum

/-- The homomorphism GL_n(∏_{w∈P} E_w) → finite adelic unitary group placing the w-component of
a matrix at the split place w, for each w in P. -/
def embedGL : GL n (LocProd P) →* Gf E n :=
  (atSplits star_notMem).comp (.pi (map <| Pi.evalRingHom _ ·))

omit [WeilData E] [Fact N.Prime] in
@[simp] lemma atPlaces_embedGL : atPlaces P (embedGL g) =
  g := by ext : 3; apply congr($(atPlace_atSplits star_notMem ..) _ _)

omit [WeilData E] [Fact N.Prime] in
lemma embedGL_mem_supportedOn : embedGL g ∈ supportedOn n P :=
  atSplits_mem_supportedOn star_notMem _

include h

section

omit [WeilData E] [Fact N.Prime]

lemma disjoint_star : Set.IsConjDisjoint (E := E) P := by grind [star_notMem]

lemma natCast_mem : ∀ w ∈ P, ↑N ∈ w.1 := by simp_all [h.4]

lemma mem_integralAbove_of_inclGL_eq {g : Gf E n} {a} (e : inclGL a = atPlaces P g) :
  g ∈ integralAbove n N := fun w o ↦ by
  refine ((h.4 w).1 o).elim ?_ (atPlace_star_mem_iff.1 ∘ ?_) <;> exact fun h ↦
    mem_intGL.2 ((mem_intGL.1 ⟨a, e⟩).imp (· · · ⟨_, h⟩ ⟨⟩) (· · · ⟨_, h⟩ ⟨⟩))

end

omit [WeilData E] in
lemma reduction_eq_iff_idem_mul_mem {x c u} (e : x.1 = evalPlaces P (N * u)) : reduction x = c ↔
  idem P * (u - residueOverN c) ∈ Ô E := by simp_all [reduction_eq_iff, sub_div]

omit [WeilData E] in
/-- Assume `IsSplitLevel` P N, w ∈ P, and ν an integral norm-one finite adele equal to 1 off w, w̄.
Then the scalar matrix ν comes, by `IsSplitLevel.embedGL`, from an integral unit scalar x of ∏_{P}
E_v with x ≡ 1 at all v ≠ w. -/
lemma exists_embedGL_scalar_eq_scalarFin {ν} (w : P) (a : ↑ν ∈ Ô E ∧ ∀ v ≠ w.1, star v ≠ w →
  ν.1 v = 1) : ∃ x : Oˣ, (∀ v ≠ w, h.reduction x v = 1) ∧ h.embedGL (inclGL (scalar n x)) =
  scalarFin n ν := ⟨.mkOfMulEqOne ⟨_, evalPlaces_mem_O _ a.1⟩ ⟨_,
  evalPlaces_mem_O _ (star_mem_Ô a.1)⟩ congr(⟨evalPlaces P $(ν.2.2), _⟩), fun v e ↦
  (residueEquiv v).map_eq_one_iff.2 congr(.mk _ ⟨$(a.2 v (by grind) (by grind [star_notMem])), _⟩),
  eq_of_supportedOn (embedGL_mem_supportedOn _) (by simp +contextual (disch := grind)
  [Units.ext_iff, a.2]) (by simp [Subtype.forall', embedGL, Units.ext_iff])⟩

variable (f : Matrix n' n _ → ℂ) (a b : AutChar E)

/-- The linear map sending a function on n'×n matrices over ∏_{w∈P} E_w to the operator it names
(`Space.name`) on the finite part of Hom(I_n, I_{n'}). -/
def name [h : IsSplitLevel P N] := (by apply LinearMap.mk₂ ℂ fun F v ↦
  ⟨_, name_mem_finitePart P (F ∘ (vecToMat · |>.map (evalPlaces P))) v.2⟩ <;> simp [Pi.add_comp,
  Pi.smul_comp] : _ →ₗ[ℂ] finitePart (hom (stdSpace E n) (stdSpace E n')) →ₗ[ℂ] finitePart _)

omit [WeilData E] in
lemma liftFn_eq_residueDatum : h.liftFn f ∘ (vecToMat · |>.map (evalPlaces _)) = residueDatum _
    fun T ↦ f (of fun i j w ↦ residueEquiv w (T w i j)) := funext fun x ↦ .symm (dite_congr
  (by simp; tauto) (by congr!; exact congrArg _ (dite_eq_left _)) (by simp))

instance isSchwartzBruhat_liftFn : IsSchwartzBruhat P (h.liftFn f ∘ (vecToMat · |>.map
  (evalPlaces _))) := by simpa [liftFn_eq_residueDatum] using
  isSchwartzBruhat_residueDatum (w := fun w : P ↦ w.1) _ (by grind [star_notMem])

/-- Let g, k be supported on P ∪ P̄ and f a function of residue matrices mod N. For every finite
datum v, ω_{a,b}(g,k) sends the operator named by f applied to v to that named by S ↦
f(k⁻¹Sg) applied to v, times explicit characters `IsSplitLevel.detCharAt` of g⁻¹ and k. -/
lemma pairWeilFinite_name k v : pairWeilFinite _ _ a b (embedGL g,
  h.embedGL k) (name (liftFn f) v) = ((detCharAt (b.spaceChar (card n')) (card n')
  g)⁻¹ * detCharAt (a.spaceChar (card n)) (card n) k) • h.name (liftFn f <| k⁻¹.1 * · * g.1) v := by
  nth_rw 2 3 [← atPlaces_embedGL g, ← atPlaces_embedGL k]
  ext1; simp [name, pairWeil_name_on, h.disjoint_star,
    embedGL_mem_supportedOn, -coe_units_inv, -atPlaces_embedGL]
  congr; simp [-atPlaces_embedGL, field]

omit [Fact N.Prime] h in
/-- Let χ(x) = a(x/x̄)υ(x)^(−i), with a(x/x̄) unramified at each w in P. Then
∏_{w∈P} χ_w(det g)·|det g|_w^(−k/2) = 1 for every k and every g in ∏_{w∈P} GL_n(O_w). -/
lemma detCharAt_inclGL (c : ∀ w ∈ P, CharUnramifiedAt a.baseChange.finPart w) i k (g : GL n _) :
    detCharAt (a.spaceChar i) k (inclGL (P := P) g) = 1 := by
  have := isIntegralUnit_iff_v_eq_one.1 (isIntegralUnit_iff_isUnit.2 g.det.isUnit)
  ext; simp_all [localChar, g.map_det, norm_locField_eq_q_zpow, CharUnramifiedAt, AutChar.spaceChar,
    charUnramifiedAt_upsilon ..]

omit [WeilData E] in
/-- Let P satisfy `IsSplitLevel`, ι : ℂ → ℂ_N be a ring map, k ≤ k′. At g = diag(1, …, 1, N) on S
(of any ranks), the N-adic size of ι(∏_{w∈P} χ_w(det g)·|det g|_w^(−k/2)) does not increase
from k to k′. -/
lemma norm_detCharAt_diagN_anti {ι : ℂ →+* ℂ_[N]} {χ k k'} (e : k ≤ k') :
    ‖ι (detCharAt χ k' (h.diagN n S))‖ ≤ ‖ι (detCharAt χ k (h.diagN n' S))‖ := by
  simp [diagN]; simp [-prod_mul_distrib, localChar]; gcongr; simp
  rw [← one_le_sq_iff₀ (by simp), ← norm_pow, ← map_pow]; norm_cast
  split <;> simp [norm_locField_eq_q_zpow, h.2, h.3, norm_p_eq_inv, NeZero.one_le]

omit [WeilData E] in
/-- For any finite set S of places, the element diag(1, …, 1, N) at all places of P is the
product of its part at P ∖ S and its part at P ∩ S. -/
lemma diagN_eq_sdiff_mul S : h.diagN n P =
  diagN n (P \ S) * diagN n S := by simp_all [diagN, ← map_mul, Pi.mul_def]

omit [WeilData E] in
/-- Let P satisfy `IsSplitLevel` for a prime N. For a finite adele z there is b in (ℤ/N)^P such
that, for every y in (ℤ/N)^P, z − y/N is integral at P exactly when Nz is integral at P and
y = b. -/
lemma exists_sub_residueOverN_mem_iff z : ∃ b, ∀ y : P → ZMod N, idem P * (z - residueOverN y) ∈ Ô
  E ↔ idem P * (N * z) ∈ Ô E ∧ b = y := ⟨_, fun y ↦ (iff_and_self.2 fun a ↦ by simpa [mul_sub,
  mul_div_cancel₀] using (add_mem (nsmul_mem (evalPlaces_mem_O _ a) N) (mem_O_locProd.2 fun w ↦
  _root_.natCast_mem (LocInt _) (y w).val))).trans
  (and_congr_right fun H ↦ (reduction_eq_iff_idem_mul_mem
  (@Function.invFun_eq _ _ ⟨0⟩ _ _ (by simp_all))).symm)⟩

attribute [local grind .] idem_mul_residueOverN idem_mul_self star_mul'

/-- Let P, S satisfy `IsSplitLevel` for N with P ∪ P̄ = S ∪ S̄, and u, u' be the projections
`Space.projOn` S of v, v'. Then τ_N(u ⊗ u') at S is ∑_z (𝐛_z(·D) ⊗ v) ⊗ (𝐜_z(D'·) ⊗ v'),
names at P, with D, D' = diag(1, …, 1, N) on P ∩ S, P ∖ S. -/
lemma translateSum_eq_sum_name (h' : IsSplitLevel S N) v v' :
  translateSum n n' S N m (projOnFinPart _ S v ⊗ₜ projOnFinPart _ S v') = ∑ z, h.name (lastColDatum
  z <| · * (h.diagN n S).1) v ⊗ₜ h.name (charDatum z <| (h.diagN m (P \ S)).1 * ·) v' := by
  let j : 𝔸f E := idem P; let ε : 𝔸f E := idem S
  have a : ε * star ε = 0 ∧ j + star j = ε + star ε := by
    simp [j, ε, DFunLike.ext_iff]; grind [IsSplitLevel]
  have r (y : S → ZMod N) : let x := residueOverN y; (ε + star ε) * x = x ∧ (ε + star ε) * star x =
      star x ∧ star x * x = 0 := by grind
  apply Module.Flat.tensorProduct_mapIncl_injective_of_left
  refine .trans ?_ (.trans (congrArg (TensorProduct.map ((apply ℂ _ v.1).1 ∘ₗ Space.name _ P)
    ((apply ℂ _ v'.1).1 ∘ₗ Space.name _ P)) (?_ : ∑ y : n' → S → ZMod N, schrodingerAct P (fun p ↦
    ite p.2.isRight (-residueOverN (y p.1)) 0) (boxIndicator _ P) ⊗ₜ schrodingerAct P (fun p ↦
    ite p.1.isRight (-star (residueOverN
    (y p.2))) 0) (boxIndicator _ P) = ∑ z, _ ⊗ₜ _)) (by simp_rw [map_sum]; rfl))
  · simp [j, ε, translateSum, *, mul_comm (residueOverN _), projOn, finHeisOp, semichar,
      idem_conjClosure_eq_add_star,
      name_schrodingerAct_boxIndicator, ↓disjoint_star (N := N), Pi.smul_def, apply_ite]
  refine sub_eq_zero.1 (tensor_eq_zero_of_separating (f := .proj) funext _ fun T ↦
    funext fun R ↦ ?_)
  simp
  let p := 1 + ε * (N - 1)
  have k x : j * x ∈ Ô E ∧ j * star x ∈ Ô E ↔ ε * x ∈ Ô E ∧ ε * star x ∈ Ô E := by
    grind [IsSplitLevel, star_star, idem_mul_mem_Ô, v_star_apply]
  have e t s : ∃ b, ∀ y : S → ZMod N, j * (t - residueOverN y) ∈ Ô E ∧ j * (s - star
    (residueOverN y)) ∈ Ô E ↔ (j * (t * p) ∈ Ô E ∧ j * ((N + 1 - p) * s) ∈ Ô E) ∧ b = y := by
    let z := j * t + star (j * s); peel h'.exists_sub_residueOverN_mem_iff z with b y _
    obtain ⟨c, d⟩ := k (z - residueOverN y), k (p * z); simp [z, p] at c d
    grind [idem_mul_star h.disjoint_star]
  choose b e using fun i ↦ e (T (i, .inr ())) (R (.inr (), i))
  have : (diagN n S).1 = diagonal (evalPlaces P <| ite ·.isLeft 1 p) ∧ (diagN m (P \ S)).1 =
    diagonal (evalPlaces P <|
    ite ·.isLeft 1 (N + 1 - p)) := by simp +contextual [diagN, funext_iff, apply_ite, p, ε]
  simp [this, show ∀ x, evalPlaces P x ∈ O ↔ j * x ∈ Ô E by simp [j], ← map_mul, vecToMat,
    schrodingerAct, ← ite_and, mem_integralBox, -idem_mul_mem_Ô, ← AddChar.map_add_eq_mul,
    liftFn_apply, ← map_sum, sum_prod_type]
  clear * - h r e; rw [Fintype.sum_eq_single b fun y ↦ by have e i := e i (y i); grind]
  replace e i := e i (b i); repeat split
  generalize k : h.reduction _ = c
  apply psi₀_congr 0 (sub_mem (sum_mem (t := univ) fun i _ ↦ ((e i).2 (by simp [*])).elim mul_mem)
    ((reduction_eq_iff_idem_mul_mem (u := ∑ i,
    R (.inr (), i) * T (i, .inr ())) (by simp [-map_mul]; grind)).1 k))
  simp [← sum_add_distrib, ← sum_neg_distrib, ← sum_sub_distrib, ← sub_add, mul_sub]
  all_goals grind
