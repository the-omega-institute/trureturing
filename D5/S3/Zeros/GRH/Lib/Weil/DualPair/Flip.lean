/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/Flip
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/Flip
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.Flip. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/Flip.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.PairSumNegation
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

This file: Adjoint map exchanges the two groups of a dual pair, up to a phase. -/

open Matrix Fintype G Int stdLattice MvPolynomial NumberField Sgn Std WeilData

attribute [-simp] matToVec_smul

variable {E : Type} [Field E] [CMType E] [WeilData E] {n a : Type}
  [Fintype n] [Fintype a] {s t t'} {c : (Ô E)ˣ} (hc : star c.1.1 * c = -1) (ht : t' = -t)
  (V : Space E a t) (W : Space E n s)

/-- For a sign t and a unit c of Ô, the idele with component t at every infinite place and
finite part cα/ᾱ. -/
@[simps! -isSimp val] noncomputable def flipIdele (c : (Ô E)ˣ) (t : ℤˣ) :
    (𝔸 E)ˣ := MulEquiv.prodUnits.symm (t.map (castRingHom _).1, c.map (Ô E).subtype * α * star α⁻¹)

attribute [local simp] sum_prod_type Matrix.mul_assoc Prod.ext_iff starCoordEquiv _root_.funext_iff
  pairSign realVac val_flipIdele pairWeil

/-- For a unit c of Ô with c̄c = −1 and signs t′ = −t, the change of coordinates x ↦ (1, cα/ᾱ)
ε_s x* ε_t from signs t′_i s_j to signs s_j t_i. -/
noncomputable def flipCoords : Std E (.id ℂ) (homSigns t s) (homSigns s t') := by
  use starCoordEquiv (.prodComm ..) (flipIdele c ∘ homSigns t s),
    starCoordEquiv (.prodCongr 1 (.prodComm ..)) (.map (castRingHom ℂ) <| homSigns t s ·.2),
    starCoordEquiv (.prodComm ..) fun _ ↦ c.map (Ô E).subtype
  any_goals intro; erw [Submodule.smul_mem_iff' _ c]
  repeat simp_all [adelicSum, val_scaleIdele_fst, val_scaleIdele_snd, realHeis, signMatrix,
    intVectors, Finset.sum_comm (γ := a), mul_right_comm _ _ (star c.1.1), ← mul_assoc, ← cast_mul,
    mul_comm, ← psi₀_star, stdLattice, dotProduct] <;> grind [star_mul', star_one, α.mul_inv,
    star_star, star_mem_Ô]

/-- Let c be a unit of Ô with c̄c = −1 and t' = −t. The change of coordinates `flipCoords` sends
an adelic matrix x to u·ε_s x* ε_t, with ε_s, ε_t the standard forms and u the idele (1,
cα/ᾱ), 1 at infinity. -/
lemma flipCoords_apply x : (flipCoords (s := s) hc ht).φ x = matToVec ((flipIdele c 1).1 • (stdForm
  E s * (vecToMat x)ᴴ * stdForm E t)) := by simp [flipCoords, stdForm, matToVec, vecToMat, field]

/-- Let c ∈ Ô^× have c̄c = −1, V′ have signs opposite to V, and φ be the adjoint `flipCoords`.
Then (ω(g,h)f)^φ = υ(det g)^{rk W} υ(det h)^{−rk V} ω(h,g)f^φ, for the Weil representations
of Hom(V,W) and Hom(W,V′). -/
lemma flipCoords_map_omega {V'} g h f : (flipCoords hc rfl).map ((V.hom W).ω (onHom (g, h)) f) =
  pairChar (upsilonU1 ^ card n)
  (upsilonU1 ^ card a) (h, g) • (W.hom V').ω (onHom (h, .neg g)) ((flipCoords hc rfl).map f) := by
  apply ω_map <;> simp [↓onHom_mulVec, flipCoords_apply, mat_inv]
  convert weilMultiplier_neg _ (onHom (g, h))⁻¹.mat_neg; iterate 2 simp [← adelicAction_Δ,
    det_onHom]
  rw [weilMultiplier, finMultiplier, ((saturatingElem _).2.map_of_le_comap
    (reindexRingEquiv _ (.prodComm ..)).toRingHom (by tauto)).glMultiplier_transpose]
  congr 2 with
  rw [realMultiplier, ← principalMinor_submatrix (.prodComm ..), ← principalMinor_transpose]; congr
  any_goals (try ext); apply_rules [mul_comm, det_reindex_self]
  simp [mul_comm]

/-- The opposite space of V = (J, x): matrix −J, opposite signs, point x scaled by the idele (1,
c̄ᾱ/α), c the fixed finite idele with c̄c = −1. -/
@[simps -isSimp] noncomputable def flipSpace : Space E _ (-t) := ⟨-V.J, .scalar _
  (star (flipIdele Weil.normNegOne 1)) * V.x, by simp [Matrix.map_neg, V.gram_point, stdForm,
            ← smul_eq_diagonal_mul, ← diagonal_smul]; grind [star_normNegOne_mul_self, star_mul,
  star_one, α.mul_inv]⟩

/-- Let V' have signs opposite to V and x_{V'} l = (1, conj(cα/ᾱ))·x_V. For each b some z of
modulus one has θ^{W,V'}_{b⁻¹υ^{rk W}, a'⁻¹υ^{rk V}}(f^φ)(h, lg) = z θ^{V,W}_{a',b}(f)(g,h)
for all a', f, g, h, φ being `flipCoords`. -/
lemma exists_pairTheta_flip V' (l : G E t') (hl : V'.x.1 * l.mat = star (flipIdele c 1).1 • V.x) b :
  ∃ z, ‖z‖ = 1 ∧ ∀ a' f g h g', g'.mat = l.mat * g.mat → pairTheta W V' (b⁻¹ * upsilonU1 ^ card n)
  (a'⁻¹ * upsilonU1 ^ card a) ((flipCoords hc ht).map f) (h, g') =
  z * pairTheta V W a' b f (g, h) :=
  have ⟨z, k, H⟩ := (flipCoords hc ht).exists_theta_omega_map (V.hom W) (W.hom V') (onHom (1, l))
    fun _ ↦ W.mem_ratVectors_hom.2 ∘ .imp' (V.J⁻¹ * ·ᴴ * W.J)
    (by simp_all [← conjTranspose_map_toAdele, V.map_J_inv, W.map_J, flipCoords_apply,
    ← V'.x.1.mul_assoc, conjTranspose_nonsing_inv, ↓onHom_mulVec]) ∘ V.mem_ratVectors_hom.1
  ⟨(b⁻¹ * upsilonU1 ^ card n).1 l.det / z, by simpa, by
    cases ht; intros; have : z ≠ 0 := by grind [norm_zero]
    simp [ext_mat (g' := l * .neg _) (by simpa), *, pairTheta, field, flipCoords_map_omega,
    rep_apply_apply, ← onHom.map_mul, mul_pow]⟩

/-- The ℂ-algebra map on polynomials sending the variable X_(τ,i,j) to −s_i t_j X_(τ,j,i):
transposition with signs. -/
noncomputable def flipPoly t s := bind₁ fun p :
    InfinitePlace E × n × a ↦ (homSigns (-t) s p.2 : ℂ) • X (R := ℂ) (p.1, p.2.swap)

lemma realMap_flipCoords_polyVector P : (flipCoords (s := s) hc ht).realMap (polyVector _ P) =
  polyVector _ (flipPoly t' s P) := by
  ext; simp [realMap, ← aeval_eq_eval, aeval_bind₁, ↓vac_realEquiv, flipPoly]
  congr; aesop (add simp [holCoord_eq, flipCoords, mul_comm])
