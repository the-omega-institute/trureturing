/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Landherr/Landherr
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Landherr/Landherr
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Landherr.Landherr. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Landherr/Landherr.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.Landherr.SumOfTwoSquares
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Landherr's Hasse principle for hermitian forms, and weak approximation for unitary
groups. The form here covers only adelically unimodular spaces of equal signature over a CM field
containing the roots of unity of order 5040. It is proved from Hasse's norm theorem instead of
Hasse-Minkowski, and approximation uses a Cayley transform with a norm-one scalar. Source: W.
Landherr, Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper, Abh. Math.
Sem. Hamburg 11 (1936) 245-248; M. Kneser, Lectures on Galois cohomology of classical groups, TIFR
47 (1969), §5.5. -/


open NumberField Matrix Complex Set Function MatMul
variable {E n s} [Field.{0} E] [CMType E] [Fintype n] [StablyUnram E] (V W : Space E n s)
attribute [local simp] map_smul' smul_smul sum_single_eq_diagonal Pi.isUnit_iff Matrix.map_sub
  Subtype.ext_iff funext_iff QuadraticAlgebra.norm_def

omit [StablyUnram E] in
/-- For every adele σ (as a 1×1 matrix) there is an adele a with the
same norm as b = 1 + σa: āa = b̄b. -/
lemma exists_norm_eq_norm_one_add_mul (σ : Matrix Unit Unit (𝔸 E)) : ∃ a b, 1 + σ * a = b ∧ aᴴ * a =
  bᴴ * b := by
  let x := (σ () ()).2
  obtain ⟨⟨t, _⟩, e, _, ⟨p, _⟩, _, q, _⟩ := (@isUnit_natCast_finAdele E _
    _ 2 nofun).exists_left_inv, by simpa using isValuationPair_Ohat (1 + x) (x * (1 - x))
  let f c d := scalar Unit (update (1 - id)⁻¹ 1 c ∘ (σ () ()).1, t * ((2 - x) * p - q) * d)
  use f (-2⁻¹) (x * e + star e - 1), f 2⁻¹ (x * star e + 1 - e)
  simp [f, update, ← ext_iff, Prod.ext_iff]; grind [star_mul]

/-- Hasse principle for representing 1: over a stably unramified CM field E (`StablyUnram`), if a
hermitian matrix J over E has an adelic vector z with zᴴJz = 1, it has a vector v over E
with vᴴJv = 1. -/
lemma exists_form_eq_one (K : Matrix n n E) (j : Kᴴ = K) (z : Matrix n Unit (𝔸 E))
    (k : zᴴ * K.map toAdele * z = 1) : ∃ w : Matrix n Unit E, wᴴ * K * w = 1 := by
  let N (u : Matrix n _ E) :=
    Subtype.mk ((uᴴ * (K * u)) () ()) (mem_maximalRealSubfield_iff_star_eq.2 (star_form j ..))
  have A {T} (f : Set.Finite T) := (denseRange_rat_matrix_add f.cj.infinite_compl.nonempty
    1).exists_mem_open (((isOpen_set_pi finite_univ fun _ _ ↦ isOpen_re_gt 0).prod
    (f.cj.isOpen_biInter fun w _ ↦ (Valued.isOpen_sphere _ one_ne_zero).preimage (continuous_evalAt
    w))).preimage_of_continuous (f := fun x ↦ (xᴴ * K.map toAdele * x) () ())) ⟨z, by aesop⟩
  simp_all [conjClosure, star_idem, union_comm, -compl_union, -mem_union, ← Matrix.map_mul]
  choose u a using A finite_empty
  have o : (N u).1 ≠ 0 := by aesop
  choose v b c using A (finite_idele_val_ne_one (principalIdele (.mk0 _ o)))
  let B := (N (u + v) - N u - N v) / (1 + 1)
  obtain ⟨⟨i, _⟩, ⟨⟨p, r⟩, q, s⟩, h⟩ := ‹StablyUnram E›.exists_i_c₀,
    exists_sq_add_sq_quadraticAlgebra _ (N v) B (ofRealHom.comp · |>
    bijective_cmType_restrict.2 |>.elim fun w e ↦ (a.1 w).trans_eq congr(($e (N u)).re)) (by simp) c
  use ((p + q * i - (r * i - s) * B : E) / N u) • u + (r * i - s : E) • v
  simp [mem_maximalRealSubfield_iff_star_eq.1, ← ext_iff]
  simp_all +zetaDelta [RingOfIntegers.ext_iff, QuadraticAlgebra.ext_iff]; grind

attribute [local simp ←] Int.cast_mul

/-- Let E be stably unramified (`StablyUnram`), J hermitian over E, s signs, t a set of indices, D
= ∑_{i∈t} s_i E_ii. If XᴴJX = D for a square adelic matrix X, then AᴴJA = D for a square
matrix A over E. -/
lemma exists_rat_frame_of_adelic t : ∀ ⦃J X : Matrix n n _⦄, Jᴴ = J ∧ Xᴴ * J.map toAdele * X =
  ∑ i ∈ t, .single i i (s i : 𝔸 E) → ∃ A, Aᴴ * J * A = ∑ i ∈ t, .single i i (s i) :=
  t.induction (fun _ _ _ ↦ ⟨0, by simp⟩) fun j t l I J X ⟨H, h⟩ ↦ by
  let c : E := s j
  let u := Matrix.single j () (toAdele c)
  have k := by simpa +contextual [Matrix.sum_mul, Finset.sum_eq_single j, u] using congr($h * u)
  have ⟨w, W⟩ := exists_form_eq_one (c • J) (by aesop) (X * u) (by aesop)
  let y := (wᴴ * J).map toAdele * X
  let r := y * (1 + -u * uᴴ)
  let ⟨a, _, rfl, e⟩ := exists_norm_eq_norm_one_add_mul (y * u)
  let ρ := a * r + -uᴴ
  have ⟨A, a⟩ := @I (J - c • J * w * wᴴ * J) (X * (1 + u * ρ)) ⟨by aesop, by
    linear_combination (norm := (simp +zetaDelta [H, l, (by aesop : ∀ (x : 𝔸 E) (M : type_of% r),
      Matrix.single () () x * M = x • M)]; abel))
      congr($h + ($k * ρ)ᴴ + (1 + u * ρ)ᴴ * $k * ρ + toAdele c • (rᴴ * $e * r))⟩
  let b := -c • wᴴ * J * A + .single () j 1
  use A + w * b
  linear_combination (norm := simp [b, c, *]) a + c • congr(bᴴ * $W * b)
  abel

/-- Landherr's theorem: over stably unramified E (`StablyUnram`), two spaces V, W with the same
signs have isometric hermitian matrices: aᴴ J_V a = J_W for some a in GL_n(E).

Known result: Landherr's Hasse principle for hermitian forms; weak approximation for unitary
groups. -/
lemma Space.landherr : ∃ a : GL n E, a.1ᴴ * V.J * a = W.J := by
  choose a H using fun V : Space E n s ↦ exists_rat_frame_of_adelic (s := s) .univ ⟨V.isHermitian_J,
    (gram_mul_of_gram_eq V.3 (gram_inv_of_gram_eq (signedSpace ..).3)).trans (by simp)⟩
  have u V := isUnit_of_mul_isUnit_right ((H V).substr (by simp))
  use (u V).unit / (u W).unit, gram_mul_of_gram_eq (H V) (gram_inv_of_gram_eq (H W))

/-- Landherr's theorem for spaces with a point: over stably unramified E (`StablyUnram`), any two
spaces V, W with the same signs differ by a rational change of coordinates a and moving the
point by some g in G. -/
lemma Space.exists_eq_move : ∃ (a : GL n E) (g : G E s) (h : a.1ᴴ * V.J * a = W.J), W.x =
  (a.map toAdele)⁻¹ * V.x * g.toUnitary ∧ ∀ γ, V.ratEmbed (U.conj a h γ) = g * W.ratEmbed γ * g⁻¹ :=
  (V.landherr W).imp fun a h ↦ ⟨G.toUnitary.symm ⟨_, gram_mul_of_gram_eq (gram_inv_of_gram_eq V.3)
  (gram_mul_of_gram_eq (x := a.map toAdele) (by simp [← h]) W.3)⟩,
  h, by simp [ratEmbed, toRatCoords, U.map, MulEquiv.symm_apply_eq, mul_assoc]⟩
