import OmegaMath.NumberTheory.GRH.New.Filling.BesselSystem
import OmegaMath.NumberTheory.GRH.Lib.Adelic.Transference.MassBasic
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Letters of this folder: f = (e₁, …, e_ϱ, z) is the frame, Z(γ) = (h(f_j, γf_l)), κ indexes X₀; 𝖴,
𝖴⁰, H, S are
`besselU`, `besselU0`, `besselH`, `besselS`; Gq = 𝖦 = `GRes`; standing hypotheses: `IsAdmissible`.
This file: Data record for filling, size hypotheses, names for groups, terms, amplitudes and
constants. -/

noncomputable section

open Finset Set NumberField MeasureTheory Matrix Real Fintype Fin Complex Classical Valued


variable (E : Type) [Field E] [CMType E] (𝔰 : Shape)

/-- The data of the filling theorem over E: a split prime N = ππ̄, two other primes with chosen
places above them, a generator ϖ of the different, a free level Kc, and Bessel systems at
infinity. -/
structure Filling where
  (N : ℕ) (levelPrime : _ → ℕ) (piBar : (𝔸f E)ˣ) (ϖ : 𝓞 E) (b) chosenPlaces : Fin 2 → Set (FinPlace E)
  [fintypeChosen (i) : Fintype (chosenPlaces i)]
  (columnLevel) (aut_columnLevel (g) : classAut (stdSpace E 𝔰.κ).Γf columnLevel g = ⊥) [hasFiniteType_columnLevel : IsLevel columnLevel]
  besselSys : InfinitePlace E → BesselSystem 𝔰 b (numInfPlaces E)
  piBar_mul_star : piBar * star piBar.1 = N
  N_prime : N.Prime
  N_split (w : FinPlace E) : v (piBar.1 w) = 1 ∨ w.q = N ∧ v (piBar.1 (star w)) = 1
  piBar_mem : ↑piBar ∈ Ô E
  levelPrime_prime i : (levelPrime i).Prime ∧ levelPrime i ≠ N
  le_levelPrime i : b ^ 10 ≤ levelPrime i
  levelPrime_le i : levelPrime i ≤ b ^ 11
  chosenPlaces_q i : ∀ w ∈ chosenPlaces i, w.q = levelPrime i
  chosenPlaces_injective : (·.2.1 : (Σ i, chosenPlaces i) → _).Injective
  star_notMem_chosenPlaces {i j w} : w ∈ chosenPlaces i → star w ∉ chosenPlaces j
  g_dvd_iff r : ↑(levelPrime 0 * levelPrime 1) ∣ r ↔ ∀ p : Σ i, chosenPlaces i, reduceAt p.2 r = 0 ∧ reduceAt p.2.1 (star r) = 0
  card_chosenPlaces i : card (chosenPlaces i) = numInfPlaces E
  star_ϖ : star ϖ = -ϖ
  span_ϖ : differentIdeal ℤ _ = .span {ϖ}
  /-- The rank ϱ is at least 10⁵. -/
  ϱ_le : 10 ^ 5 ≤ 𝔰.ϱ
  pow_six_le : 2⁻¹ ^ 𝔰.ϱ ≤ b⁻¹ ^ 6
  degree_le : (𝔰.ϱ + 1) * Module.finrank ℚ E ≤ 2 ^ (2 * 𝔰.ϱ)
  pow_le_k : 1000 * (2 * 𝔰.ϱ + 2) ^ 9 ≤ 𝔰.k
  ϱ_le_k : 1000 * (2 * 𝔰.ϱ + 2) ≤ 𝔰.k
  k_le_f : 𝔰.k ≤ numInfPlaces E
  size_le : (200 * (numInfPlaces E * 𝔰.k) * rootDiscr E) ^ 1000 ≤ b
  f_le_b : numInfPlaces E ≤ b / 1000
  k_le_b : 𝔰.k ≤ b
  rd_le_b : rootDiscr E ≤ b
  succ_le_b : ↑(𝔰.ϱ + 1) ≤ b
  thousand_le_b : 1000 ≤ b
  one_le_b : 1 ≤ b
  g_le_b_pow : ↑(levelPrime 0 * levelPrime 1) ≤ b ^ 23
  le_g : b ^ 19 ≤ ↑(levelPrime 0 * levelPrime 1)
  le_N : (5 : ℝ) ≤ N
  pow_chain : 10 ^ 10 * 𝔰.n ^ 4 ≤ 𝔰.n ^ 6 ∧ 3 * 𝔰.n ^ 6 + 12 ≤ 𝔰.n ^ 7 ∧ 𝔰.n ^ 7 ≤ 𝔰.k

variable {E 𝔰} (S : Filling E 𝔰) (R : Type) [CommRing R]

namespace Filling


attribute [instance] fintypeChosen hasFiniteType_columnLevel

attribute [scoped simp] Nat.Prime.ne_zero N_prime levelPrime_prime

/-- The natural number g = q₀q₁, the product of the two primes of the data. -/
abbrev g := S.levelPrime 0 * S.levelPrime 1

/-- For a commutative ring R, the diagonal Gram matrix over R of X₀ ⊕ Ez in the standard basis:
1 on κ and −N at z. -/
abbrev ratMiddle := 𝔰.middleGram (S.N : R)

/-- For a commutative ring R, the Gram matrix over R of X₀ ⊕ Ez in the lattice basis, where
e_{k₀} is replaced by e_{k₀}/π̄ + z/N. -/
abbrev latMiddle := latMiddleGram 𝔰 (S.N : R)

/-- For a commutative ring R with involution, the unitary group over R of the form made of ϱ
hyperbolic pairs and the middle Gram matrix `Filling.ratMiddle`. -/
abbrev G [StarRing R] := (S.ratMiddle R).G

/-- The unitary group over the finite adeles of E of the form made of ϱ hyperbolic pairs and the
middle Gram matrix `Filling.latMiddle` (lattice basis). -/
abbrev GFin := (S.latMiddle (𝔸f E)).G

/-- The finite group Gq (or 𝖦): the product, over i = 0,1 and the chosen places w above qᵢ, of
the general linear groups of
rank dim V over the residue fields at w. -/
abbrev GRes := ∀ i (w : S.chosenPlaces i), GL 𝔰.BesselIndex (ResField w.1)

/-- The set of tuples choosing, for each infinite place v, one coordinate index of the Bessel
system at v. -/
abbrev BesselCoord := ∀ v, (S.besselSys v).I

/-- The set of double cosets U(X₀)(E⁺) \ U(X₀)(𝔸_f) / Kc, for the unitary group of the standard
form on κ. -/
def Classes := DoubleCosets (stdSpace ..).Γf S.columnLevel deriving Nonempty

variable [σ : Side] (T : Set (S.G E)) (c : S.Classes) (s : S.GRes) (c' γ v a i j)
  (y : InfinitePlace E → 𝔰.G₁)
omit σ

/-- For a rational element γ of the unitary group, the matrix Z(γ) = (h(f_j, γf_l)) of products
between the frame and its image under γ. -/
abbrev frameProducts (γ : S.G E) := (S.ratMiddle E).frameGram γ

/-- The subgroup K of the finite adelic unitary group (lattice basis) of elements that are
integral invertible matrices over the profinite completion of the ring of integers. -/
def latStabilizer := (intGL _ (Ô E)).subgroupOf S.GFin

/-- The homomorphism from the integral subgroup K to the finite group Gq reducing matrix entries
modulo each chosen place above q₀ and q₁. -/
protected def reduction : S.latStabilizer →* S.GRes := .pi fun _ ↦
  .pi (reduceAt · |> intGL.map |>.comp (S.GFin.subtype.subgroupComap _))

/-- The principal congruence subgroup K(g): the kernel of the reduction from K to Gq, as a
subgroup of the finite adelic unitary group. -/
def principalLevel := S.reduction.ker.map S.latStabilizer.subtype

/-- For a subgroup A of the finite adelic unitary group, the image of A ∩ K in the finite group
Gq under reduction. -/
def reducedImage A := (Subgroup.subgroupOf A _).map S.reduction

/-- The real number κ_v, the real part of g·v(ϖ)/(2πi), where v(ϖ) is the image of ϖ under the
chosen embedding at v. -/
def kappa := (S.g * Φ v S.ϖ.val / (2 * π * .I)).re

/-- The scales of the normalised basis at v: κ_v^(ϱ−a)/√N on e_a, 1 on κ, 1/√N on z, and the
inverse of the scale of e_a on e*_a. -/
def basisScale : 𝔰.BesselIndex → ℂ := let s a := S.kappa v ^ (𝔰.ϱ - a) / √S.N; (s ·) ⊕ᵥ
    ((1 ⊕ᵥ fun _ ↦ s 𝔰.ϱ) ⊕ᵥ (s ·)⁻¹)

attribute [local simp] zero_lt_iff forall_fin_succ' splitGram middleGram pow_mul' fieldEq
  discr_ne_zero

lemma map_splitGram_ratMiddle {R'} [CommRing R'] (f : R →+* R') : (S.ratMiddle R).splitGram.map f =
  (S.ratMiddle _).splitGram := by aesop

/-- The additive character x ↦ ψ_f(−x/ϖ) of the finite adeles of E, with values in ℂ. -/
def selfDualChar := (Circle.coeHom.compAddChar (ψf E)).mulShift ↑(-S.ϖ.val⁻¹)

@[simp high] lemma varpi_ne_zero :
  S.ϖ.val ≠ 0 := mod_cast ne_zero_of_differentIdeal_eq_span S.span_ϖ

/-- The number κ_v^(2(ϱ−a))/N, the square of the scale of the frame vector of index a at v. -/
def frameScaleSq := S.kappa v ^ (2 * (𝔰.ϱ - a)) / S.N

/-- The product over infinite places v and a = 0,…,ϱ of (κ_v^(2(ϱ−a))/N)^(k+2(ϱ−a)), where k is
the size of κ. -/
def frameScaleProd := ∏ v, ∏ a : Fin (𝔰.ϱ + 1), S.frameScaleSq v a ^ (𝔰.k + 2 * (𝔰.ϱ - a))

/-- The number (g^(ϱ(2(ϱ+k)+1))/N^k)^f · vol(Ô)^(−ϱ(ϱ+k)) · |D_E|^(ϱ/4) / `frameScaleProd`, k = |κ|,
f the number of infinite places; it serves as the covolume ν of 𝖴_c(g) in 𝖴_∞. -/
def unipCovolume := let d := ∑ a ∈ .range 𝔰.ϱ, (a + (𝔰.k + 1) + a); (S.g ^ (2 * d + 𝔰.ϱ) /
             S.N ^ 𝔰.k) ^ numInfPlaces E / volÔ E ^ d * √√|discr E| ^ 𝔰.ϱ / S.frameScaleProd

/-- The constant c_* = ((2π)^k rd_E^(1/2−k) / ((k−1)! N^k))^f, with k = |κ|, rd_E the root
discriminant and f the number of infinite places. -/
def siegelConst :=
  (π ^ 𝔰.k / (𝔰.k - 1).factorial / S.N ^ 𝔰.k) ^ numInfPlaces E * √√|discr E| * volÔ E ^ 𝔰.k

/-- For a rational γ, the element 𝗀(γ) = |D_{ϱ+1}|² − N²|D_ϱ|² of E formed from the last two
leading
minors of Z(γ). -/
abbrev termDisc := frameDisc ↑S.N (S.frameProducts γ)

lemma basisScale_besselFrame : ∀ b, S.basisScale v (𝔰.besselFrame b) =
  S.kappa v ^ (𝔰.ϱ - b) / √S.N := by simp [basisScale]

lemma coe_kappa : S.kappa v = S.g * Φ v S.ϖ / (2 * π * .I) := conj_eq_iff_re.1 (by
  simpa [map_ofNat] using congr(-Φ v $S.star_ϖ))

@[simp] lemma kappa_ne_zero : S.kappa v ≠ 0 := by simp [← ofReal_ne_zero, coe_kappa]

@[simp] lemma frameScaleSq_pos : 0 < S.frameScaleSq v a := by simp [frameScaleSq, sq]

lemma frameScaleProd_pos : 0 < S.frameScaleProd := prod_pos (by simp [prod_pos])

@[simp] lemma basisScale_ne_zero : ∀ i, S.basisScale v i ≠ 0 := by simp [basisScale]

/-- The invertible diagonal complex matrix whose entries are the scales `Filling.basisScale` of the
normalised basis at v. -/
def basisScaleGL := diagGL (.mk0 _ <| S.basisScale_ne_zero v ·)

lemma gram_basisScaleGL : (S.basisScaleGL v).1ᴴ * (S.ratMiddle ℂ).splitGram * (S.basisScaleGL v).1 =
  (𝔰.middleGram 1).splitGram := by simp_all [basisScaleGL, basisScale, ← ext_iff, ← ofReal_pow]

/-- The invertible matrix over the finite adeles whose columns are the lattice basis of V
(e_{k₀} replaced by e_{k₀}/π̄ + z/ππ̄) in the standard basis. -/
abbrev latBasis := besselLatticeBasis 𝔰 S.piBar

/-- The isomorphism from the finite adelic unitary group in the standard basis to that in the
lattice basis, given by conjugation with the change of basis matrix. -/
def toLatBasis : S.G (𝔸f E) ≃* S.GFin :=
  (U.conj _ (gram_besselLatticeBasis _ _ S.piBar_mul_star)).symm

/-- The homomorphism from the rational unitary group to the adelic unitary group induced
entrywise by the diagonal map from E to its adeles. -/
def ratToAdelic : S.G E →* S.G (𝔸 E) := U.map toAdele (h := map_splitGram_ratMiddle ..)

/-- The homomorphism from the adelic unitary group to the product of copies of G₁, taking each
infinite component and conjugating by the diagonal rescaling matrix there. -/
def adelicToInf : S.G (𝔸 E) →* type_of% y := .pi fun v ↦ .comp
  (U.conj _ (S.gram_basisScaleGL v)).symm (U.map (evalInf v) (h := map_splitGram_ratMiddle ..))

/-- The homomorphism from the adelic unitary group to the finite adelic unitary group in the
lattice basis: take the finite part, then change basis. -/
def adelicToFin : S.G (𝔸 E) →* S.GFin :=
  .comp S.toLatBasis (U.map (.snd ..) (h := map_splitGram_ratMiddle ..))

/-- The homomorphism sending a rational element of the unitary group to its tuple of rescaled
images in G₁ at all infinite places. -/
def ratToInf := S.adelicToInf.comp S.ratToAdelic

/-- The homomorphism sending a rational element of the unitary group to its image in the finite
adelic unitary group, written in the lattice basis. -/
def ratToFin := S.adelicToFin.comp S.ratToAdelic

/-- The homomorphism including the finite adelic points of U(X₀) in the finite adelic unitary
group of V, written in the lattice basis. -/
def inclHFin := S.toLatBasis.toMonoidHom.comp (toBesselH ..)

instance : Fintype S.Classes := @ofFinite _ HasFiniteType.finite_classes

/-- For a double coset class c, the image h_c in the finite adelic unitary group of V of a
chosen representative of c. -/
abbrev h := S.inclHFin c.out

/-- The element h_c⁻¹ γ h_c' of the finite adelic unitary group, for classes c, c' and a
rational element γ. -/
def termPosition := (S.h c)⁻¹ * S.ratToFin γ * S.h c'

/-- The set of terms over (c, s, c'): rational γ such that h_c⁻¹ γ h_c' lies in K and has
reduction s. -/
def termsOver := {γ | ∃ k, S.reduction k = s ∧ k = S.termPosition c c' γ}

/-- The group 𝖴_c(g) of rational points u of the unipotent group 𝖴 with h_c⁻¹ u h_c ∈ K(g). -/
def classUnip : Subgroup (S.G E) :=
  besselU ⊓ (S.principalLevel.comap (MulAut.conj (S.h c)⁻¹)).comap S.ratToFin

/-- The subgroup 𝖴⁰_c(g) of the elements of 𝖴_c(g) that fix every frame vector. -/
def classUnip₀ := S.classUnip c ⊓ besselU0

/-- The number b^(2(ϱ+1)²), the size of the boxes. -/
def boxSize := S.b ^ (2 * 𝔰.n ^ 2)

/-- ω is measurable, at most 1, left invariant under 𝖴⁰ and H at infinity; ω(y) ≠ 0 and `InCut` at v
put y_v in `frameBox` `boxSize`; ∑_{γ∈𝖴_c(g)} a(γ)ω(γy) = 1 if a sums to 1 on each coset
𝖴⁰_c(g)γ. -/
def IsBoxPartition (ω : _ → ENNReal) := Measurable ω ∧
  (∀ y v, ω y ≠ 0 → InCut (y v) S.b → y v ∈ frameBox S.boxSize) ∧ (∀ y (a : S.classUnip c → _),
  (∀ γ, ∑' u : (S.classUnip₀ c).subgroupOf _, a (u.1 * γ) = 1) → ∑' γ, a γ * ω (S.ratToInf γ *
  y) = 1) ∧ (∀ y, ω y ≤ 1) ∧ ∀ s y, (∀ v, s v ∈ besselU0 ⊔ besselH) → ω (s * y) = ω y

/-- For y in G_∞ and a tuple i of indices, the product over infinite places v of the i_v-th
coordinate of the local Bessel function at y_v. -/
def besselFn (i : S.BesselCoord) := ∏ v, (S.besselSys v).W σ (y v) (i v)

/-- For rational γ and y in G_∞, the tensor W(y) ⊗ W(γ⁻¹y)^*, with coordinates W_i(y)
conj(W_j(γ⁻¹y)). -/
def besselKernel : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) :=
  .toLp 2 fun i ↦ S.besselFn y i.1 * star (S.besselFn ((S.ratToInf γ)⁻¹ * y) i.2)

/-- The number of classes times the number of index tuples of the Bessel systems: the dimension
of the space of columns. -/
def columnDim := card S.Classes * card S.BesselCoord

/-- The product over infinite places of the constants deg of the local Bessel systems. -/
def besselDegree := ∏ v, (S.besselSys v).deg

lemma besselDegree_pos : 0 < S.besselDegree := prod_pos fun _ _ ↦ (besselSys ..).deg_pos

/-- The real number 𝖽 = columnDim² / (besselDegree · mass), mass that of rank r. -/
def mainEnergy := S.columnDim ^ 2 / (S.besselDegree * mass E 𝔰.r)

/-- The number g^{fϱ(2k+2ϱ+1)}, f the number of infinite places of E; used as the order of the
reduction Ū of the integral points of the unipotent group 𝖴. -/
abbrev unipOrder := S.g ^ (numInfPlaces E * (𝔰.ϱ * (2 * 𝔰.k + 2 * 𝔰.ϱ + 1)))

/-- The constant a_* = |S̄| · g^(fϱ(2k + 2ϱ + 1)) · (number of classes) · c_*, with S̄ the image
in Gq of the Bessel subgroup, k = |κ|, f the number of infinite places. -/
def packetConst := Nat.card (S.reducedImage besselS) * S.unipOrder * card S.Classes * S.siegelConst

/-- The real number 𝖽₁ (or d₁) = |S̄| · `Filling.columnDim`,
where S̄ is the image of the Bessel subgroup S in
Gq. -/
def besselEnergy : ℝ := Nat.card (S.reducedImage besselS) * S.columnDim

/-- The real number τ = b^{kf/4}, with k = |κ| and f the number of infinite places of E. -/
def tailScale := S.b ^ (𝔰.k * numInfPlaces E / 4 : ℝ)

/-- The real number 2τ⁶/g^(kf), with τ = b^(kf/4), k = |κ| and f the number of infinite places
of E. -/
abbrev codimFactor := (S.b / S.g) ^ (𝔰.k * numInfPlaces E) * (2 * S.tailScale ^ 2)

/-- The standing hypotheses: Kc is the preimage of K(g), reduction K → Gq is onto, and size
inequalities hold between b, ϱ, k, the degree, the primes, N, ϖ, dimensions, an index and
the mass. -/
class IsAdmissible where
  columnLevel_eq : S.columnLevel = S.principalLevel.comap S.inclHFin
  reduction_surjective : Function.Surjective S.reduction
  ϖ_le v : ‖Φ v S.ϖ.val‖ ≤ S.b
  one_le_abs_kappa v : 1 ≤ |S.kappa v|
  abs_kappa_le v : |S.kappa v| ≤ S.b ^ 23
  N_le : S.N ≤ S.b ^ (60 * 𝔰.n)
  prod_band_le_inv_deg : ∏ v, 𝔰.bandConst * S.b ^ (7 * 𝔰.k) *
    (|S.kappa v| ^ (2 * 𝔰.ϱ + 1) / (S.g * S.N)) ^ (𝔰.k - 𝔰.n ^ 7) ≤ S.besselDegree⁻¹
  besselEnergy_le : S.tailScale ^ 44 * S.besselEnergy ≤ S.mainEnergy
  mainEnergy_le : S.tailScale ^ 18 * S.codimFactor * S.mainEnergy ≤ S.besselEnergy
  codimFactor_le_one : S.codimFactor ≤ 1
  card_besselCoord_le : card S.BesselCoord ≤ S.b ^ (2 * 𝔰.k * numInfPlaces E)
  le_relIndex : (S.N ^ 𝔰.k / S.b) ^ numInfPlaces E ≤
    (S.latStabilizer.comap S.inclHFin).relIndex (Kf E _)
  packetConst_mul_mass_le : S.packetConst ≤
    (1 + S.b⁻¹ ^ 9) * S.mainEnergy * S.besselDegree * 𝔰.openCellConst ^ numInfPlaces E /
    volÔ E ^ 𝔰.n * (S.unipCovolume * S.frameScaleProd / card S.BesselCoord) ^ 2

lemma adelicToInf_apply : (S.adelicToInf γ v).1 i j = (γ.1 i j).1 v *
  (S.basisScale v j / S.basisScale v i) := by simp! [adelicToInf, basisScaleGL, U.map, diagGL]

@[simp] lemma ratToInf_apply : (S.ratToInf γ v).1 i j =
  Φ v (γ.1 i j) * (S.basisScale v j / S.basisScale v i) := adelicToInf_apply ..

lemma coe_ratToFin : S.ratToFin γ = S.latBasis⁻¹ * .map (algebraMap E _) γ * S.latBasis := rfl

instance : Countable (S.G E) := Units.val_injective.injOn.injective.countable

/-- For a finite family f of basis indices and a compact set C, only finitely many points of C
have the form (submatrix on rows and columns f of the rescaled u at v)_v with u ∈ 𝖴_c(g). -/
lemma finite_classUnip_inter_compact {m} [Finite m] (f : m → _) {C} (hC : IsCompact C) : (C ∩ range
  fun (u : S.classUnip c) v ↦ (S.ratToInf u v).1.1.submatrix f f).Finite := .subset (.pi' fun v ↦
  .pi' fun i ↦ .pi' fun j ↦ (isCovolOneLattice_ratAdeles.finite_preimage ((hC.prod (isCompact_intGL
  isCompact_Ô)).image_auto fun p ↦ ((p.1 · i j) * (S.basisScale · (f i)) / (S.basisScale · (f j)),
  (S.latBasis * (S.h c).1 * p.2 / (S.latBasis * (S.h c).1) :) (f i) (f j)))).image (Φ v · * _))
  (by rintro _ ⟨h, ⟨u, _, k, _⟩, ⟨⟩⟩ v i j
      exact ⟨_, ⟨(_, _), ⟨h, k.2⟩, by aesop (add simp [coe_ratToFin, mul_assoc])⟩,
        (ratToInf_apply ..).symm⟩)

/-- The image of a subgroup K of 𝖴_c(g) at the infinite places is discrete and has a cutoff: a
measurable β with values in [0, ∞] and ∑_{u∈K} β(uy) = 1 for all y. -/
lemma exists_cutoff_classUnip {c}
  K : let Γ := Subgroup.map (S.ratToInf.domRestrict (S.classUnip c)) K; ∃ β, Measurable β
    ∧ (∀ y, ∑' u : K, β (S.ratToInf u * y) = 1) ∧ DiscreteTopology Γ ∧ IsCutoff (H := Γ) .count β :=
  have := Continuous.discrete_of_tendsto_cofinite_cocompact (by fun_prop)
    (tendsto_cofinite_cocompact_iff.2 fun _ ↦ .of_injOn (fun ⟨_, u, _, rfl⟩ ↦ (⟨·, u, rfl⟩))
    Units.val_injective.injOn.injective.comp_left.injOn.injective.injOn ∘
    S.finite_classUnip_inter_compact c id)
  (hasCutoff_count _).1.imp fun _ h ↦ ⟨h.1, ((((K.equivMapOfInjective _ fun _ ↦ by simp [funext_iff,
    ↓Subtype.ext_iff, ↓Units.ext_iff, ← ext_iff, (RingHom.injective _).eq_iff]).tsum_eq _).trans
  (lintegral_count _).symm).trans <| h.2 ·), this, h⟩

/-- The function β_c at the infinite places: a chosen cutoff for 𝖴⁰_c(g) times a chosen function
satisfying `Filling.IsBoxPartition` (arbitrary if there is none). -/
@[irreducible] def classCutoff := (S.exists_cutoff_classUnip
  ((S.classUnip₀ c).subgroupOf (S.classUnip c))).choose * epsilon (S.IsBoxPartition c)

/-- The amplitude of γ over the classes c, c': the integral over G_∞ of β_c(y) β_c'(γ⁻¹y) W(y) ⊗
W(γ⁻¹y)^*. -/
def amplitude := ∫ y,
  (S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y)).toReal • S.besselKernel γ y

/-- The integral over G_∞ of β_c(y) β_c'(γ⁻¹y) ‖W(y) ⊗ W(γ⁻¹y)^*‖, in [0, ∞], with β_c the
cutoffs `Filling.classCutoff` and W the full or cut Bessel function. -/
def amplitudeAbs := ∫⁻ y,
  S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y) * ‖S.besselKernel γ y‖ₑ

/-- The sum A_T(c, s, c') of the amplitudes of the elements of T that are terms over (c, s, c'). -/
def amplitudeSum := ∑' γ : ↥(T ∩ S.termsOver c s c'), S.amplitude c c' γ

lemma abs_kappa_eq : |S.kappa v| = S.g * ‖Φ v S.ϖ‖ / (2 * π) :=
  by simpa [abs_of_pos pi_pos] using congr(‖$(S.coe_kappa v)‖)

@[simp] lemma realFrameGram_ratToInf : ∀ a b, realFrameGram (S.ratToInf γ v) a b =
  ↑(S.kappa v ^ (𝔰.ϱ - a) * S.kappa v ^ (𝔰.ϱ - b) /
  S.N) * Φ v (S.frameProducts γ a b) := by simp [frameGram, mul_apply, basisScale, ← ofReal_pow]

lemma det_submatrix_realFrameGram_ratToInf {n} [Fintype n] (e : n → _) :
  ((realFrameGram (S.ratToInf γ v)).submatrix e e).det = (∏ a, delta% S.frameScaleSq v (e a)) * Φ v
  ((S.frameProducts γ).submatrix e e).det := by simp [det_apply, sq,
  mul_sum, mul_smul_comm, prod_pow_eq_pow_sum, Equiv.sum_comp _ (𝔰.ϱ - e ·)]

lemma unipCovolume_pos : 0 < S.unipCovolume := div_pos (by bound) S.frameScaleProd_pos

/-- The integer g = q₀q₁ as a unit of the finite adeles of E. -/
def gIdele : (𝔸f E)ˣ := .map (algebraMap E _).1 (.mk0 S.g (by simp))

/-- For u in the finite adelic unitary group, the number ψ_f(−σ(u)/gϖ), where σ(u) sums the
entries just above the diagonal in the frame block of u. -/
def unipotentChar (u : S.GFin) := S.selfDualChar (S.gIdele⁻¹ * simpleRootSum u)

/-- The element s of Gq agrees: integral u, u' ∈ 𝖴 with ū s = s ū' have the same value of
`Filling.unipotentChar`. -/
def Agrees := ∀ u u', u.1 ∈ besselU → u'.1 ∈ besselU → S.reduction u * s = s * S.reduction u' →
  S.unipotentChar u = S.unipotentChar u'

/-- A set T of rational elements is stable if u⁻¹γu' ∈ T for all γ ∈ T and all rational points
u, u' of 𝖴. -/
def IsStable := ∀ᵉ (u ∈ besselU) (u' ∈ besselU) (γ), u⁻¹ * γ * u' ∈ T ↔ γ ∈ T

/-- The set of rational elements γ of the unitary group with 𝗀(γ) ≠ 0 (`frameDisc`) and link
equal to Λ. -/
def termsOfLink Λ := {γ | S.termDisc γ ≠ 0 ∧ link γ = Λ}

export Filling.IsAdmissible (one_le_abs_kappa abs_kappa_le N_le codimFactor_le_one)
