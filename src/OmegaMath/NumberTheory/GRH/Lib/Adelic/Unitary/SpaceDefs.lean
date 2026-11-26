import OmegaMath.NumberTheory.GRH.Lib.General.Measure.SubgroupIntegral
import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.AdditiveCharDefs
import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.ValuedMatrix
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Adelic points of unitary groups, levels and Haar measures (known result; see
Lib.Adelic.Reduction.MinkowskiSecond).

This file: Adelic unitary groups, split places, compact levels, framed hermitian spaces, lattices,
masses. -/

noncomputable section

open NumberField MeasureTheory Measure Matrix GeneralLinearGroup WithZero Filter Valued


section

variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] (w : FinPlace E)

lemma matrix_ext_evalAt {m n} {M N : Matrix m n (𝔸f E)} (h : ∀ u, M.map (evalAt u) =
  N.map (evalAt u)) : M = N := by ext; simp_all [← ext_iff]

/-- The ring homomorphism 𝔸 → ℂ taking an adele of E to its component at the infinite place v. -/
@[simps!] def evalInf (v : InfinitePlace E) : 𝔸 E →+* ℂ := (Pi.evalRingHom _ v).comp (.fst ..)

lemma matrix_ext_𝔸 {m n} {M N : Matrix m n (𝔸 E)} (h₁ : ∀ w, M.map (evalInf w) = N.map (evalInf w))
  (h₂ : M.map (RingHom.snd ..) = N.map (RingHom.snd ..)) : M = N := by ext <;> simp_all [← ext_iff]

/-- The homomorphism sending g in GL_n(E_w) to the element of GL_n(𝔸_f) with component g at w
and 1 at the other places. -/
def locGL : GL n (LocField w) →* GL n (𝔸f E) := Units.map ⟨⟨fun g ↦ 1 + (g - 1).map (singleAdele
  w), by simp⟩, by noncomm_ring [← Matrix.map_mul, ← Matrix.map_add, map_add, implies_true]⟩

@[simp] lemma evalAt_locGL g : (locGL w g : GL n _).map (evalAt w) = g := by
  ext : 2; simp [locGL, -evalAt_apply]; simp

@[simp] lemma evalAt_locGL_of_ne {u w : FinPlace E} (h : u ≠ w) (g : GL n _) :
  (locGL w g).map (evalAt u) = 1 := by ext; simp [locGL, -evalAt_apply]; aesop

lemma GL_ext_evalAt {a b : GL n (𝔸f E)} (h : ∀ u, a.map (evalAt u) = b.map (evalAt u)) : a = b :=
  Units.ext (matrix_ext_evalAt (congr($(h ·))))

variable {R : Type _} [CommRing R] [TopologicalSpace R] {O : Subring R}

lemma isOpen_intGL (h : @IsOpen R _ O) : (intGL n O).IsOpen :=
  Eq.subst (by ext; exact mem_intGL.symm) (O.matrix.isOpen_units h.matrix)

variable [IsTopologicalRing R]

lemma isCompact_intGL [T2Space R] (h : @IsCompact R _ O) : IsCompact (SetLike.coe (intGL n O)) :=
  Eq.subst (by ext; exact mem_intGL.symm) (O.matrix.units_isCompact h.matrix)

/-- If the subring O and the O-submodule M are open in the topological ring R, the group of
matrices in GL_n(O) whose rows e(i), finitely many, are congruent to those of 1 modulo M is
open in GL_n(R). -/
lemma isOpen_congruenceGL {m} {e : m → n} [Finite m] {M : Submodule O R} (h : @IsOpen R _ O) (k :
  @IsOpen R _ M) : (congruenceGL M e).IsOpen := (isOpen_intGL h).and k.matrix.preimage_of_continuous

/-- If the O-submodules M_i of R shrink to 0 along a filter, then the principal congruence
subgroups of level M_i eventually lie in any given neighbourhood of 1 in GL_n(R). -/
lemma eventually_congruenceGL_subset {ι l s} {M : ι → Submodule O R} (h : @Tendsto _ (Set R) (M ·) l
  (nhds 0).smallSets) (k : s ∈ nhds (1 : GL n R)) : ∀ᶠ i in l, ∀ g ∈ congruenceGL (M i) id, g ∈ s :=
  have H : (l.bind fun i ↦ 𝓟 (congruenceGL (M i) id).carrier).Tendsto (·.1) (nhds 1) :=
    tendsto_sub_nhds_zero_iff.1 (tendsto_pi_nhds.2 fun _ ↦ tendsto_pi_nhds.2 fun _ _ u ↦
    l.3 (h (mem_lift' u)) fun _ a _ b ↦ a (b.2 ..))
  (H.prodMk_nhds fun _ u ↦ l.3 (H (MulOpposite.continuous_op.tendsto _ u))
    fun _ a ↦ (@a ·⁻¹ ∘ by simp)).le_comap ((nhds_induced ..).ge k)

variable (n)

/-- For a finite place w of E, the subgroup GL_n(O_w) of GL_n(E_w) of matrices that, with their
inverses, have entries in the local integers. -/
abbrev Kw : Subgroup (GL n (LocField w)) := intGL n (LocInt w).1

/-- The g in GL_n(E_w) with g and ϖg⁻¹ integral and det g of order j (ϖ a uniformiser); for j ≤
n, the GL_n(O_w)-double coset of diag(ϖ1_j, 1). -/
def basicDoubleCoset (j : ℕ) := {g : GL n (LocField w) | (∀ a b, v (g a b) ≤ 1) ∧
  (∀ a b, v (g⁻¹ a b) ≤ exp 1) ∧ v g.1.det = exp (-↑j)}

variable (E) [IsCMField E]

/-- The finite adelic unitary group G_f: matrices g in GL_n(𝔸_f) with gᴴg = 1. -/
@[instance_reducible] def Gf := ↥(U (1 : Matrix n n (𝔸f E)))
  deriving Group, TopologicalSpace, MeasurableSpace, DistribMulAction _ (n → 𝔸f E), PolishSpace,
  CoeOut _ (GL n (𝔸f E)), CoeOut _ (Matrix n n (𝔸f E)), SecondCountableTopology

instance : ContinuousSMul (Gf E n) (n → 𝔸f E) := ⟨.matrix_mulVec (by fun_prop) continuous_snd⟩

variable [IsEmpty n] in
deriving instance Subsingleton for Gf E n

@[simp] lemma Gf.coe_mul (g k : Gf E n) : (g * k).1 = g.1 * k.1 := rfl

@[simp] lemma Gf.coe_mul' (g : Gf E n) (k : U 1) : (g * k).1 = g.1 * k.1 := rfl

@[simp] lemma Gf.coe_inv (g : Gf E n) : g⁻¹.1 = g.1⁻¹ := rfl

@[simp] lemma Gf.coe_one : (1 : Gf E n).1 = 1 := rfl

@[simp] lemma Gf.subtype_apply g : DFunLike.coe (F := Gf E n →* _) (U 1).subtype g = g.1 := rfl

@[simp] lemma Gf.codRestrict_apply {M} [Monoid M] (f : M →* _) h x :
  DFunLike.coe (F := M →* Gf E n) (f.codRestrict (U 1) h) x = ⟨f x, h x⟩ := rfl

@[ext] lemma Gf.val_ext {g k : Gf E n} : g.1 = k → g = k := by simp

/-- The subgroup K_0 = G_f ∩ GL_n(Ô) of the finite adelic unitary group, the stabiliser of the
standard lattice Ô^n. -/
def Kf : Subgroup (Gf E n) := (intGL n (Ô E)).subgroupOf _

variable {n} (s : n → ℤˣ)

/-- The archimedean unitary group G_∞ for signs s: one copy of the complex unitary group U(diag
s) for each infinite place of E. -/
abbrev GInf := InfinitePlace E → USign s

/-- The adelic unitary group G = G_∞ × G_f for signs s at the infinite places and the identity
matrix at the finite places. -/
abbrev G := GInf E s × Gf E n

/-- A finite point as an adelic point. -/
instance : Coe (Gf E n) (G E s) := ⟨(1, ·)⟩

/-- The diagonal adelic matrix that is diag(s) at every infinite place and the identity at the
finite places. -/
def stdForm := diagonal (α := 𝔸 E) fun i ↦ (fun _ ↦ s i, 1)

variable {E s} {u w : FinPlace E} (hw : w.IsSplit)

/-- The function F on G = G_∞ × G_f has level K ⊂ G_f: F(g·(1, k)) = F(g) for all k ∈ K and g ∈
G. -/
@[simp] abbrev HasLevel {W S} [Membership _ S] (F : G E s → W) (K : S) :=
  ∀ k ∈ K, ∀ g, F (g * (1, k)) = F g

/-- The j-th Hecke operator on a representation π of GL_n(E_w): the action (`heckeFun`) of
the indicator function of `basicDoubleCoset` j, for K = GL_n(O_w). -/
def heckeGL {A W} [CommSemiring A] [AddCommMonoid W] [Module A W] (π : Representation A
  (GL n (LocField w)) W) j := heckeFun π (Kw ..) ((basicDoubleCoset n w j).indicator 1)

lemma evalAt_star_GL h (g : GL n _) : (map (evalAt w) (star g)).1 =
  ((map (evalAt u) g).1.map (conjLoc h))ᵀ := by ext1; apply adeleMap_apply

@[local simp] lemma evalAt_star_locGL (h : star u ≠ w) (g : GL n _) :
    (star (locGL w g)).map (evalAt u) = 1 := by ext1; simp_all [evalAt_star_GL (star_star u)]

/-- The homomorphism G_f → GL_n(E_w) sending an element to its component at w. -/
def Gf.atPlace (w : FinPlace E) : Gf E n →* GL n (LocField w) :=
  .comp (map (evalAt w)) (U 1).subtype

/-- For a split place w, the homomorphism GL_n(E_w) → G_f sending g to the unitary element with
component g at w and 1 off w, w̄. -/
def atSplit : GL n (LocField w) →* Gf E n := by
  refine .mk' (fun g ↦ ⟨locGL w g * star (locGL w g⁻¹), Units.ext_iff.1 (?_ : star (_ : GL n _) *
    1 * _ = 1)⟩) fun _ _ ↦ Subtype.ext ?_ <;> exact GL_ext_evalAt (by by_cases · = w <;> aesop)

/-- For a split finite place w (w̄ ≠ w) and g in GL_n(E_w), the element of G_f attached to g by
`atSplit` has component g at w. -/
@[simp] lemma atPlace_atSplit (g : GL n _) : (atSplit hw g).atPlace w =
  g := by simp_all [Gf.atPlace, atSplit]

variable (n) (S : Set (FinPlace E))

/-- For a ring homomorphism f from the integral finite adeles to S, the homomorphism K_0 →
GL_n(S) applying f to each entry. -/
def Kf.map {S} [CommRing S] (f : Ô E →+* S) : Kf E n →* GL n S :=
  (intGL.map f).comp ((U 1).subtype.subgroupComap _)

/-- The subgroup of G_f of elements supported on S ∪ S̄, that is, with component 1 at every
place outside S ∪ S̄. -/
def Gf.supportedOn := ⨅ w, ⨅ _ : w ∉ S ∧ star w ∉ S, (atPlace (n := n) w).ker

/-- The subgroup of G_f of elements whose component at each place w in S lies in K w; by default
K w is GL_n(O_w). -/
def localLevel (K := fun w : FinPlace E ↦ Kw n w) : Subgroup (Gf E n) := by
  use! {g | ∀ w ∈ S, g.atPlace w ∈ K w} <;> simp_all [mul_mem]

/-- The subgroup of G_f of elements with component 1 at every place in S (hence, being unitary,
also at the conjugate places). -/
def Gf.trivialOn := ⨅ w ∈ S, (atPlace (n := n) w).ker

variable {n S} (w) (g k : G E s) {K : Subgroup (Gf E n)}

/-- Reduction modulo w: the homomorphism from K_0 = G_f ∩ GL_n(Ô) to GL_n of the residue field
at w. -/
def Kf.reduceAt := map n (_root_.reduceAt w)

lemma mem_localLevel {K g} : g ∈ localLevel n S K ↔ ∀ w ∈ S, g.atPlace w ∈ K w := .rfl

lemma mem_Kf {g} : g ∈ Kf E n ↔ ∀ i j, g.1 i j ∈ Ô E :=
  mem_intGL.trans (U.inv_val_eq_conjTranspose g ▸ by simp_all [star_mem_Ô])

lemma isOpen_Kf : (Kf E n).IsOpen := (isOpen_intGL isOpen_Ô).preimage_val

/-- Known result: Adelic points of unitary groups, levels and Haar measures. -/
lemma isCompact_Kf : IsCompact (SetLike.coe (Kf E n)) :=
  (isCompact_intGL isCompact_Ô).preimage_val (isClosed_U _)

/-- The subgroup K of the finite adelic unitary group G_f is a level: it is open and contained
in K_0 = G_f ∩ GL_n(Ô). -/
class IsLevel K where
  le : K ≤ Kf E n
  isOpen : K.IsOpen

instance : IsLevel (Kf E n) := ⟨le_rfl, isOpen_Kf⟩

/-- For a subgroup K of G_f, the index [K₀ : K ∩ K₀], where K₀ = `Kf`; it is 0 if the index
is infinite. -/
abbrev stdLevelIndex K := Subgroup.relIndex K (Kf E n)

/-- The element of GL_n(𝔸) with components a_w in GL_n(ℂ) at the infinite places and finite part
b. -/
@[simps! apply_val] def mkAdelicGL : (InfinitePlace E → GL n ℂ) × GL n (𝔸f E) →* GL n (𝔸 E) :=
  .toHomUnits (by use! fun g ↦ of fun i j ↦ ((g.1 · i j), g.2 i j) <;>
    simp_all [entrywise, ← prod_mk_sum, funext_iff, apply_ite])

/-- The isomorphism from G = G_∞ × G_f to the unitary group over the adeles of the standard form
`stdForm`. -/
def G.toUnitary : G E s ≃* U (stdForm E s) where
  toFun g := ⟨mkAdelicGL (_, g.2), by apply matrix_ext_𝔸 <;> simp [stdForm,
          ↓Matrix.map_mul, -mul_one, -Matrix.mul_one]; exacts [(g.1 · |>.2), g.2.2]⟩
  invFun g := by refine (fun w ↦ U.map (evalInf w) ?_ ?_ g, U.map (.snd ..) ?_ ?_ g) <;>
    simp [stdForm, signMatrix]
  map_mul' _ _ := Subtype.ext (.symm (map_mul ..).symm)

/-- The n×n matrix over the adeles of an element g of the adelic unitary group G. -/
@[local simp] def G.mat := g.toUnitary.1.1

@[simp] lemma G.mat_fst i j w : (g.mat i j).1 w = (g.1 w).1 i j := rfl

@[simp] lemma G.mat_snd i j : (g.mat i j).2 = g.2.1 i j := rfl

@[simp] lemma G.mat_one : mat (1 : G E s) = 1 := by simp

@[simp] lemma G.mat_mul : (g * k).mat = g.mat * k.mat := by simp

@[fun_prop] lemma G.continuous_mat : Continuous (mat : G E s → _) := by
  simp +unfoldPartialApp [toUnitary, mkAdelicGL]; fun_prop

instance : PolishSpace (GL n (𝔸f E)) where

deriving instance LocallyCompactSpace, BorelSpace, IsTopologicalGroup for Gf E n, G E s

lemma IsLevel.isCompact [h : IsLevel K] : IsCompact K.carrier :=
  isCompact_Kf.of_isClosed_subset (K.isClosed_of_isOpen h.2) h.1

instance [h : IsLevel K] : CompactSpace K := h.isCompact.compactSpace

/-- The Haar measure that gives `Kf` mass one. -/
instance : MeasureSpace (Gf E n) :=
  ⟨haarMeasure ⟨⟨_, isCompact_Kf⟩, by simp [isOpen_Kf.interior_eq]⟩⟩

instance : (@volume (Gf E n) _).IsHaarMeasure := isHaarMeasure_haarMeasure _

/-- For the chosen Haar measure on the finite adelic unitary group G_f, the subgroup K_0 = G_f ∩
GL_n(Ô) has volume 1. -/
@[simp] lemma volume_Kf : volume (SetLike.coe (Kf E n)) = 1 := haarMeasure_self

end

attribute [local simp] evalAt_star_locGL

attribute [local simp] G.mat

variable (E : Type*) [Field E] [CMType E] {n : Type*} [Fintype n] {s : n → ℤˣ}

/-- A hermitian space with a point: a matrix J over E and x in GL_n(𝔸) with xᴴJx equal to
diag(s) at the infinite places and 1 at the finite places. -/
structure Space n [Fintype n] s where
  J : Matrix n n E
  x : GL n (𝔸 E)
  gram_point : x.1ᴴ * J.map toAdele * x.1 = stdForm E s

namespace Space

variable {E} (V : Space E n s)

/-- For a space (J, x), the isomorphism g ↦ x g x⁻¹ from G to the adelic unitary group U(J)(𝔸). -/
def toRatCoords := G.toUnitary.trans (U.conj _ V.gram_point)

/-- For a space (J, x), the homomorphism γ ↦ x⁻¹ γ x from the rational unitary group U(J)(E) to
G. -/
def ratEmbed := V.toRatCoords.symm.toMonoidHom.comp (U.map _ (by simp) rfl)

/-- For a space (J, x), the homomorphism U(J)(E) → G_f sending γ to the finite part of x^{-1} γ
x. -/
def embFin := (MonoidHom.snd ..).comp V.ratEmbed

/-- For a space (J, x), the subgroup x^{-1} U(J)(E) x of G, the image of the rational unitary
group. -/
def Γ := V.ratEmbed.range

/-- For a space (J, x), the subgroup of G_f formed by the finite parts of the elements x^{-1} γ
x, γ in U(J)(E). -/
abbrev Γf := V.embFin.range

/-- For a space (J, x), the adelic vector x⁻¹y attached to a rational vector y in E^n. -/
def vecAtPoint :=
  V.x⁻¹.1.mulVecLin ∘ₛₗ .mk (σ := toAdele) ⟨(toAdele ∘ ·), by simp⟩ (by simp [funext_iff])

/-- For a space V = (J, x), the lattice E^n ∩ x_f Ô^n of rational vectors y with x⁻¹y integral
at all finite places, as an additive subgroup. -/
def baseLattice :
  AddSubgroup (n → E) := by use! {y | ∀ i, (V.vecAtPoint y i).2 ∈ Ô E} <;> simp_all [add_mem]

end Space

variable (n)

/-- The definite space I_n with J = 1 and x = 1: the sum of n norms with its standard lattice. -/
@[simps] def stdSpace : Space E n 1 := ⟨1, 1, by simp [stdForm]; rfl⟩

/-- The mass of the genus of O_E^l: the sum of 1/#Aut over the classes Γ\G_f/K_0 for the space
I_l. -/
def mass l := (classSum (stdSpace E (Fin l)).Γf (Kf ..) 1 : ℝ)

variable {E n}

/-- The homomorphism U_n(E) → G_f sending a matrix γ over E with γᴴγ = 1 to its image over the
finite adeles. -/
abbrev stdEmbFin := (stdSpace E n).embFin

/-- The image of U_n(E), the matrices γ over E with γᴴγ = 1, in the finite adelic unitary group
G_f. -/
abbrev stdRatPoints := (stdSpace E n).Γf
