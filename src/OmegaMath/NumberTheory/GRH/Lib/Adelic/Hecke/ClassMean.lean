import OmegaMath.NumberTheory.GRH.Lib.General.Measure.SubgroupIntegral
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Abstract Hecke operators of a pair (G,K), level eigenspaces and weighted class
sums. Here the operator of any function on finitely many cosets gK acts on any representation over
any commutative semiring, with no Hecke ring and no Haar measure. The same sums can therefore be
read in rings of integers and under field automorphisms. Source: G. Shimura, Introduction to the
Arithmetic Theory of Automorphic Functions (1971), ch. 3; B. Gross, Algebraic modular forms, Israel
J. Math. 113 (1999) 61-93; M. Greenberg and J. Voight, Lattice methods for algebraic modular forms
on classical groups, arXiv 1209.2460.

This file: Integral over double cosets as automorphism-weighted class sum; level change; smooth
vectors. -/

noncomputable section

open Pointwise Nat DoubleCoset Finset SetLike Function Classical MulAut Subgroup IsTopologicalGroup


variable {G W W' : Type*} [Group G]

/-- The subgroup of k in G with f(gk) = f(g) for all g. -/
def rightStab (f : G → W) : Subgroup G := ⟨⟨⟨{k | ∀ g, f (g * k) = f g}, by grind⟩, by simp⟩,
  by grind [inv_mul_cancel_right]⟩

@[simp] lemma mem_rightStab {f : G → W} {k} : k ∈ rightStab f ↔ ∀ g, f (g * k) = f g := .rfl

variable (Γ K K' : Subgroup G) [AddCommGroup W] [Module ℚ W] [AddCommGroup W'] [Module ℚ W']
  (f : G → W) [TopologicalSpace G]

/-- The integral of f over Γ\G with vol K = 1: the class sum at the level K' of elements of K
fixing f, divided by [K : K']. -/
def classIntegral := ((rightStab f).relIndex K : ℚ)⁻¹ • classSum Γ (rightStab f ⊓ K) f

/-- Finiteness for Γ and K in G: K is open and compact, Γ\G/K is finite, and every stabiliser Γ
∩ gKg⁻¹ is finite. -/
class HasFiniteType where
  finite_classes : Finite (@Quotient G _ Γ K)
  finite_aut g : Finite (classAut Γ K g)
  isOpen : @IsOpen G _ K
  isCompact : @IsCompact G _ K

scoped[HasFiniteType] attribute [instance] HasFiniteType.finite_classes HasFiniteType.finite_aut
  Fintype.ofFinite

scoped[decompGroup] attribute [instance] propDecidable

open HasFiniteType
attribute [local simp] map_rat_smul classSum.eq_1 le_def out_eq' mul_assoc mul_mem_cancel_right
  mul_mem_cancel_left classIntegral smul_smul smul_sum inf_relIndex_right

omit [TopologicalSpace G] in
lemma surjective_doubleCoset_mk_mul : Surjective fun x : DoubleCosets Γ K × _ ⧸ K'.subgroupOf K ↦
  mk Γ K' (x.1.out *
  x.2.out) := Quot.ind fun g ↦ (mk_out_eq_mul Γ K g).elim fun _ ⟨a, _, b, _⟩ ↦ ⟨(⟦g⟧, _), .symm
  ((eq ..).2 ⟨_, a, _, mem_subgroupOf.1 (QuotientGroup.eq.1 ⟦⟨_, b⟩⁻¹⟧.out_eq.symm), by aesop⟩)⟩

/-- The set of left Γ-invariant functions G → W whose stabiliser under right translation is open
in G. -/
def smoothInvariants := {f : G → W | Γ.FixesLeft f ∧ @IsOpen G _ (rightStab f)}

/-- Let u : Δ → G be injective with image containing Γ. The γ with u(γ) ∈ Γ and g⁻¹u(γ)h ∈ K
form a finite set, of cardinality #Aut(gK) if ΓgK = ΓhK and 0 otherwise (assuming
`HasFiniteType` Γ K). -/
lemma exists_transporter {Δ} {u : Δ → G} (i : Injective u := by exact injective_id) (E : ↑Γ ⊆
    Set.range u := by simp) K [HasFiniteType Γ K] g h : ∃ s, (∀ γ, γ ∈ s ↔ u γ ∈ Γ ∧
  g⁻¹ * u γ * h ∈ K) ∧ #s = if mk Γ K g = mk Γ K h then .card (classAut Γ K g) else 0 := by
  simp_rw [eq, card_eq_fintype_card]; split; choose a _ _ _ using ‹_›
  use ((univ.map ⟨_, (classAut Γ K g).subtype_injective⟩).map (Equiv.divRight a)).preimage u i.injOn
  simp_all [card_preimage, filter_eq_self.2, ← mul_assoc, Set.subset_def]
  aesop (add simp inv_mul_eq_iff_eq_mul.symm)

variable {Γ K K' f} (hl : Γ.FixesLeft f) (free : ∀ g, classAut Γ K g = ⊥) (hK : K ≤ rightStab f)

section

omit [TopologicalSpace G]

lemma card_classAut_out g : Nat.card (classAut Γ K g) = .card (classAut Γ K (mk Γ K g).out) := by
  choose γ _ _ _ using mk_out_eq_mul Γ K g; apply card_congr ((conj γ).subtypeEquiv _)
  simp_all; simp_all [← mul_assoc]

@[simp] lemma classIntegral_const_mul (β : ℂ) f : classIntegral Γ K (β * f ·) =
  β * classIntegral Γ K f := by by_cases β = 0 <;> simp [*, rightStab, mul_finsum]

include hK in
lemma classIntegral_eq_classSum : classIntegral Γ K f =
  classSum Γ K f := by simp [relIndex_eq_one.2 hK, inf_eq_right.2 hK]

include hl hK in
omit [AddCommGroup W] [Module ℚ W] in
lemma apply_doubleCoset_out g : f (mk Γ K g).out = f g := by grind [mk_out_eq_mul Γ K g, hK _ _]

end

variable [IsTopologicalGroup G] [H : HasFiniteType Γ K]

/-- The finiteness condition `HasFiniteType` for Γ and K (K open and compact, finitely many
double cosets, finite stabilisers) passes to every subgroup K' of K that is open in G. -/
lemma HasFiniteType.of_le (h : K' ≤ K) (o : @IsOpen G _ K') : HasFiniteType Γ K' := ⟨have :=
              (finite_of_card_ne_zero (H.4.relIndex_ne_zero o)); .of_surjective _
    (surjective_doubleCoset_mk_mul _ K _),
  (H.2 · |> Set.Finite.subset <| by aesop), o, H.4.of_isClosed_subset (isClosed_of_isOpen _ o) h⟩

variable [J : HasFiniteType Γ K'] (L : W →+ W')

include free in
omit [IsTopologicalGroup G] in
lemma card_classes_eq_classSum : (Nat.card (DoubleCosets Γ K) : ℝ) = classSum Γ K 1 := by aesop

include hK free in
omit [IsTopologicalGroup G] in
/-- If all stabilisers of points gK in Γ are trivial and f is right K-invariant with values in A,
the integral of f over Γ\G is a sum of elements of A, one for each double coset in Γ\G/K. -/
lemma classIntegral_mem_nsmul {A : Set W} (h : ∀ g, f g ∈ A) :
  classIntegral Γ K f ∈ Nat.card (DoubleCosets Γ K) • A := by
  simpa [↓classIntegral_eq_classSum hK, *] using Set.finsetSum_mem_finsetSum univ _ _ fun q _ ↦ h _

attribute [-simp] mem_classAut

/-- Assume `HasFiniteType` for K and K', and let L = a⁻¹K'a have finite index in K. If F(g) is
the value of f at the chosen representative of Γ(ga)K for all g, the class sum of F at K' is
[K : L] times that of f at K. -/
lemma classSum_eq_relIndex_smul {L F} (h : L ≤ K) a (e : K'.comap (conj a) = L) (o : ∀ g,
  f (mk Γ K (g * a)).out = F g) : classSum Γ K' F = (L.relIndex K : ℚ) • classSum Γ K f := by
  have := finite_of_card_ne_zero (H.4.relIndex_ne_zero (H := L)
    (e ▸ J.3.preimage (continuous_conj a)))
  choose T hT cT using exists_transporter Γ
  have e x y : #(T K y (x * a)) = ∑ q : K ⧸ L.subgroupOf K, #(T K' (y * q.out * a⁻¹) x) := by
    simp_rw [card_eq_sum_ones]; rw [← sum_comm' (t := ({q | q.out⁻¹ * y⁻¹ * · * (x * a) ∈ L}))]
    congr!; simp; lift y⁻¹ * (‹G› * (x * a)) to K using by grind with a; norm_cast
    simp [↓← mem_subgroupOf, ← QuotientGroup.eq, filter_eq']
    intro γ q; simpa [hT, ← e] using (fun _ ↦ @h (q.out⁻¹ * y⁻¹ * γ * x * a) ·)
  have q x : F x = classSum Γ K fun y ↦ (#(T K y (x * a)) : ℚ) • f y := by simp [*]
  simp [q, sum_comm, e, cT, ← sum_smul, mul_sum, mul_comm, relIndex,
    index, ↓card_classAut_out (_ * _)]

omit [IsTopologicalGroup G] in
lemma classSum_pos [PartialOrder W] [IsOrderedAddMonoid W] [PosSMulStrictMono ℚ W] (h : ∀ g, 0 ≤ f
  g) {c : DoubleCosets Γ K} (hc : 0 < f c.out) : 0 < classSum Γ K f := by
  simp_all [sum_pos_iff_of_nonneg, smul_nonneg]; use c; positivity

lemma classSum_one_of_le : K' ≤ K → classSum Γ K' 1 = (K'.relIndex K : ℝ) * classSum Γ K 1 :=
  (classSum_eq_relIndex_smul · 1 (by aesop) (by simp))

omit [IsTopologicalGroup G] in
lemma classSum_one_pos : (0 : ℝ) < classSum Γ K 1 := by simp; positivity

include hl in
lemma classIntegral_eq_classSum_mul a (h : K'.comap (conj a) ≤ rightStab f ⊓ K) (h' : K' ≤ K) :
    classIntegral Γ K f = (K'.relIndex K : ℚ)⁻¹ • classSum Γ K' (f <| · * a) := by
  rcases H.of_le (by simp) (isOpen_mono h (J.3.preimage (continuous_conj a))),
    (classSum_one_of_le (Γ := Γ) h').symm, classSum_one_pos (H := J).ne'
  simp_all [classSum_eq_relIndex_smul (f := f) h a rfl, apply_doubleCoset_out hl, -classSum.eq_1,
    field,
    classSum_eq_relIndex_smul (f := 1) h a rfl, classSum_one_of_le inf_le_right, Rat.smul_def]
  norm_cast at *; simp [*]

lemma classIntegral_eq_of_le (hl : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) (h : K' ≤ rightStab f) (h' : K' ≤
  K) : classIntegral Γ K f =
  (K'.relIndex K : ℚ)⁻¹ • classSum Γ K' f := by simp_all [↓classIntegral_eq_classSum_mul _ 1 _ h']

/-- Assume `HasFiniteType` for Γ and K. If F(g) = ∑_{i∈s} L_i(f_i(g a_i)) for all g, with L_i
additive, a_i ∈ G and f_i smooth and left Γ-invariant, then the integral of F over Γ\G is ∑_{i∈s}
L_i(integral of f_i). -/
lemma classIntegral_sum {ι F} s (L : ι → W →+ W') (a : ι → G) {f : ι → _} (hf : ∀ i,
  f i ∈ smoothInvariants Γ) (o : ∀ g, F g = ∑ i ∈ s, L i (f i (g * a i))) : classIntegral Γ K F =
  ∑ i ∈ s, L i (classIntegral Γ K (f i)) := by
  have := H.of_le (K' := K ⊓ ⨅ i : s, comap ↑(conj (a i)⁻¹) (rightStab (f i) ⊓ K)) inf_le_left
    (H.3.inter (coe_iInf.substr (isOpen_iInter_of_finite fun i ↦ ((hf i).2.inter H.3).preimage
    (continuous_conj _))))
  rw [classIntegral_eq_of_le (J := this)] <;> simp +contextual [o, s.sum_comm,
    (hf _).1, -map_inv, ↓fun i h ↦ classIntegral_eq_classSum_mul (J := this) (hf i).1 (a i)
    ((comap_mono (inf_le_of_right_le (iInf_le _ ⟨i, h⟩))).trans (by simp)) inf_le_left]
  grind [sum_congr, mul_inv_cancel_left]

lemma classIntegral_add {g} (h : f ∈ smoothInvariants Γ) (h' : g ∈ smoothInvariants Γ) :
  classIntegral Γ K (f + g) = classIntegral Γ K f +
  classIntegral Γ K g := by simp [↓classIntegral_sum univ (fun _ ↦ .id _) 1 (f := (cond · f g)), *]

lemma map_classIntegral {F} a (h : f ∈ smoothInvariants Γ := by simp [*]) (o : ∀ g, F g =
  L (f (g * a)) := by simp) : classIntegral Γ K F =
  L (classIntegral Γ K f) := by simp [↓classIntegral_sum {a} (fun _ ↦ L) id fun _ ↦ h, o]

variable (R) [CommSemiring R] [Module R W]

/-- The smooth functions G → W, those fixed under right translation by an open subgroup, as a
subrepresentation of the right regular representation. -/
def smoothFunctions : Subrepresentation (rightRegular R G W) := ⟨.ofLinearComb {f | @IsOpen G _
  (rightStab f)} ⟨0, by simp [rightStab]⟩ fun _ a _ b _ _ ↦ (rightStab _ ⊓ _).isOpen_mono (by aesop)
  (a.inter b), fun a _ h ↦ isOpen_of_one_mem_interior _ ⟨_, ⟨h.preimage (continuous_conj a⁻¹),
  fun _ ↦ (by simpa using · <| · * a)⟩, by simp⟩⟩
