/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Cartan/ProjectiveModules
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Cartan/ProjectiveModules
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Cartan.ProjectiveModules. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Cartan/ProjectiveModules.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology.DiscreteUnits
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Finiteness of the cokernel of the Cartan map, and Higman's criterion. It is stated
here for rational multiplicative functions on finite modules killed by a prime on which one element,
central modulo the level, fixes no nonzero vector, and projective is read as Higman's property. The
proof uses functions on two parallel affine hyperplanes, with no Brauer characters or Artin
induction. Source: J.-P. Serre, Linear Representations of Finite Groups (1977), Thm 35; for the
route by induction from cyclic subgroups in the local Euler characteristic formula, Milne,
Arithmetic Duality Theorems, I 2.10-2.12.

This file: Multiplicative function trivial on projective modules is trivial; Higman criterion,
dévissage. -/

namespace DiscreteModule

open MulAction Equiv QuotientGroup Finset Finite Submonoid Function commutatorElement Subgroup
  Module.End Fintype Fint
variable {R G : Type} [CommRing R] [Group G] [TopologicalSpace G] (l n : ℕ) [F : Fact l.Prime]
  (U : OpenNormalSubgroup G) (Q : Subgroup G) [i : Finite (G ⧸ Q)] (z : G) (m j : ℕ) (A :
  DiscreteModule R G)

/-- Higman's criterion relative to Q of finite index: some additive τ : A → A has ∑ gτg⁻¹ = 1,
summed over chosen representatives g of G/Q. -/
def IsHigmanProjective := ∃ τ : A →+ A, ∀ a, ∑ g : G ⧸ Q, A.ρ g.out (τ (A.ρ g.out⁻¹ a)) = a

/-- The condition that the subgroup Q of G acts trivially on A. -/
abbrev TrivialOn := ∀ g ∈ Q, ∀ m, A.ρ g m = m

/-- The G-module A is finite, killed by n, fixed by the subgroup Q, and the endomorphism z − m
of A (z in G, m a natural number) is injective. -/
def FiniteKilledFixedInj := Finite A ∧ (∀ a : A, n • a = 0) ∧ A.TrivialOn Q ∧ Injective ⇑(A.ρ z - m)

attribute [local simp] mul_smul QuotientGroup.eq compHom_smul_def TrivialOn

/-- For a finite set Y with an action of a discrete group Δ, the (G × Δ)-module of functions f :
Y → A, with ((g, δ)f)(x) = g f(δ⁻¹x). -/
abbrev permModule {Δ} [Group Δ] [TopologicalSpace Δ] [DiscreteTopology Δ] Y [Finite Y] [MulAction Δ
  Y] := of ⟨⟨fun g : G × Δ ↦ .pi fun x : Y ↦ A.ρ g.1 ∘ₗ .proj (g.2⁻¹ • x), by aesop⟩, by aesop⟩

variable {l n U Q i z m j A} (φ : ∀ A : DiscreteModule R G,
  FiniteKilledFixedInj l U.1.1 z 1 A → ℚ≥0)

lemma FiniteKilledFixedInj.of_isShortExact {B M ι π} (s : A.IsShortExact ι (π : Hom B M)) :
  B.FiniteKilledFixedInj n Q z m → A.FiniteKilledFixedInj n Q z m ∧ M.FiniteKilledFixedInj n Q z
  m := by refine s.rec fun r ⟨_, s⟩ ⟨_, _, _, t⟩ ↦ have := of_surjective _ s; ⟨⟨of_injective _
    r, ?_, ?_, fun a b e ↦ r (t ?_)⟩, this, ?_, ?_, injective_iff_surjective.2 ((s.comp
  t.bijective_of_finite.2).forall.2 (⟨π ·, ?_⟩))⟩ <;>
  simp_all [← r.eq_iff, ι.isIntertwining, s.forall, ← map_nsmul π n, ← π.isIntertwining]

/-- If A is finite, killed by n and fixed by Q, and the index of Q is prime to n, then A has
Higman's property `DiscreteModule.IsHigmanProjective` for Q. -/
lemma FiniteKilledFixedInj.isHigmanProjective_of_coprime (c : A.FiniteKilledFixedInj n Q z m) (h :
  n.Coprime Q.index) : A.IsHigmanProjective Q := have ⟨_, b, e⟩ := h.isCoprime
  ⟨b • .id _, (by simpa [add_smul, c.2, mul_comm b, index] using congr($e • ·))⟩

/-- Dévissage: for P normal, a property that holds for modules fixed by P and killed by l and is
stable under extensions holds for every finite l^j-torsion module on which each g in P has
some g^(l^i) acting trivially. -/
@[elab_as_elim] lemma devissage_induction (e : l ^ j = n) (P Q : Subgroup G) [P.Normal] {p : ∀ A :
  DiscreteModule R G, FiniteKilledFixedInj n Q z m A → Prop} (H : ∀ g ∈ P, ∃ i, g ^ l ^ i ∈ Q) (h :
  ∀ A c, FiniteKilledFixedInj l P z m A → p A c) (k : ∀ {A B C ι π} (s : IsShortExact ι π) c,
  p A (c.of_isShortExact s).1 → p C (c.of_isShortExact s).2 → p B c) : ∀ B c, p B c :=
  (invImage (Module.length R ·.V) inferInstance).2.fix fun B ih ⟨f, a, t, i⟩ ↦
  (IsPGroup.card_eq_or_dvd (G := Multiplicative B) (⟨j, e ▸ a ·⟩)).elim (h _ _ ⟨f,
  card_le_one_iff_subsingleton.1 ·.le |>.rec (by tauto)⟩) fun d ↦ (exists_prime_addOrderOf_dvd_card'
  (G := FixedPoints.addSubgroup (P.map B.ρ.toHomUnits) B) l (((IsPGroup.card_modEq_card_fixedPoints
  (fun ⟨_, g, h, rfl⟩ ↦ by peel H g h; ext; simp [*, ← map_pow]) B).dvd_iff dvd_rfl).1 d)).rec
  fun ⟨b, o⟩ e ↦ let W := (B.restrictTo P).H0 ⊓ (l • LinearMap.id).ker; k (B.isShortExact_submodule
    W fun g b ↦ .imp (B.ρ.le_comap_invariants _ g ·) (by simp_all [← map_nsmul])) _ ((fun c ↦
    h _ c (c.imp_right (by simp [W, ← SetLike.coe_eq_coe]; tauto))) _) (ih _ (W.length_quotient_lt
  (F.1.ne_one <| e ▸ by simpa using ·.le ⟨(o ⟨_, _, ·.2, rfl⟩), e ▸ by simp⟩)) _)

variable (R l U) [IsTopologicalGroup G] [CompactSpace G] (w : ∀ g, ⁅z, g⁆ ∈ U) (h : ∀ {A B D ι π}
  (s : IsShortExact ι π) c, φ B c = φ A (c.of_isShortExact s).1 * φ D (c.of_isShortExact s).2) (c :
  A.FiniteKilledFixedInj l U z 1) (k : ∀ {B} c, B.IsHigmanProjective U → φ B c = 1)

/-- Sylow's theorem for G/U: for a compact group G, an open normal subgroup U and a prime l,
some open subgroup P ⊇ U has index prime to l, and each g in P has g^(l^k) ∈ U for some k. -/
lemma exists_open_sylow : ∃ P : OpenSubgroup G, U.1.1 ≤ P ∧ l.Coprime P.1.index ∧
  ∀ g ∈ P, ∃ k, g ^ l ^ k ∈ U := have P : Sylow l _ := default
  ⟨⟨_, isOpen_mono (le_comap_mk' _ P.1) U.1.2⟩, le_comap_mk' .., by simp [P.not_dvd_index,
  index_comap, F.1.coprime_iff_not_dvd], (by simpa [Subtype.ext_iff, ← mk_pow] using! P.2 ⟨·, ·⟩)⟩

include w in
/-- Let z be central modulo U. Some normal S in Δ = G/U satisfies: for finite A killed by l,
fixed by U, with z − 1 injective, and finite Δ/S-sets Y, Fun(Y, A) keeps these properties,
and meets Higman's criterion for U if some Y → ℤ/l has trace 1 over Δ/S. -/
lemma exists_permModule_isHigmanProjective : ∃ S : Subgroup (G ⧸ U.1.1), ∃ _ : S.Normal,
  ∀ {A : DiscreteModule R G}, A.FiniteKilledFixedInj l U z 1 →
  ∀ Y [Finite Y] [MulAction (_ ⧸ S) Y], let := compHom Y (mk' S)
  let B :=
    (A.permModule Y).restrictAlong ⟨.prod (.id G) (mk' U.1), .prodMk continuous_id continuous_mk⟩
  B.FiniteKilledFixedInj l U z 1 ∧ ∀ a : Y → ZMod l, (∀ y, ∑ g : _ ⧸ S, a (g⁻¹ • y) = 1) →
    B.IsHigmanProjective U :=
  have ⟨j, n, _⟩ := WfDvdMonoid.max_power_factor (orderOf_pos (@mk _ _ U z)).ne' F.1
  let S := zpowers (↑z ^ l ^ j)
  have : S.Normal := ⟨by
    rintro _ ⟨i, rfl⟩ ⟨g⟩; use i, eq_mul_inv_of_mul_eq (((commutatorElement_eq_one_iff_commute.1
    ((eq_one_iff _).2 (w g))).pow_left _).zpow_left i)⟩; ⟨S, this, by
  intro A ⟨_, c, t, i⟩ Y _ _ _ B
  obtain ⟨⟩ := AddCommGroup.zmodModule c, (Commute.one_right (A.ρ z - 1)).add_pow_prime_pow_eq F.1 j
  refine ⟨⟨Pi.finite, ?_, ?_, .of_ker _ fun a e ↦ (fun _ ↦ funext fun y ↦ iterate_injective i
    (l ^ j) (a₂ := 0) ?_) (((stabilizerSubmonoid _ a).comap B.ρ).pow_mem (x := z) (by simp_all) (l
    ^ j))⟩, fun a e ↦ ⟨.pi ((a · / n) • Pi.evalAddMonoidHom _), fun _ ↦ funext fun y ↦ ?_⟩⟩
  iterate 3 simp_all [B, funext_iff, (eq_one_iff _).2, S] <;> tauto
  simp [B, ZMod.map_smul, ← sum_smul, ← sum_div]
  erw [S.groupEquivQuotientProdSubgroup.sum_comp (a <| ·.1⁻¹ • y)]
  simp [S, sum_prod_type_right, card_zpowers, orderOf_pow, ZMod.natCast_eq_zero_iff, F.1.pos, *]⟩

/-- Let f, from finite Δ-sets (Δ finite) to ℚ≥0, be 1 on empty sets, with f(Y) = f(Y − Δy)
f(Δ/Stab y). If X has a fixed point and f(X × Δ/K) = 1 for all subgroups K, then f(Δ/K) = 1
for all K. -/
lemma eq_one_of_prod_quotient.{u, v} (Δ : Type (max u v)) {X : Type v} [Group Δ] [Finite Δ]
  [Finite X] [MulAction Δ X] (f : ∀ (Y : Type (max u v)) [Finite Y] [MulAction Δ Y], ℚ≥0)
  (x : fixedPoints Δ X) (h : ∀ Y
  [Finite Y] [MulAction Δ Y], (IsEmpty Y → f Y = 1) ∧ ∀ y : Y, f Y = f ↥(SubMulAction.mk (orbit Δ y)
  (mem_orbit_of_mem_orbit ·))ᶜ * f (Δ ⧸ stabilizer Δ y)) (H : ∀ K : Subgroup Δ, f (X × Δ ⧸ K) = 1) :
  ∀ K : Subgroup Δ, f (Δ ⧸ K) = 1 := WellFoundedLT.fix fun K ih ↦ by
  rw [← pow_eq_one_iff_left, ← H, (h (X × Δ ⧸ K)).2 (x, ⟦1⟧), pow_succ, (by aesop :
  stabilizer Δ _ = K), ← (((measure _).2.fix fun Y r _ _ p ↦ (isEmpty_or_nonempty Y).elim
  (fun _ ↦ by simp [h]) fun ⟨y⟩ ↦ (p
  y).exists_rep.rec fun g e ↦ (h _).2 (g⁻¹ • y) ▸ mul_mem (r _ (card_subtype_lt (by tauto)) ⟨(p ·),
  by simp⟩) ((eq_or_lt_of_le (b := K) fun _ a ↦ by simpa [← e] using congr(p $a)).elim (· ▸
  mem_powers _) (by simp [ih, ·])) : ∀ Y [Finite Y] [MulAction Δ Y], (Y →[Δ] Δ ⧸ K) → f Y ∈ powers
  (f (Δ ⧸ K))) (Subtype _) ⟨(·.1.2), by simp⟩).choose_spec]; simp

include h k w

/-- Let l be prime, U open normal in the compact group G, z central modulo U, and φ, with values in
ℚ≥0, multiplicative in short exact sequences of finite l-torsion modules fixed by U on which z − 1
is injective. If φ = 1 on those with Higman's property, then φ = 1 on all.

Known result: The Cartan map has finite cokernel; Higman's criterion. -/
lemma IsMultiplicative.eq_one_of_isHigmanProjective :
  φ A c = 1 := have ⟨S, _, P⟩ := exists_permModule_isHigmanProjective R l U w; by
    have I {A B a b} (u : (ρ A).Equiv (ρ B)) : φ A a = φ B b := by simp [@h (of (V := Unit)
      1) _ _ 0 _ ⟨by tauto, by aesop_cat, u.surjective⟩, k _ ⟨0, _⟩]
    let Δ := _ ⧸ S
    let Λ := AddMonoidHom.mk' _ (@sum_add_distrib Δ (ZMod l) univ _)
    let := @arrowAction Δ
    let act e := (Λ.fiberEquivKer e).symm.mulAction Δ (β := SubMulAction.mk _ fun g a ↦
      (sum_comp (.mulLeft g⁻¹) (a ·)).trans)
    let := act 0
    obtain ⟨⟨⟩, _⟩ := PSigma.mk _ (discreteTopology_bot (Perm Λ.ker)), @Unique.mk' (Δ ⧸ ⊤) _
      subsingleton_quotient_top
    let H : Subgroup (G × Perm Λ.ker) := ⟨⟨⟨{p | ∀ y z, (p.2 y).1 - p.2 z = (p.1 : Δ) • (y -
      z)}, by simp_all [-Subtype.forall]⟩, by simp⟩, (by simp [eq_inv_smul_iff, ← · _])⟩
    let s e : G →ₜ* H := .mk (.mk' (fun g ↦ ⟨(g, (act e).toPerm ↑↑g), fun _ _ ↦
      by (repeat erw [add_sub_add_left_eq_sub]); rfl⟩) (by simp [← toPermHom_apply]))
    have tw e B a : ∀ b, φ (restrictAlong B (s 0)) a = φ (restrictAlong B (s e)) b :=
      devissage_induction (z := 1) (m := 0) l.pow_one
      ((MonoidHom.fst ..).domRestrict H).ker ⊥ (fun g (a : g.1.1 = 1) ↦ ⟨1, by
      ext <;> simp [a, congr($(ext (g := .addLeft (g.1.2 0)) (by simpa [a, Subtype.ext_iff,
        sub_eq_iff_eq_add'] using (g.2 · 0))) ^ l)]⟩) (fun B _ t _ _ ↦ I (.mk 1 fun g ↦ B.ρ.eq_iff.2
      (LinearMap.ext (t.2.2.1 _ (inv_mul_cancel g))))) (fun S ↦ by simp_all [h (S.restrictAlong _),
      FiniteKilledFixedInj.of_isShortExact (S.restrictAlong _)]) B (a.imp_right (by simp; tauto)) a
    exact .trans (I (.mk (.symm (.funUnique ..)) (by tauto))) (eq_one_of_prod_quotient Δ (fun Y ↦
      φ _ (P c Y).1) ⟨0, fun _ ↦ one_smul Δ 0⟩ (fun Y ↦ ⟨fun _ ↦ k _ ⟨0, by simp [funext_iff]⟩,
      fun y ↦ let E := .funCongrLeft R A (((orbitEquivQuotientStabilizer ..).symm.sumCongr
      (.refl _)).trans (sumCompl _)) ≪≫ₗ .sumArrowLequivProdArrow ..; @h _ _ _ ⟨_, by
      intro; ext _ _ x; by_cases orbit Δ x = orbit Δ y <;> simp [← orbit_eq_iff, *]; rfl⟩ ⟨_, by
      simp [DFunLike.ext_iff, funext_iff, forall_mk]⟩
        ⟨E.symm.injective.comp LinearMap.inr_injective,
      (E.conj_symm_exact_iff_exact ..).2 .inr_fst, Prod.fst_surjective.comp E.surjective⟩ _⟩)
      (fun K ↦ have C e := @P _ (P c _).1 _ _ (act e); .trans (I (b := (C 0).1) (.mk (.curry ..)
      (by tauto))) ((tw _ ((permModule ..).restrictTo H) _ _).trans (k (C _).1 ((C (Pi.single 1
        1)).2 (·.1 1 + 1) fun ⟨_, _⟩ ↦ by (repeat erw [sum_add_distrib]); simpa [Δ])))) ⊤)
