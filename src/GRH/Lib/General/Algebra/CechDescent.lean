import GRH.Lib.General.Algebra.TangentNakayama
import GRH.Lib.Cohomology.Hodge.WitnessCocycles
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Long exact sequences of abelian groups, their morphisms and the shift. Long exact Ext
sequences, four and five lemmas for ladders. Dévissage for maps of delta-functors; Čech descent of
bijectivity, step by step. -/

/-- A long exact sequence 0 → A 0 → B 0 → C 0 → A 1 → … -/
structure LongExactSeq.{u} where
  {A B C : ℕ → Ab.{u}} f n : A n →+ B n
  g n : B n →+ C n
  δ n : C n →+ A (n + 1)
  injective_f : Function.Injective (f 0)
  exact_f_g n : Function.Exact (f n) (g n)
  exact_g_delta n : Function.Exact (g n) (δ n)
  exact_delta_f n : Function.Exact (δ n) (f _)

/-- A morphism of long exact sequences L → L': additive maps on all terms, commuting with the
maps f, g and the connecting maps δ. -/
structure LongExactSeq.Hom (L L' : LongExactSeq) (a : ∀ n, L.A n →+ L'.A n) (b : ∀ n,
  L.B n →+ L'.B n) (c : ∀ n, L.C n →+ L'.C n) where
  comm_f n x : b n (L.f n x) = L'.f n (a n x)
  comm_g n x : c n (L.g n x) = L'.g n (b n x)
  comm_delta n x : a _ (L.δ n x) = L'.δ n (c n x)

/-- The sequence L moved by one place, 0 → 0 → A⁰ → B⁰ → C⁰ → ⋯: its terms in degree n are
C^(n-1), Aⁿ, Bⁿ, with C^(-1) = 0. -/
abbrev LongExactSeq.rotate (L : LongExactSeq) := @mk (·.casesOn (.of PUnit) L.C) _ _
  (·.casesOn 0 L.δ) _ _ (by tauto) (·.casesOn (by simp [Function.Exact, ← L.injective_f.eq_iff,
  eq_comm]) L.exact_delta_f) L.exact_f_g L.exact_g_delta

lemma LongExactSeq.Hom.rotate {L L' a b c} (h : Hom L L' a b c) : L.rotate.Hom L'.rotate
  (·.casesOn 0 c) a b := ⟨(·.casesOn (by simp) h.comm_delta), h.comm_f, h.comm_g⟩

open CategoryTheory Function LongExactSeq Abelian.Ext
variable {A B A' B' : ℕ → Type*} {f : ∀ n, A n → B n} {r C C'} [Category C] [Category C']
  {F N F' n N' L L'} {S : ShortComplex (AbFunctor C)} {S' : ShortComplex (AbFunctor C')} {a b c}
  (hS : S.ShortExact) (hS' : S'.ShortExact) (h : Hom L L' a b c)

variable (f r) in
/-- For maps f_n: A_n → B_n, the first r of the conditions: f₀ injective, f₀ surjective, f₁
injective, f₁ surjective, and so on. -/
def BijectiveUpTo := ∀ n, (2 * n < r → Injective (f n)) ∧ (2 * n + 1 < r → Surjective (f n))

lemma forall_bijective_iff_bijectiveUpTo : AllBijective f ↔ ∀ r, BijectiveUpTo f r := by
  simp [AllBijective, BijectiveUpTo, Bijective, forall_and, forall_comm, ← exists_imp, exists_gt]

lemma BijectiveUpTo.congr {g a b} (ha : AllBijective a) (hb : AllBijective b) (w : ∀ n x,
  b n (f n x) = g n (a n x)) : BijectiveUpTo f r ↔ @BijectiveUpTo A' B' g r := by
  simpa [BijectiveUpTo, (hb _).1,
    (ha _).2, *, ↓← comp_def] using congr(BijectiveUpTo $(funext₂ w) r)

lemma Comparison.bijective_iff_of_comm_sq {A B A' B' f f' g g'} (w : ∀ x, f' (g x) = g' (f x)) (h :
  Bijective g) (h' : Bijective g') : @Bijective A B f ↔ @Bijective A' B' f' := by
  simp [← h'.of_comp_iff', ← h.of_comp_iff, comp_def, w]

lemma LongExactSeq.exact_of_shortComplex_exact {S} : @ShortComplex.Exact Ab _ _ S → Exact S.f S.g :=
  S.ab_exact_iff_function_exact.1

/-- For 0 → S₁ → S₂ → S₃ → 0 short exact, the long exact sequence Ext^n(S₃,F) → Ext^n(S₂,F) →
Ext^n(S₁,F) → Ext^{n+1}(S₃,F) of Z-modules. -/
noncomputable def LongExactSeq.contravariant F :=
  {mk _ _ _ (precomp_mk₀_injective_of_epi F (hg := hS.3)) (exact_of_shortComplex_exact ∘'
  contravariant_sequence_exact₂' hS F) (exact_of_shortComplex_exact <|
  contravariant_sequence_exact₁' hS F · _ (by lia)) fun _ ↦ exact_of_shortComplex_exact
  (contravariant_sequence_exact₃' ..) with f := H.map F _, g := H.map F _}

/-- For 0 → S₁ → S₂ → S₃ → 0 short exact, the long exact sequence Ext^n(N,S₁) → Ext^n(N,S₂) →
Ext^n(N,S₃) → Ext^{n+1}(N,S₁) of Z-modules. -/
noncomputable def LongExactSeq.covariant N := mk _ _ _ (postcomp_mk₀_injective_of_mono N (hf :=
  hS.2)) (exact_of_shortComplex_exact ∘' covariant_sequence_exact₂' N hS)
  (exact_of_shortComplex_exact <| covariant_sequence_exact₃' _ hS · _ rfl) fun _ ↦
  exact_of_shortComplex_exact (covariant_sequence_exact₁' ..)

lemma LongExactSeq.Hom.bijective_succ_family {ι : Type*} {L' a b c : ∀ _ : ι, _} (k : ∀ i,
  Hom L (L' i) (a i) (b i) (c i)) (hb : Bijective (swap (b · n ·))) (hc :
  Bijective (swap (c · n ·))) (h : Surjective (L.δ n)) (h' : ∀ i, Surjective ((L' i).δ n)) :
  Bijective (swap (a · n.succ ·)) := by use (.of_ker (AddMonoidHom.pi _) ?_),
  ((Surjective.piMap h').comp hc.2 · |>.imp' (L.δ n) ?_) <;> simp [(k _).comm_delta, h.forall,
  funext_iff, exact_g_delta .., hb.2.exists, Classical.skolem, (k _).comm_g, ← hc.1.eq_iff, swap]

lemma LongExactSeq.Hom.eq_zero_of_delta_eq_zero (h : Hom L _ a b c) (ha : Surjective (a n)) (hb :
  Injective (b n)) x : c n x = 0 → L.δ n x = 0 →
  x = 0 := by grind -linarith [exact_g_delta .., Hom, exact_f_g .., ha.exists]

lemma LongExactSeq.Hom.exists_preimage_mod_f (h : Hom L _ a b c) (i : Injective (a n.succ)) y x (e :
  c n x = L'.g n y) : ∃ z, (∃ w, y = b n z + L'.f n w) ∧ L.g n z = x := by
  cases (L.exact_g_delta _ x).1 (i (by grind [Hom, exact_g_delta ..])); grind
    [exact_f_g _ n (y - b n ‹_›), Hom]

lemma LongExactSeq.Hom.exists_preimage (h : Hom L _ a b c) (ha : Surjective (a n)) (i :
  Injective (a n.succ)) y x (e : c n x = L'.g n y) : ∃ z, b n z = y ∧ L.g n z =
  x := have ⟨z, e⟩ := h.exists_preimage_mod_f i y x e
  (ha.exists.1 e.1).imp' (z + L.f n ·) (by grind [Hom, exact_f_g ..])

include h in
/-- Four lemma for a morphism (a, b, c) of long exact sequences 0 → A⁰ → B⁰ → C⁰ → A¹ → ⋯: if b
satisfies the first r conditions of `BijectiveUpTo` and c the first r − 1, then a
satisfies the first r. -/
lemma LongExactSeq.Hom.four_lemma (hb : BijectiveUpTo (b ·) r) (hc : BijectiveUpTo (c ·) (r - 1)) :
  BijectiveUpTo (a ·) r := by
  rintro ⟨⟩ <;> use fun k ↦ .of_ker _ (h.rotate.rotate.eq_zero_of_delta_eq_zero ?_ ?_ · ·
    ((hb _).1 k ?_)), fun k y ↦ ((hb _).2 k _).elim (h.rotate.exists_preimage ?_ ?_
    y · · |>.imp ?_) <;> first | tauto | simp (disch := lia) [hb _, hc _, h.comm_f, *]

lemma LongExactSeq.Hom.five_lemma (h : Hom L _ a b c) (k : AllBijective (c ·)) :
    AllBijective (b ·) ↔ AllBijective (a ·) := ⟨by simp_all [forall_bijective_iff_bijectiveUpTo,
  h.four_lemma], fun _ n ↦ forall_bijective_iff_bijectiveUpTo.2
  (fun _ ↦ by apply_rules [h.rotate.rotate.four_lemma,
  forall_bijective_iff_bijectiveUpTo.1]; rintro ⟨⟩ <;> aesop) n.succ⟩

set_option backward.isDefEq.respectTransparency false

attribute [local simp] Comparison.pull Surjective H.map H.push LongExactSeq.covariant contravariant

/-- In a long exact sequence 0 → A⁰ → B⁰ → C⁰ → A¹ → ⋯, if B^m → C^m is surjective for all m <
n, then A^n → B^n is injective. -/
lemma LongExactSeq.f_injective_of_g_surjective (L : LongExactSeq) : (∀ m < n, Surjective (L.g m)) →
  Injective (L.f n) := by cases n <;> simp_all [L.injective_f, injective_iff_map_eq_zero,
  exact_delta_f .., exact_g_delta ..]

lemma Comparison.pull_hom_contravariant c (τ : _ ⟶ S.map (restrictAlong («φ» c))) :
  (contravariant hS F).Hom (contravariant hS' F') (c.pull τ.3) (c.pull τ.2) (c.pull τ.1) := by
  constructor <;> simp [← τ.4, ← τ.5, ← comp_assoc (a₂ := 1), add_comm, ← hS'.extClass_naturality]

lemma Comparison.pull_hom_covariant {φ} (τ : S.map (restrictAlong φ) ⟶ _) α : Hom (covariant hS N)
  (covariant hS' N') (pull ⟨φ, τ.1⟩ α) (pull ⟨φ, τ.2⟩ α) (pull ⟨φ, τ.3⟩ α) := by constructor <;>
  simp_all [τ.4, τ.5, ShortComplex.ShortExact.extClass_naturality, comp_assoc (a₃ := 1)]

lemma isCohomEquiv_iff_subsingleton (hS : S.ShortExact) : IsCohomEquiv F S.f ↔ ∀ n, Subsingleton
  (H S.X₃ F n) := by use fun h n ↦ ⟨fun _ _ ↦ (contravariant hS F).f_injective_of_g_surjective
  (fun _ _ ↦ (h _).2) ((h n).1 ?_)⟩, fun h n ↦ ⟨@f_injective_of_g_surjective n.succ (contravariant
  hS F).rotate.rotate ?_, (exact_g_delta (contravariant hS F) n · |>.1 ?_)⟩ <;> simp [nontriviality]

/-- For a short exact sequence 0 → X₁ → X₂ → X₃ → 0 of functors with Extⁿ(X₁,F) = 0 for all n,
the pull-back Extⁿ(X₃,F) → Extⁿ(X₂,F) is bijective for all n. -/
lemma isCohomEquiv_quotient_of_acyclic (hS : S.ShortExact) (h : ∀ n (x : H S.X₁ F n), x = 0) :
    IsCohomEquiv F S.g := fun n ↦ ⟨(contravariant hS F).f_injective_of_g_surjective (by aesop),
  (exact_f_g (contravariant hS F) n · |>.1 (h ..))⟩

open Subfunctor ShortComplex CartesianMonoidalCategory witnessed abCoker cech Limits
variable {C C' : _} {D} [Category C] [Category C'] [Category D] {Y E : D ⥤ Type 1} (F : _) (p : E ⟶
  Y) {P} {A B : D ⥤ Ab.{1} → ℕ → Type*} (f : ∀ N n, A N n → B N n)

/-- The class P contains the zero functors and, for 0 → X₁ → X₂ → X₃ → 0 exact with X₁ in P,
contains X₂ exactly when it contains X₃. -/
def IsClosedClass (P : D ⥤ Ab.{1} → _) := (∀ N, 𝟙 N = 0 → P N) ∧ ∀ S, ShortExact S → P S.X₁ →
  (P S.X₂ ↔ P S.X₃)

lemma IsClosedClass.iff_of_isIso (hP : IsClosedClass P) {M N : D ⥤ _} (g : M ⟶ N) [IsIso g] : P M ↔
  P N := hP.2 _ ⟨exact_kernel g⟩ (hP.1 _ ((isZero_kernel_of_mono g).eq_of_src ..))

lemma H.subsingleton_of_id_eq_zero {N} (e : 𝟙 N = 0) F n : Subsingleton (@H C _ N F n) :=
  ⟨(·.mk₀_id_comp ▸ ·.mk₀_id_comp ▸ by aesop)⟩

/-- Stepwise four lemma for f: along any short exact 0 → X₁ → X₂ → X₃ → 0, the first r
conditions of `BijectiveUpTo` at X₂ and the first r − 1 at X₁ give the first r at X₃. -/
structure StepwiseFourLemma where
  step {X r} : ShortExact X → BijectiveUpTo (f X.X₂) r → BijectiveUpTo (f X.X₁) (r - 1) →
    BijectiveUpTo (f X.X₃) r

/-- Five- and four-lemma properties of maps f_{N,n}: bijectivity in all degrees satisfies
`IsClosedClass`; for 0 → X₁ → X₂ → X₃ → 0 exact, r conditions `BijectiveUpTo` on X₂, r −
1 on X₁ give r on X₃. -/
structure Devissage extends StepwiseFourLemma f where isClosedClass : IsClosedClass (AllBijective <|
  f ·)

/-- For a comparison (φ,β) from F to F', exact functors Φ, Φ' and a natural map η: Φ'N → (ΦN)∘φ,
the induced maps Ext^n(ΦN,F) → Ext^n(Φ'N,F') have the five- and four-lemma properties
`Devissage`. -/
lemma Comparison.devissage {F F'} (c : @Comparison C C' _ _ F F') (Φ : (D ⥤ _) ⥤ _) {Φ'} (η :
  Φ' ⟶ Φ ⋙ restrictAlong c.φ)
  [IsExactFunctor Φ] [IsExactFunctor Φ'] : Devissage fun N ↦ (c.pull (η N) ·) :=
  let L X e := c.pull_hom_contravariant (.map_of_exact e Φ) (e.map_of_exact _) (mapNatTrans X η)
  ⟨⟨(L _ · |>.four_lemma)⟩, by simp_all [← Φ.3, ← Φ'.3, AllBijective, Bijective, Surjective,
        H.subsingleton_of_id_eq_zero, nontriviality], (L · · |>.five_lemma)⟩

variable {f}

instance : IsIso (proj p 0 0) := (isoOfAppBijective _ fun _ ↦
  ((Equiv.subtypeUnivEquiv (by simp)).trans (.funUnique (Fin 1) _)).bijective).isIso_hom

/-- Čech descent. Suppose that, in short exact sequences, r conditions of `BijectiveUpTo` on
the middle term and r − 1 on the kernel give r on the quotient. Then r on Z[E] and r − 1 on
all fibre powers of p give r on Z[im p]. -/
lemma cech_descent_step (st : StepwiseFourLemma f) {r} (h₀ : BijectiveUpTo (f (freeAb E)) r) (h :
  ∀ m, BijectiveUpTo (f (freeAb (cech p m))) (r - 1)) :
  BijectiveUpTo (f (freeAb (range p).toFunctor)) r := by
  let R := Subfunctor.equalizer (ι ⊤ ≫ snd .. ≫ p) (ι ⊤ ≫ fst .. ≫ (range p).ι)
  let e m : witnessed R _ ≅ cech p m := NatIso.ofComponents fun _ ↦ Equiv.toIso (.mk
    (fun ⟨_, t⟩ ↦ ⟨_, (t · |>.2.trans <| t · |>.2.symm)⟩)
    (⟨(⟨_, _, rfl⟩, _), fun i ↦ ⟨⟨⟩, ·.2 i 0⟩⟩) fun t ↦ congr(⟨(⟨$((t.2 0).2), _⟩, _), _⟩))
  have H {m P K r} (e : _ ≅ P) (t : _ ≅ K) := @st.1 ⟨cokerBoundary R m ≫ e.1, e.2 ≫ π _ ≫ t.1,
    by simp [reassoc_of% shortExact_cokerBoundary.1]⟩ r (shortExact_of_iso
    (isoMk (.refl (abCoker _)) e t) shortExact_cokerBoundary.2)
  exact H (freeAb.mapIso (e 0 ≪≫ asIso (proj _ 0 0))) (@asIso _ _ _ _ _
    (shortExact_cokerBoundary.2.isIso_f_iff.2 (.of_epi_eq_zero _ (freeAb.hom_ext fun _ ↦
    (proj_boundary_of_eq_zero ⟨_, ⟨⟩, ·.1.1.2.choose_spec⟩)))) ≪≫ freeAb.mapIso (noWitness _)) h₀
    (show BijectiveUpTo (f (abCoker (boundary R (0 + 2)))) _ from (r - 1).rec (by tauto)
    (fun r i h m ↦ H (freeAb.mapIso (e _)) (.refl _) (h _) (by grind [BijectiveUpTo])) h 0)

/-- Čech descent: if the maps f obey the five and four lemmas (`Devissage`) and are
bijective in all degrees on Z of every fibre power of p: E → Y, E included, then they are so
on Z[im p]. -/
lemma Devissage.bijective_range_of_cech (h : Devissage f) (H : ∀ m, AllBijective (f (freeAb (cech p
  m)))) : AllBijective (f (freeAb (range p).toFunctor)) := (h.isClosedClass.iff_of_isIso (freeAb.map
  (proj p 0 0))).rec (by simp_all [forall_bijective_iff_bijectiveUpTo, cech_descent_step, h.1])

/-- p: E → Y is a cover for F: the inclusion of the image of p in Y induces bijections on
Ext^n(Z[−],F) for all n. -/
def IsCover := IsCohomEquiv F (freeAb.map (range p).ι)

lemma IsPointwiseSurjective.isCover {F} (hp : IsPointwiseSurjective p) :
  IsCover F p := have := (range p).eq_top_iff_isIso.1 (by aesop)
  .of_isIso _
