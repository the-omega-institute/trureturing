/- GID: D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport
   mirror-E: none(waiver:source-only-positive-theorem)
   anchors: []
   utility: none
   digest: Actual nonzero proper ideals and divisor/support semantics for ideal-intersection graphs. -/

import Mathlib.RingTheory.Ideal.Int
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
The ideal-intersection graph and support model are attributed to
`the-omega-institute/ideal-intersection-laplacian`, commit
`b93becea662a746badeadba42fdc3d3eb3db9382`, `paper/sections/graph.tex`.
The formal proofs are independently authored. Vertices here are actual ideals;
all divisor and support models are connected to them by proved equivalences.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Ideal Finset Matrix
open scoped Classical

namespace D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport

/-- The vertices of the ideal-intersection graph, as actual ideals. -/
abbrev Vertex (n : ℕ) := {I : Ideal (ZMod n) // I ≠ ⊥ ∧ I ≠ ⊤}

/-- Distinct nonzero proper ideals are joined precisely when their intersection is nonzero. -/
def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj I J := I ≠ J ∧ I.1 ⊓ J.1 ≠ ⊥
  symm := ⟨by intro I J h; exact ⟨h.1.symm, by simpa [inf_comm] using h.2⟩⟩
  loopless := ⟨by intro I h; exact h.1 rfl⟩

/-- The positive divisor generating the inverse-image integer ideal. -/
def divisor (n : ℕ) (I : Ideal (ZMod n)) : ℕ :=
  (I.comap (Int.castRingHom (ZMod n))).absNorm

private lemma divisor_comap (n : ℕ) (I : Ideal (ZMod n)) :
    Ideal.span {(divisor n I : ℤ)} = I.comap (Int.castRingHom (ZMod n)) :=
  Int.ideal_span_absNorm_eq_self _

private lemma divisor_dvd (n : ℕ) (I : Ideal (ZMod n)) : divisor n I ∣ n := by
  apply Int.natCast_dvd_natCast.mp
  rw [← Ideal.mem_span_singleton, divisor_comap, Ideal.mem_comap]
  simpa using I.zero_mem

private lemma span_divisor (n : ℕ) (I : Ideal (ZMod n)) :
    Ideal.span {(divisor n I : ZMod n)} = I := by
  have h := congrArg (Ideal.map (Int.castRingHom (ZMod n))) (divisor_comap n I)
  rw [Ideal.map_comap_of_surjective _ ZMod.intCast_surjective] at h
  simpa [Ideal.map_span] using h

private lemma divisor_injective (n : ℕ) : Function.Injective (divisor n) := by
  intro I J h
  rw [← span_divisor n I, ← span_divisor n J, h]

private lemma comap_span_of_dvd {n d : ℕ} (hd : d ∣ n) :
    (Ideal.span {(d : ZMod n)}).comap (Int.castRingHom (ZMod n)) =
      Ideal.span {(d : ℤ)} := by
  have hm : Ideal.map (Int.castRingHom (ZMod n)) (Ideal.span {(d : ℤ)}) =
      Ideal.span {(d : ZMod n)} := by simp [Ideal.map_span]
  rw [← hm, Ideal.comap_map_of_surjective _ ZMod.intCast_surjective]
  apply sup_eq_left.mpr
  rw [← RingHom.ker_eq_comap_bot, ZMod.ker_intCastRingHom]
  exact Ideal.span_singleton_le_span_singleton.mpr (Int.natCast_dvd_natCast.mpr hd)

private lemma divisor_span_of_dvd {n d : ℕ} (hd : d ∣ n) :
    divisor n (Ideal.span {(d : ZMod n)}) = d := by
  simp [divisor, comap_span_of_dvd hd, Ideal.absNorm_span_natCast]

/-- All actual ideals of `ZMod n` correspond to divisors of `n`, including the two endpoints. -/
def idealDivisorEquiv (n : ℕ) : Ideal (ZMod n) ≃ {d : ℕ // d ∣ n} where
  toFun I := ⟨divisor n I, divisor_dvd n I⟩
  invFun d := Ideal.span {(d.1 : ZMod n)}
  left_inv I := span_divisor n I
  right_inv d := Subtype.ext (divisor_span_of_dvd d.2)

private lemma divisor_bot (n : ℕ) : divisor n ⊥ = n := by
  simpa using (divisor_span_of_dvd (n := n) (d := n) (dvd_refl n))

private lemma divisor_top (n : ℕ) : divisor n ⊤ = 1 := by
  simpa using (divisor_span_of_dvd (n := n) (d := 1) (one_dvd n))

private lemma divisor_inf (n : ℕ) (I J : Ideal (ZMod n)) :
    divisor n (I ⊓ J) = Nat.lcm (divisor n I) (divisor n J) := by
  have h : (I ⊓ J).comap (Int.castRingHom (ZMod n)) =
      Ideal.span {((Nat.lcm (divisor n I) (divisor n J) : ℕ) : ℤ)} := by
    rw [Ideal.comap_inf, ← divisor_comap n I, ← divisor_comap n J,
      span_singleton_inf_span_singleton, ← Int.coe_lcm, Int.lcm_def]
    simp
  change Ideal.absNorm _ = _
  rw [h]
  simp [Ideal.absNorm_span_natCast]

/-- Adjacency in the actual ideal graph is exactly the divisor intersection test. -/
theorem adj_iff_lcm (n : ℕ) (I J : Vertex n) :
    (graph n).Adj I J ↔ I ≠ J ∧ Nat.lcm (divisor n I.1) (divisor n J.1) ≠ n := by
  change (I ≠ J ∧ I.1 ⊓ J.1 ≠ ⊥) ↔ _
  have hi : I.1 ⊓ J.1 = ⊥ ↔ Nat.lcm (divisor n I.1) (divisor n J.1) = n := by
    constructor
    · intro h
      simpa [divisor_inf, divisor_bot] using congrArg (divisor n) h
    · intro h
      apply divisor_injective n
      simpa [divisor_inf, divisor_bot] using h
  exact and_congr_right (fun _ => not_congr hi)

section PrimePowers
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)

/-- The modulus for an arbitrary finite family of prime powers. -/
def modulus (k : ι → ℕ) : ℕ := ∏ i, p i ^ k i

/-- The complete exponent box, including the zero and full exponent vectors. -/
abbrev Box (k : ι → ℕ) := ∀ i, Fin (k i + 1)

include hp in
private lemma modulus_ne_zero (k : ι → ℕ) : modulus p k ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero)

include hp in
private lemma factorization_modulus (k : ι → ℕ) :
    (modulus p k).factorization = ∑ i, Finsupp.single (p i) (k i) := by
  rw [modulus, Nat.factorization_prod (fun i _ => pow_ne_zero _ (hp i).ne_zero)]
  exact Finset.sum_congr rfl (fun i _ => (hp i).factorization_pow)

include hp hinj in
private lemma factorization_modulus_at (k : ι → ℕ) (j : ι) :
    (modulus p k).factorization (p j) = k j := by
  classical
  rw [factorization_modulus p hp, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    exact Finsupp.single_eq_of_ne (fun h => hij (hinj h.symm))
  · simp

include hp in
private lemma factorization_modulus_off (k : ι → ℕ) (q : ℕ)
    (hq : ∀ i, p i ≠ q) : (modulus p k).factorization q = 0 := by
  rw [factorization_modulus p hp, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun i _ => Finsupp.single_eq_of_ne (hq i).symm)

include hp hinj in
private lemma modulus_dvd_iff (k l : ι → ℕ) :
    modulus p k ∣ modulus p l ↔ ∀ i, k i ≤ l i := by
  constructor
  · intro h i
    have hf := (Nat.factorization_le_iff_dvd (modulus_ne_zero p hp k)
      (modulus_ne_zero p hp l)).mpr h
    simpa only [factorization_modulus_at p hp hinj] using hf (p i)
  · intro h
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow (p i) (h i))

include hp hinj in
private lemma divisor_reconstruct (k : ι → ℕ) {d : ℕ} (hd : d ∣ modulus p k) :
    modulus p (fun i => d.factorization (p i)) = d := by
  have hn := modulus_ne_zero p hp k
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
  apply Nat.eq_of_factorization_eq (modulus_ne_zero p hp _) hd0
  intro q
  by_cases hq : ∃ i, p i = q
  · obtain ⟨i, rfl⟩ := hq
    exact factorization_modulus_at p hp hinj _ i
  · have hoff : ∀ i, p i ≠ q := by simpa using hq
    rw [factorization_modulus_off p hp _ q hoff]
    symm
    apply Nat.eq_zero_of_le_zero
    have hle := (Nat.factorization_le_iff_dvd hd0 hn).mpr hd
    simpa [factorization_modulus_off p hp k q hoff] using hle q

/-- Prime-power exponents classify every actual ideal, with no support-class assumptions. -/
def idealBoxEquiv (k : ι → ℕ) : Ideal (ZMod (modulus p k)) ≃ Box k :=
  (idealDivisorEquiv (modulus p k)).trans
  { toFun := fun d i => ⟨d.1.factorization (p i), by
      have hd0 : d.1 ≠ 0 := ne_zero_of_dvd_ne_zero (modulus_ne_zero p hp k) d.2
      have hle := (Nat.factorization_le_iff_dvd hd0 (modulus_ne_zero p hp k)).mpr d.2
      have := hle (p i)
      rw [factorization_modulus_at p hp hinj] at this
      omega⟩
    invFun := fun e => ⟨modulus p (fun i => (e i).1),
      (modulus_dvd_iff p hp hinj _ _).mpr (fun i => Nat.le_of_lt_succ (e i).2)⟩
    left_inv := fun d => Subtype.ext (divisor_reconstruct p hp hinj k d.2)
    right_inv := fun e => by
      funext i
      apply Fin.ext
      exact factorization_modulus_at p hp hinj _ i }

/-- The exponent vector of the zero ideal. -/
def fullExponent (k : ι → ℕ) : Box k := fun i => ⟨k i, Nat.lt_succ_self _⟩

/-- The exponent vector of the unit ideal. -/
def zeroExponent (k : ι → ℕ) : Box k := fun _ => 0

private lemma idealBox_bot (k : ι → ℕ) :
    idealBoxEquiv p hp hinj k ⊥ = fullExponent k := by
  funext i
  apply Fin.ext
  change (divisor (modulus p k) ⊥).factorization (p i) = k i
  rw [divisor_bot, factorization_modulus_at p hp hinj]

private lemma idealBox_top (k : ι → ℕ) :
    idealBoxEquiv p hp hinj k ⊤ = zeroExponent k := by
  funext i
  apply Fin.ext
  change (divisor (modulus p k) ⊤).factorization (p i) = 0
  rw [divisor_top, Nat.factorization_one]
  rfl

/-- The exponent box with precisely the two ideal endpoints removed. -/
abbrev BoxVertex (k : ι → ℕ) :=
  {e : Box k // e ≠ fullExponent k ∧ e ≠ zeroExponent k}

/-- The ideal/exponent correspondence preserves both excluded endpoints. -/
def vertexBoxEquiv (k : ι → ℕ) : Vertex (modulus p k) ≃ BoxVertex k where
  toFun I := ⟨idealBoxEquiv p hp hinj k I.1,
    fun h => I.2.1 ((idealBoxEquiv p hp hinj k).injective
      (h.trans (idealBox_bot p hp hinj k).symm)),
    fun h => I.2.2 ((idealBoxEquiv p hp hinj k).injective
      (h.trans (idealBox_top p hp hinj k).symm))⟩
  invFun e := by
    refine ⟨(idealBoxEquiv p hp hinj k).symm e.1, ?_, ?_⟩
    · intro h
      apply e.2.1
      rw [← (idealBoxEquiv p hp hinj k).apply_symm_apply e.1, h,
        idealBox_bot p hp hinj k]
    · intro h
      apply e.2.2
      rw [← (idealBoxEquiv p hp hinj k).apply_symm_apply e.1, h,
        idealBox_top p hp hinj k]
  left_inv I := Subtype.ext ((idealBoxEquiv p hp hinj k).symm_apply_apply I.1)
  right_inv e := by
    apply Subtype.ext
    change idealBoxEquiv p hp hinj k ((idealBoxEquiv p hp hinj k).symm e.1) = e.1
    exact (idealBoxEquiv p hp hinj k).apply_symm_apply e.1

/-- A coordinate belongs to the support exactly when its exponent is not maximal. -/
def support {k : ι → ℕ} (e : Box k) : Finset ι :=
  Finset.univ.filter (fun i => (e i).1 < k i)

/-- The support-class relation, with the diagonal removed. -/
def supportGraph (k : ι → ℕ) : SimpleGraph (BoxVertex k) where
  Adj e f := e ≠ f ∧ ∃ i, i ∈ support e.1 ∧ i ∈ support f.1
  symm := ⟨by rintro e f ⟨h, i, he, hf⟩; exact ⟨h.symm, i, hf, he⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

private lemma idealBox_inf_apply (k : ι → ℕ) (I J : Ideal (ZMod (modulus p k))) (i : ι) :
    ((idealBoxEquiv p hp hinj k (I ⊓ J)) i).1 =
      max ((idealBoxEquiv p hp hinj k I) i).1 ((idealBoxEquiv p hp hinj k J) i).1 := by
  have hn := modulus_ne_zero p hp k
  have hi : divisor (modulus p k) I ≠ 0 :=
    ne_zero_of_dvd_ne_zero hn (divisor_dvd _ I)
  have hj : divisor (modulus p k) J ≠ 0 :=
    ne_zero_of_dvd_ne_zero hn (divisor_dvd _ J)
  change (divisor _ (I ⊓ J)).factorization (p i) =
    max ((divisor _ I).factorization (p i)) ((divisor _ J).factorization (p i))
  rw [divisor_inf, Nat.factorization_lcm hi hj]
  rfl

/-- The graph on actual ideals is isomorphic to the support-class graph.
This includes the universal vertices and does not assume a spectral bridge. -/
def actualSupportIso (k : ι → ℕ) : graph (modulus p k) ≃g supportGraph k where
  toEquiv := vertexBoxEquiv p hp hinj k
  map_rel_iff' := by
    intro I J
    change (supportGraph k).Adj (vertexBoxEquiv p hp hinj k I)
      (vertexBoxEquiv p hp hinj k J) ↔ (graph (modulus p k)).Adj I J
    rw [adj_iff_lcm]
    change ((vertexBoxEquiv p hp hinj k I ≠ vertexBoxEquiv p hp hinj k J) ∧ _) ↔
      (I ≠ J ∧ Nat.lcm (divisor (modulus p k) I.1) (divisor (modulus p k) J.1) ≠ modulus p k)
    rw [(vertexBoxEquiv p hp hinj k).injective.ne_iff]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨i, hi, hj⟩ hlcm
      have hbot : I.1 ⊓ J.1 = ⊥ := divisor_injective _ (by
        rw [divisor_inf,hlcm,divisor_bot])
      have h := idealBox_inf_apply p hp hinj k I.1 J.1 i
      rw [hbot, idealBox_bot p hp hinj k] at h
      have hei : ((idealBoxEquiv p hp hinj k I.1) i).1 < k i :=
        (Finset.mem_filter.mp hi).2
      have hej : ((idealBoxEquiv p hp hinj k J.1) i).1 < k i :=
        (Finset.mem_filter.mp hj).2
      change k i = _ at h
      omega
    · intro hlcm
      have hbot : I.1 ⊓ J.1 ≠ ⊥ := by
        intro hz
        apply hlcm
        rw [← divisor_inf,hz,divisor_bot]
      by_contra! hno
      apply hbot
      apply (idealBoxEquiv p hp hinj k).injective
      rw [idealBox_bot p hp hinj k]
      funext i
      apply Fin.ext
      rw [idealBox_inf_apply p hp hinj]
      have hI := ((idealBoxEquiv p hp hinj k I.1) i).2
      have hJ := ((idealBoxEquiv p hp hinj k J.1) i).2
      have hi := hno i
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      change ((idealBoxEquiv p hp hinj k I.1 i).1 < k i →
        ¬(idealBoxEquiv p hp hinj k J.1 i).1 < k i) at hi
      change max _ _ = k i
      omega


/-- A support fiber is a product of the freely varying proper prime-power exponents. -/
def supportFiberEquiv (k : ι → ℕ) (S : Finset ι) :
    {e : Box k // support e = S} ≃ (∀ i : S, Fin (k i.1)) where
  toFun e i := ⟨(e.1 i.1).1, by
    have h : i.1 ∈ support e.1 := e.2.symm ▸ i.2
    exact (Finset.mem_filter.mp h).2⟩
  invFun e := by
    refine ⟨fun i => if hi : i ∈ S then ⟨(e ⟨i, hi⟩).1, Nat.lt_succ_of_lt (e ⟨i, hi⟩).2⟩
      else ⟨k i, Nat.lt_succ_self _⟩, ?_⟩
    ext i
    by_cases hi : i ∈ S
    · simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, dif_pos hi]
      exact iff_of_true (e ⟨i, hi⟩).2 hi
    · simp [support, hi]
  left_inv e := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    dsimp
    split_ifs with hi
    · rfl
    · have h : i ∉ support e.1 := by rwa [e.2]
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at h
      have := (e.1 i).2
      change k i = (e.1 i).1
      omega
  right_inv e := by
    funext i
    apply Fin.ext
    dsimp
    simp only [dif_pos i.2]

/-- Every nonempty support class has its exact prime-power multiplicity. -/
theorem support_fiber_card (k : ι → ℕ) (S : Finset ι) :
    Nat.card {e : Box k // support e = S} = ∏ i ∈ S, k i := by
  classical
  rw [Nat.card_congr (supportFiberEquiv k S), Nat.card_eq_fintype_card,
    Fintype.card_pi]
  simp only [Fintype.card_fin]
  exact (Finset.prod_subtype S (fun _ => Iff.rfl) (fun i => k i)).symm

include hp hinj in
/-- The number of actual nonzero proper ideals, for arbitrary positive exponents. -/
theorem actual_vertex_card (k : ι → ℕ) (hk : ∀ i, 0 < k i) [Nonempty ι] :
    Nat.card (Vertex (modulus p k)) = (∏ i, (k i + 1)) - 2 := by
  classical
  rw [Nat.card_congr (vertexBoxEquiv p hp hinj k)]
  let bad : Box k → Prop := fun e => e = fullExponent k ∨ e = zeroExponent k
  have hne : fullExponent k ≠ zeroExponent k := by
    intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have he := congrArg (fun e : Box k => (e i).1) h
    change k i = 0 at he
    exact (hk i).ne' he
  have hbad : Fintype.card {e : Box k // bad e} = 2 := by
    rw [Fintype.card_subtype]
    have hf : ({e : Box k | bad e} : Finset (Box k)) = {fullExponent k, zeroExponent k} := by
      ext e
      simp [bad]
    rw [hf]
    simp [hne]
  have he : Fintype.card (BoxVertex k) = Fintype.card {e : Box k // ¬bad e} := by
    exact Fintype.card_congr (Equiv.subtypeEquivRight (by intro e; simp [bad]))
  rw [Nat.card_eq_fintype_card, he, Fintype.card_subtype_compl, hbad]
  simp only [Box, Fintype.card_pi, Fintype.card_fin]

/-- Every retained exponent vertex has nonempty support. -/
theorem support_nonempty (k : ι → ℕ) (e : BoxVertex k) :
    (support e.1).Nonempty := by
  by_contra h
  have hempty := Finset.not_nonempty_iff_eq_empty.mp h
  apply e.2.1
  funext i
  apply Fin.ext
  have hi : ¬(e.1 i).1 < k i := by
    intro hh
    have : i ∈ support e.1 := Finset.mem_filter.mpr ⟨mem_univ i, hh⟩
    simpa [hempty] using this
  have := (e.1 i).2
  change (e.1 i).1 = k i
  omega

private def singletonExponent (k : ι → ℕ) (i : ι) : Box k :=
  fun j => if j = i then 0 else fullExponent k j

private def singletonVertex (k : ι → ℕ) (hk : ∀ i, 0 < k i) [Nontrivial ι]
    (i : ι) : BoxVertex k := by
  refine ⟨singletonExponent k i, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun e : Box k => (e i).1) h
    have hi := hk i
    simp [singletonExponent, fullExponent] at hh
    omega
  · intro h
    obtain ⟨j, hji⟩ := exists_ne i
    have hh := congrArg (fun e : Box k => (e j).1) h
    have hj := hk j
    simp [singletonExponent, fullExponent, zeroExponent, hji] at hh
    omega

private lemma support_singletonVertex (k : ι → ℕ) (hk : ∀ i, 0 < k i) [Nontrivial ι]
    (i : ι) : support (singletonVertex k hk i).1 = {i} := by
  ext j
  simp only [support, mem_filter, mem_univ, true_and, mem_singleton]
  change ((singletonExponent k i j).1 < k j) ↔ j = i
  by_cases hji : j = i
  · subst j
    simp [singletonExponent, hk i]
  · simp [singletonExponent, fullExponent, hji]

/-- Complement adjacency is exactly disjointness of the nonempty supports. -/
theorem complement_adj_disjoint (k : ι → ℕ) (e f : BoxVertex k) :
    (supportGraph k)ᶜ.Adj e f ↔ Disjoint (support e.1) (support f.1) := by
  rw [SimpleGraph.compl_adj]
  constructor
  · rintro ⟨hne, h⟩
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact h ⟨hne, i, hi, hj⟩
  · intro h
    have hne : e ≠ f := by
      intro hef
      subst f
      obtain ⟨i, hi⟩ := support_nonempty k e
      exact Finset.disjoint_left.mp h hi hi
    refine ⟨hne, ?_⟩
    rintro ⟨_, i, hi, hj⟩
    exact Finset.disjoint_left.mp h hi hj

/-- The nonuniversal part of the support model. -/
abbrev ActiveVertex (k : ι → ℕ) :=
  {e : BoxVertex k // support e.1 ≠ univ}

/-- The complement after deleting all universal vertices. -/
def activeComplement (k : ι → ℕ) : SimpleGraph (ActiveVertex k) :=
  ((supportGraph k)ᶜ).induce {e : BoxVertex k | support e.1 ≠ univ}

private def activeSingleton (k : ι → ℕ) (hk : ∀ i, 0 < k i) [Nontrivial ι]
    (i : ι) : ActiveVertex k := by
  refine ⟨singletonVertex k hk i, ?_⟩
  rw [support_singletonVertex]
  intro h
  obtain ⟨j, hji⟩ := exists_ne i
  have hj : j ∈ ({i} : Finset ι) := h.symm ▸ mem_univ j
  exact hji (mem_singleton.mp hj)

/-- The complement with its universal vertices removed is connected, uniformly
in the number of prime coordinates and all positive exponents. -/
theorem activeComplement_connected (k : ι → ℕ) (hk : ∀ i, 0 < k i) [Nontrivial ι] :
    (activeComplement k).Connected := by
  classical
  have hs (i : ι) : support (activeSingleton k hk i).1.1 = {i} :=
    support_singletonVertex k hk i
  have hex (e : ActiveVertex k) : ∃ i, i ∉ support e.1.1 := by
    by_contra! h
    exact e.2 (eq_univ_iff_forall.mpr h)
  have hlink (e : ActiveVertex k) (i : ι) (hi : i ∉ support e.1.1) :
      (activeComplement k).Adj e (activeSingleton k hk i) := by
    change (supportGraph k)ᶜ.Adj e.1 (activeSingleton k hk i).1
    rw [complement_adj_disjoint, hs]
    exact Finset.disjoint_singleton_right.mpr hi
  have hbetween (i j : ι) (hij : i ≠ j) :
      (activeComplement k).Adj (activeSingleton k hk i) (activeSingleton k hk j) := by
    change (supportGraph k)ᶜ.Adj (activeSingleton k hk i).1 (activeSingleton k hk j).1
    rw [complement_adj_disjoint, hs, hs]
    exact Finset.disjoint_singleton.mpr hij
  letI : Nonempty (ActiveVertex k) := ⟨activeSingleton k hk (Classical.arbitrary ι)⟩
  refine { preconnected := ?_ }
  intro e f
  obtain ⟨i, hi⟩ := hex e
  obtain ⟨j, hj⟩ := hex f
  have he := (hlink e i hi).reachable
  have hf := (hlink f j hj).reachable.symm
  by_cases hij : i = j
  · subst j
    exact he.trans hf
  · exact he.trans ((hbetween i j hij).reachable.trans hf)

private lemma support_fullExponent (k : ι → ℕ) : support (fullExponent k) = ∅ := by
  ext i
  simp [support, fullExponent]

private lemma support_zeroExponent (k : ι → ℕ) (hk : ∀ i, 0 < k i) :
    support (zeroExponent k) = univ := by
  ext i
  constructor
  · intro _; exact mem_univ i
  · intro _
    exact mem_filter.mpr ⟨mem_univ i, hk i⟩

/-- For a nonempty proper support, neither removed endpoint lies in its fiber. -/
def vertexSupportFiberEquiv (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (S : Finset ι) (hS : S.Nonempty) (hSu : S ≠ univ) :
    {e : BoxVertex k // support e.1 = S} ≃ {e : Box k // support e = S} where
  toFun e := ⟨e.1.1, e.2⟩
  invFun e := by
    refine ⟨⟨e.1, ?_, ?_⟩, e.2⟩
    · intro h
      have hh : S = ∅ := by rw [← e.2, h, support_fullExponent]
      exact hS.ne_empty hh
    · intro h
      apply hSu
      rw [← e.2, h, support_zeroExponent k hk]
  left_inv e := rfl
  right_inv e := rfl

/-- The support-cell multiplicity in the graph, with actual endpoint removal. -/
theorem vertex_support_fiber_card (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (S : Finset ι) (hS : S.Nonempty) (hSu : S ≠ univ) :
    Nat.card {e : BoxVertex k // support e.1 = S} = ∏ i ∈ S, k i := by
  rw [Nat.card_congr (vertexSupportFiberEquiv k hk S hS hSu), support_fiber_card]

private def universalFiberEquiv (k : ι → ℕ) (hk : ∀ i, 0 < k i) [Nonempty ι] :
    {e : BoxVertex k // support e.1 = univ} ≃
      {e : {e : Box k // support e = univ} // e.1 ≠ zeroExponent k} where
  toFun e := ⟨⟨e.1.1, e.2⟩, e.1.2.2⟩
  invFun e := by
    refine ⟨⟨e.1.1, ?_, e.2⟩, e.1.2⟩
    intro h
    have hh : (univ : Finset ι) = ∅ := by
      rw [← e.1.2, h, support_fullExponent]
    exact Finset.univ_nonempty.ne_empty hh
  left_inv e := rfl
  right_inv e := rfl

/-- Universal vertices have count `∏ kᵢ - 1`, including the possible value zero. -/
theorem universal_vertex_count (k : ι → ℕ) (hk : ∀ i, 0 < k i) [Nonempty ι] :
    Nat.card {e : BoxVertex k // support e.1 = univ} = (∏ i, k i) - 1 := by
  classical
  let z : {e : Box k // support e = univ} := ⟨zeroExponent k, support_zeroExponent k hk⟩
  let ee : {e : {e : Box k // support e = univ} // e.1 ≠ zeroExponent k} ≃
      {e : {e : Box k // support e = univ} // e ≠ z} :=
    Equiv.subtypeEquivRight (fun e => by simp only [ne_eq, Subtype.ext_iff, z])
  rw [Nat.card_congr (universalFiberEquiv k hk), Nat.card_congr ee,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp only [Fintype.card_subtype_eq]
  have hh := support_fiber_card k univ
  simpa only [Nat.card_eq_fintype_card] using congrArg (fun q : ℕ => q - 1) hh

/-- Full support is exactly the universal-vertex condition. -/
theorem universal_iff_full_support (k : ι → ℕ) (hk : ∀ i, 0 < k i) [Nontrivial ι]
    (e : BoxVertex k) : (supportGraph k).IsUniversal e ↔ support e.1 = univ := by
  constructor
  · intro h
    apply eq_univ_iff_forall.mpr
    intro i
    by_contra hi
    have hc : (supportGraph k)ᶜ.Adj e (singletonVertex k hk i) := by
      rw [complement_adj_disjoint, support_singletonVertex]
      exact Finset.disjoint_singleton_right.mpr hi
    have hh : e ≠ singletonVertex k hk i ∧ ¬(supportGraph k).Adj e (singletonVertex k hk i) := hc
    exact hh.2 (h hh.1)
  · intro h f hef
    obtain ⟨i, hi⟩ := support_nonempty k f
    exact ⟨hef, i, h.symm ▸ mem_univ i, hi⟩

/-- The support-cell weight, before the single universal-vertex exclusion. -/
def supportWeight (k : ι → ℕ) (S : Finset ι) : ℝ := ∏ i ∈ S, (k i : ℝ)

theorem support_lift_sum (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (f : Finset ι → ℝ) (h0 : f ∅ = 0) (hu : f univ = 0) :
    (∑ e : BoxVertex k, f (support e.1)) = ∑ S, supportWeight k S * f S := by
  classical
  rw [← Fintype.sum_fiberwise' (fun e : BoxVertex k => support e.1) f]
  apply sum_congr rfl
  intro S _
  by_cases hS : S = ∅
  · subst S; simp [h0]
  by_cases hSu : S = univ
  · subst S; simp [hu]
  have hc : Fintype.card {e : BoxVertex k // support e.1 = S} = ∏ i ∈ S, k i := by
    simpa only [Nat.card_eq_fintype_card] using
      vertex_support_fiber_card k hk S (Finset.nonempty_iff_ne_empty.mpr hS) hSu
  simp only [sum_const, card_univ, nsmul_eq_mul, hc, supportWeight, Nat.cast_prod]

/-- The complement Laplacian on support-constant functions. Empty and full
support cells are explicitly excluded from its neighbor sum. -/
def supportComplementOp (k : ι → ℕ) (f : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ T : Finset ι, if T.Nonempty ∧ T ≠ univ ∧ Disjoint S T
    then supportWeight k T * (f S - f T) else 0

/-- Lift a support function to all actual exponent vertices. -/
def supportLift (k : ι → ℕ) (f : Finset ι → ℝ) : BoxVertex k → ℝ :=
  fun e => f (support e.1)

/-- The support operator is intertwined with the graph's actual complement
Laplacian. In particular its eigenvectors lift without an assumed bridge. -/
theorem support_complement_intertwining (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (f : Finset ι → ℝ) (e : BoxVertex k) :
    (((supportGraph k)ᶜ).lapMatrix ℝ *ᵥ supportLift k f) e =
      supportComplementOp k f (support e.1) := by
  classical
  rw [SimpleGraph.lapMatrix_mulVec_apply']
  have hneighbor : ((supportGraph k)ᶜ).neighborFinset e =
      univ.filter (fun d : BoxVertex k => Disjoint (support e.1) (support d.1)) := by
    ext d
    simp only [SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and]
    exact complement_adj_disjoint k e d
  rw [hneighbor, Finset.sum_filter]
  let g : Finset ι → ℝ := fun T =>
    if T.Nonempty ∧ T ≠ univ ∧ Disjoint (support e.1) T then f (support e.1) - f T else 0
  have he : (support e.1).Nonempty := support_nonempty k e
  have hg : (∑ d : BoxVertex k,
      if Disjoint (support e.1) (support d.1) then
        supportLift k f e - supportLift k f d else 0) =
      ∑ d : BoxVertex k, g (support d.1) := by
    apply sum_congr rfl
    intro d _
    have hd := support_nonempty k d
    by_cases hdu : support d.1 = univ
    · have hdis : ¬Disjoint (support e.1) (univ : Finset ι) := by
        intro h
        obtain ⟨i,hi⟩ := he
        exact Finset.disjoint_left.mp h hi (mem_univ i)
      simp [g, hdu, hdis]
    · simp [g, hd, hdu, supportLift]
  rw [hg, support_lift_sum k hk g (by simp [g]) (by simp [g])]
  unfold supportComplementOp
  apply sum_congr rfl
  intro T _
  dsimp [g]
  split_ifs <;> simp

/-- A nonzero value in a genuine support cell yields a nonzero graph lift. -/
theorem support_lift_nonzero (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (f : Finset ι → ℝ) (S : Finset ι) (hS : S.Nonempty) (hSu : S ≠ univ)
    (hf : f S ≠ 0) : supportLift k f ≠ 0 := by
  classical
  have hcard := vertex_support_fiber_card k hk S hS hSu
  have hpos : 0 < ∏ i ∈ S, k i := Finset.prod_pos (fun i _ => hk i)
  have hn : Nonempty {e : BoxVertex k // support e.1 = S} := by
    apply Fintype.card_pos_iff.mp
    simpa only [← Nat.card_eq_fintype_card, hcard] using hpos
  obtain ⟨e⟩ := hn
  intro h
  have hh := congrFun h e.1
  exact hf (by simpa [supportLift, e.2] using hh)

end PrimePowers

end D5.S3.Combinatorics.SpectralGraph.IdealIntersectionSupport
