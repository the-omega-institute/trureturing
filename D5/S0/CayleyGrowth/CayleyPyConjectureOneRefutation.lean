/- GID: D5/S0/CayleyGrowth/CayleyPyConjectureOneRefutation
   generality: G
   mirror-B: D5/B/S0/CayleyGrowth/CayleyPyConjectureOneRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Diameter bounds for polynomial-size transposition generator families. -/

import D5.S0.CayleyGrowth.QuasipolynomialWordMetricRefutation
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic

/-!
Conjecture 1 of Chervov et al. asks for a quasipolynomial diameter for every generator family
whose members can be output in polynomial time. The family here uses all transpositions at
nonsquare sizes and all products of at most three transpositions at square sizes. Both sets
have polynomial-size explicit enumerations.

At nonsquare sizes the full-support rotation forces diameter at least `n / 2`, because each
transposition moves at most two points. At square sizes a permutation is a product of at most
`n` transpositions, so grouping them in triples gives diameter at most `ceil(n / 3)`.
These incompatible slopes occur in the same residue class of any proposed quasipolynomial.
-/

namespace CayleyGrowth

private theorem swapFactorsAux_length_le {α : Type*} [DecidableEq α]
    (l : List α) (f : Equiv.Perm α)
    (h : ∀ {x}, f x ≠ x → x ∈ l) :
    (Equiv.Perm.swapFactorsAux l f h).1.length ≤ l.length := by
  induction l generalizing f with
  | nil => simp [Equiv.Perm.swapFactorsAux]
  | cons x l ih =>
      unfold Equiv.Perm.swapFactorsAux
      split_ifs with hfx
      · exact (ih f (fun {y} hy =>
          List.mem_of_ne_of_mem (fun hyx : y = x => by simp [hyx, hfx.symm] at hy) (h hy))).trans
          (Nat.le_succ _)
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (ih _ (fun {y} hy =>
          have hy' : f y ≠ y ∧ y ≠ x :=
            Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hy
          List.mem_of_ne_of_mem hy'.2 (h hy'.1)))

private theorem swapFactors_length_le {n : ℕ} (f : Equiv.Perm (Fin n)) :
    (Equiv.Perm.swapFactors f).1.length ≤ n := by
  simpa [Equiv.Perm.swapFactors, Finset.length_sort] using
    swapFactorsAux_length_le (Finset.univ.sort (· ≤ ·)) f
      (fun {_ _} => (Finset.mem_sort _).2 (Finset.mem_univ _))

private theorem cayley_edist_le_list_length {G : Type*} [Group G]
    (S : Set G) (u : G) (l : List G) (hl : ∀ g ∈ l, g ∈ S) :
    (SimpleGraph.mulCayley S).edist u (u * l.prod) ≤ l.length := by
  induction l generalizing u with
  | nil => simp
  | cons g l ih =>
      have hg : g ∈ S := hl g (List.mem_cons_self ..)
      have htail : ∀ h ∈ l, h ∈ S := fun h hh => hl h (List.mem_cons_of_mem g hh)
      have hstep : (SimpleGraph.mulCayley S).edist u (u * g) ≤ 1 := by
        by_cases hone : g = 1
        · simp [hone]
        · have hne : u ≠ u * g := by
            intro h
            have h' : u * g = u * 1 := by simpa using h.symm
            exact hone (mul_left_cancel h')
          have hadj : (SimpleGraph.mulCayley S).Adj u (u * g) := by
            apply (SimpleGraph.mulCayley_adj' S u (u * g)).mpr
            exact ⟨hne, ⟨g, hg, Or.inl rfl⟩⟩
          rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj]
      calc
        (SimpleGraph.mulCayley S).edist u (u * (g :: l).prod) ≤
            (SimpleGraph.mulCayley S).edist u (u * g) +
              (SimpleGraph.mulCayley S).edist (u * g) ((u * g) * l.prod) := by
                simpa [List.prod_cons, mul_assoc] using
                  (SimpleGraph.edist_triangle (v := u * g)
                    (G := SimpleGraph.mulCayley S) (u := u) (w := u * (g :: l).prod))
        _ ≤ 1 + l.length := add_le_add hstep (ih (u * g) htail)
        _ = (g :: l).length := by simp [add_comm]

private theorem allTranspositions_edist_le_n (n : ℕ)
    (u v : Equiv.Perm (Fin n)) :
    (SimpleGraph.mulCayley (allTranspositions n)).edist u v ≤ n := by
  let f := u⁻¹ * v
  let l := (Equiv.Perm.swapFactors f).1
  have hprod : l.prod = f := (Equiv.Perm.swapFactors f).2.1
  have hmem : ∀ g ∈ l, g ∈ allTranspositions n :=
    fun g hg => (Equiv.Perm.swapFactors f).2.2 g hg
  have hbound := cayley_edist_le_list_length (allTranspositions n) u l hmem
  have hu : u * l.prod = v := by simp [hprod, f]
  rw [hu] at hbound
  have hlen : l.length ≤ n := swapFactors_length_le f
  exact hbound.trans (by exact_mod_cast hlen)

private theorem support_card_mul_le {n : ℕ}
    (f g : Equiv.Perm (Fin n)) :
    (f * g).support.card ≤ f.support.card + g.support.card :=
  (Finset.card_le_card (Equiv.Perm.support_mul_le f g)).trans
    (Finset.card_union_le f.support g.support)

private theorem support_card_le_two_mul_walk {n : ℕ}
    {u v : Equiv.Perm (Fin n)}
    (w : (SimpleGraph.mulCayley (allTranspositions n)).Walk u v) :
    (u⁻¹ * v).support.card ≤ 2 * w.length := by
  induction w with
  | nil => simp
  | @cons u m v h w ih =>
      have hstep : (u⁻¹ * m).support.card = 2 := by
        rcases (SimpleGraph.mulCayley_adj (allTranspositions n) u m).mp h with
          ⟨_, hs | hs⟩
        · exact Equiv.Perm.card_support_eq_two.mpr hs
        · have htwo : (m⁻¹ * u).support.card = 2 :=
            Equiv.Perm.card_support_eq_two.mpr hs
          have heq : m⁻¹ * u = (u⁻¹ * m)⁻¹ := by group
          rw [heq, Equiv.Perm.support_inv] at htwo
          exact htwo
      have hfactor : u⁻¹ * v = (u⁻¹ * m) * (m⁻¹ * v) := by group
      rw [hfactor]
      have hmul := support_card_mul_le (u⁻¹ * m) (m⁻¹ * v)
      rw [hstep] at hmul
      simpa only [SimpleGraph.Walk.length_cons] using
        hmul.trans (by omega : 2 + (m⁻¹ * v).support.card ≤ 2 * (w.length + 1))

private theorem allTranspositions_diameter_lower {n : ℕ} (hn : 2 ≤ n) :
    n ≤ 2 * (SimpleGraph.mulCayley (allTranspositions n)).diam := by
  let G := SimpleGraph.mulCayley (allTranspositions n)
  have hupper : G.ediam ≤ n :=
    SimpleGraph.ediam_le_of_edist_le (allTranspositions_edist_le_n n)
  have hfinite : G.ediam ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hupper
  have hed : G.edist 1 (finRotate n) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top n)
      (allTranspositions_edist_le_n n 1 (finRotate n))
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hed
  have hsize : (finRotate n).support.card = n := by
    rw [support_finRotate_of_le hn, Finset.card_univ, Fintype.card_fin]
  have hlen : n ≤ 2 * w.length := by
    simpa [hsize] using support_card_le_two_mul_walk w
  have hdist : w.length = G.dist 1 (finRotate n) := by
    change w.length = (G.edist 1 (finRotate n)).toNat
    rw [← hw]
    simp
  have hle : w.length ≤ G.diam := hdist ▸ SimpleGraph.dist_le_diam hfinite
  change w.length ≤ (SimpleGraph.mulCayley (allTranspositions n)).diam at hle
  omega

/-- Products of at most three transpositions, an explicitly enumerable `O(n^6)` family. -/
def tripleTranspositionProducts (n : ℕ) : Set (Equiv.Perm (Fin n)) :=
  {f | ∃ l : List (Equiv.Perm (Fin n)),
    l.length ≤ 3 ∧ (∀ g ∈ l, g.IsSwap) ∧ l.prod = f}

private theorem triple_step_le_one {n : ℕ} (u : Equiv.Perm (Fin n))
    (l : List (Equiv.Perm (Fin n))) (hl : l.length ≤ 3)
    (hs : ∀ g ∈ l, g.IsSwap) :
    (SimpleGraph.mulCayley (tripleTranspositionProducts n)).edist u (u * l.prod) ≤ 1 := by
  have hmem : l.prod ∈ tripleTranspositionProducts n := ⟨l, hl, hs, rfl⟩
  simpa using cayley_edist_le_list_length (tripleTranspositionProducts n) u [l.prod]
    (by simpa using hmem)

private theorem triple_edist_le_list_length {n : ℕ} (u : Equiv.Perm (Fin n))
    (l : List (Equiv.Perm (Fin n))) (hs : ∀ g ∈ l, g.IsSwap) :
    (SimpleGraph.mulCayley (tripleTranspositionProducts n)).edist u (u * l.prod) ≤
      ((l.length + 2) / 3 : ℕ) := by
  let G := SimpleGraph.mulCayley (tripleTranspositionProducts n)
  have main : ∀ k : ℕ, ∀ l : List (Equiv.Perm (Fin n)), l.length = k →
      ∀ u, (∀ g ∈ l, g.IsSwap) → G.edist u (u * l.prod) ≤ ((k + 2) / 3 : ℕ) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro l hlen u hs
      by_cases hzero : l.length = 0
      · have hnil : l = [] := List.length_eq_zero_iff.mp hzero
        subst l
        simp [← hlen]
      by_cases hshort : l.length ≤ 3
      · have hstep := triple_step_le_one u l hshort hs
        have hq : 1 ≤ (k + 2) / 3 := by omega
        exact hstep.trans (by exact_mod_cast hq)
      let a := l.take 3
      let b := l.drop 3
      have ha : a.length = 3 := by simp [a]; omega
      have hb : b.length = l.length - 3 := by simp [b]
      have hblt : b.length < k := by omega
      have has : ∀ g ∈ a, g.IsSwap := fun g hg => hs g (List.mem_of_mem_take hg)
      have hbs : ∀ g ∈ b, g.IsSwap := fun g hg => hs g (List.mem_of_mem_drop hg)
      have hprod : l.prod = a.prod * b.prod := by
        rw [← List.take_append_drop 3 l, List.prod_append]
      have hstep : G.edist u (u * a.prod) ≤ 1 := triple_step_le_one u a (by omega) has
      have hrest : G.edist (u * a.prod) ((u * a.prod) * b.prod) ≤
          ((b.length + 2) / 3 : ℕ) := ih b.length hblt b rfl (u * a.prod) hbs
      have hq : 1 + (b.length + 2) / 3 = (k + 2) / 3 := by omega
      calc
        G.edist u (u * l.prod) ≤
            G.edist u (u * a.prod) + G.edist (u * a.prod) ((u * a.prod) * b.prod) := by
              simpa [hprod, mul_assoc] using
                (SimpleGraph.edist_triangle (G := G) (u := u)
                  (v := u * a.prod) (w := u * l.prod))
        _ ≤ 1 + (((b.length + 2) / 3 : ℕ) : ℕ∞) := add_le_add hstep hrest
        _ = (((k + 2) / 3 : ℕ) : ℕ∞) := by exact_mod_cast hq
  exact main l.length l rfl u hs

private theorem tripleTranspositionProducts_edist_le {n : ℕ}
    (u v : Equiv.Perm (Fin n)) :
    (SimpleGraph.mulCayley (tripleTranspositionProducts n)).edist u v ≤
      ((n + 2) / 3 : ℕ) := by
  let f := u⁻¹ * v
  let l := (Equiv.Perm.swapFactors f).1
  have hprod : l.prod = f := (Equiv.Perm.swapFactors f).2.1
  have hs : ∀ g ∈ l, g.IsSwap := (Equiv.Perm.swapFactors f).2.2
  have hbound := triple_edist_le_list_length u l hs
  have hu : u * l.prod = v := by simp [hprod, f]
  rw [hu] at hbound
  have hlen : l.length ≤ n := swapFactors_length_le f
  have hdiv : (l.length + 2) / 3 ≤ (n + 2) / 3 := by omega
  exact hbound.trans (by exact_mod_cast hdiv)

theorem tripleTranspositionProducts_diameter_upper (n : ℕ) :
    (SimpleGraph.mulCayley (tripleTranspositionProducts n)).diam ≤ (n + 2) / 3 := by
  have h : (SimpleGraph.mulCayley (tripleTranspositionProducts n)).ediam ≤
      ((n + 2) / 3 : ℕ) :=
    SimpleGraph.ediam_le_of_edist_le (tripleTranspositionProducts_edist_le)
  change (SimpleGraph.mulCayley (tripleTranspositionProducts n)).ediam.toNat ≤ _
  exact ENat.toNat_le_toNat h (ENat.natCast_ne_top _)

private theorem polynomial_eventually_nonneg_or_nonpos (P : Polynomial ℚ) :
    (∀ᶠ x : ℚ in Filter.atTop, 0 ≤ P.eval x) ∨
      (∀ᶠ x : ℚ in Filter.atTop, P.eval x ≤ 0) := by
  by_cases hdeg : 0 < P.degree
  · rcases le_total 0 P.leadingCoeff with hl | hl
    · left
      exact (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hl).eventually_ge_atTop 0
    · right
      exact (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hl).eventually_le_atBot 0
  · have hconst : P = Polynomial.C (P.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hdeg)
    rcases le_total 0 (P.coeff 0) with hc | hc
    · left
      exact Filter.Eventually.of_forall (fun x => by rw [hconst, Polynomial.eval_C]; exact hc)
    · right
      exact Filter.Eventually.of_forall (fun x => by rw [hconst, Polynomial.eval_C]; exact hc)

private theorem square_nonsquare_same_residue (p M N B : ℕ) (hp : 0 < p) :
    ∃ u v : ℕ, M ≤ u ∧ M ≤ v ∧ N ≤ u ∧ N ≤ v ∧ B ≤ u ∧ B ≤ v ∧
      8 < u ∧ 0 < v ∧ IsSquare u ∧ ¬ IsSquare v ∧ u % p = 0 ∧ v % p = 0 := by
  let b := p * (M + N + B + p + 10)
  let u := b ^ 2
  let v := u + p
  have hb : M + N + B + p + 10 ≤ b := by
    have h := Nat.le_mul_of_pos_left (M + N + B + p + 10) hp
    simpa [b] using h
  have hbu : b ≤ u := by
    simpa [u, pow_two] using Nat.le_mul_of_pos_left b (by omega : 0 < b)
  have hpb : p ≤ b := by omega
  have hbetween : b ^ 2 < v ∧ v < (b + 1) ^ 2 := by
    dsimp [v, u]
    constructor <;> nlinarith
  have hns : ¬ IsSquare v := by
    rintro ⟨r, hr⟩
    have hlo : b < r := Nat.mul_self_lt_mul_self_iff.mp (by
      simpa only [pow_two, hr] using hbetween.1)
    have hhi : r < b + 1 := Nat.mul_self_lt_mul_self_iff.mp (by
      simpa only [pow_two, hr] using hbetween.2)
    omega
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hns, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact ⟨b, by simp [u, pow_two]⟩
  · simp [u, b, Nat.pow_mod]
  · simpa [v, Nat.add_mod_right] using (show u % p = 0 by simp [u, b, Nat.pow_mod])

theorem not_eventuallyQuasipolynomial_of_square_diameter_gap
    (f : ℕ → ℚ) (M : ℕ)
    (hsq : ∀ n, M ≤ n → IsSquare n → 3 * f n ≤ (n : ℚ) + 2)
    (hns : ∀ n, M ≤ n → ¬ IsSquare n → (n : ℚ) ≤ 2 * f n) :
    ¬ IsEventuallyQuasipolynomial f := by
  rintro ⟨p, hp, P, N, hP⟩
  let Q : Polynomial ℚ := P 0 - Polynomial.C (5 / 12 : ℚ) * Polynomial.X
  rcases polynomial_eventually_nonneg_or_nonpos Q with hsign | hsign
  · obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hsign
    obtain ⟨B, hB⟩ := exists_nat_ge K
    obtain ⟨u, v, hMu, _, hNu, _, hBu, _, hu8, _, huSq, _, hpu, _⟩ :=
      square_nonsquare_same_residue p M N B hp
    have hQ : 0 ≤ Q.eval (u : ℚ) := hK _ (le_trans hB (by exact_mod_cast hBu))
    have hPu : f u = (P 0).eval (u : ℚ) := by simpa [hpu] using hP u hNu
    have hsmall := hsq u hMu huSq
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hQ
    rw [← hPu] at hQ
    have hu8' : (8 : ℚ) < u := by exact_mod_cast hu8
    linarith
  · obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hsign
    obtain ⟨B, hB⟩ := exists_nat_ge K
    obtain ⟨u, v, _, hMv, _, hNv, _, hBv, _, hv0, _, hvNs, _, hpv⟩ :=
      square_nonsquare_same_residue p M N B hp
    have hQ : Q.eval (v : ℚ) ≤ 0 := hK _ (le_trans hB (by exact_mod_cast hBv))
    have hPv : f v = (P 0).eval (v : ℚ) := by simpa [hpv] using hP v hNv
    have hlarge := hns v hMv hvNs
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] at hQ
    rw [← hPv] at hQ
    have hv0' : (0 : ℚ) < v := by exact_mod_cast hv0
    linarith

/-- A square-dependent family with at most `O(n^6)` explicitly enumerable generators. -/
def conjectureOneGenerators (n : ℕ) : Set (Equiv.Perm (Fin n)) :=
  if IsSquare n then tripleTranspositionProducts n else allTranspositions n

noncomputable def conjectureOneDiameter (n : ℕ) : ℚ :=
  (SimpleGraph.mulCayley (conjectureOneGenerators n)).diam

theorem cayleyPy_conjecture1_refuted :
    ¬ IsEventuallyQuasipolynomial conjectureOneDiameter := by
  apply not_eventuallyQuasipolynomial_of_square_diameter_gap conjectureOneDiameter 2
  · intro n _ hsq
    have h := tripleTranspositionProducts_diameter_upper n
    simp only [conjectureOneDiameter, conjectureOneGenerators, if_pos hsq]
    have hq : (3 : ℚ) * (((SimpleGraph.mulCayley (tripleTranspositionProducts n)).diam : ℕ) : ℚ) ≤
        (n : ℚ) + 2 := by
      exact_mod_cast (show 3 * (SimpleGraph.mulCayley
        (tripleTranspositionProducts n)).diam ≤ n + 2 by omega)
    exact hq
  · intro n hn hns
    have h := allTranspositions_diameter_lower hn
    simp only [conjectureOneDiameter, conjectureOneGenerators, if_neg hns]
    exact_mod_cast h

end CayleyGrowth
