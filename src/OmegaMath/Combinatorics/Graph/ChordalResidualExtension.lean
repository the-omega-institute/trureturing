import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.Dirac
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

compile_only_with_mathlib

/-! Omega original.

# Residual invariants under reverse simplicial elimination

A center rule acts on the candidates for a simplicial vertex and maintains
bounds on the residual energy of edges, triangles, and tetrahedra.
-/

namespace SimpleGraph.ChordalResidualExtension

variable {V E : Type*} [NormedAddCommGroup E]

def Skew {ι : Type*} (r : ι → ι → E) : Prop :=
  ∀ i j, r j i = -r i j

theorem Skew.diagonal {ι : Type*} {r : ι → ι → E} (hr : Skew r)
    [NormedSpace ℝ E] (i : ι) : r i i = 0 := by
  have h : (2 : ℝ) • r i i = 0 := by
    rw [two_smul, ← neg_eq_iff_add_eq_zero]
    exact (hr i i).symm
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

def holonomy (r : V → V → E) (a b c : V) : E :=
  r a b + r b c - r a c

noncomputable def triangle (r : V → V → E) (a b c : V) : ℝ :=
  ‖r a b‖ ^ 2 + ‖r b c‖ ^ 2 + ‖r a c‖ ^ 2 - (2 / 3) * ‖holonomy r a b c‖ ^ 2

noncomputable def tetrahedron (r : V → V → E) (a b c d : V) : ℝ :=
  ‖r a b‖ ^ 2 + ‖r a c‖ ^ 2 + ‖r a d‖ ^ 2 + ‖r b c‖ ^ 2 + ‖r b d‖ ^ 2 + ‖r c d‖ ^ 2 -
    (‖holonomy r a b c‖ ^ 2 + ‖holonomy r a b d‖ ^ 2 +
      ‖holonomy r a c d‖ ^ 2 + ‖holonomy r b c d‖ ^ 2) / 2

theorem holonomy_rotate (r : V → V → E) (hr : Skew r) (a b c : V) :
    holonomy r b c a = holonomy r a b c := by
  unfold holonomy
  rw [hr a c, hr a b]
  abel

theorem triangle_rotate (r : V → V → E) (hr : Skew r) (a b c : V) :
    triangle r b c a = triangle r a b c := by
  unfold triangle
  rw [holonomy_rotate r hr, hr a c, hr a b, norm_neg, norm_neg]
  ring

theorem tetrahedron_rotate (r : V → V → E) (hr : Skew r) (a b c d : V) :
    tetrahedron r b c d a = tetrahedron r a b c d := by
  unfold tetrahedron
  rw [holonomy_rotate r hr a b c, holonomy_rotate r hr a b d, holonomy_rotate r hr a c d]
  rw [hr a b, hr a c, hr a d, norm_neg, norm_neg, norm_neg]
  ring

section Local

/-- Data on the already placed neighbors of a simplicial vertex.
The candidate potential at each neighbor's new edge is recorded by `y`. -/
structure Neighborhood (ι : Type*) (r : ι → ι → E) (y : ι → E)
    (R M N : ℝ) : Prop where
  skew : Skew r
  edge : ∀ i j, ‖r i j‖ ≤ R
  defect : ∀ i j, ‖r i j - (y i - y j)‖ ≤ 1
  hol : ∀ i j l, ‖holonomy r i j l‖ ≤ 1
  tri : ∀ i j l, triangle r i j l ≤ M
  tet : ∀ i j l m, tetrahedron r i j l m ≤ N

/-- The edge, triangle, and tetrahedron inequalities to check for a new vertex. -/
structure Placement {ι : Type*} (r : ι → ι → E) (y : ι → E)
    (R M N : ℝ) (z : E) : Prop where
  edge : ∀ i, ‖y i - z‖ ≤ R
  tri : ∀ i j, ‖r i j‖ ^ 2 + ‖y j - z‖ ^ 2 + ‖y i - z‖ ^ 2 -
    (2 / 3) * ‖r i j - (y i - y j)‖ ^ 2 ≤ M
  tet : ∀ i j l, ‖r i j‖ ^ 2 + ‖r i l‖ ^ 2 + ‖y i - z‖ ^ 2 +
      ‖r j l‖ ^ 2 + ‖y j - z‖ ^ 2 + ‖y l - z‖ ^ 2 -
      (‖holonomy r i j l‖ ^ 2 + ‖r i j - (y i - y j)‖ ^ 2 + ‖r i l - (y i - y l)‖ ^ 2 +
        ‖r j l - (y j - y l)‖ ^ 2) / 2 ≤ N

/-- A rule proved for exactly `k` candidates applies to any family of at most
`k` candidates by repeating an existing candidate. -/
theorem placement_of_fin {k : ℕ} {R U M N : ℝ}
    (h : ∀ (r : Fin k → Fin k → E) (y : Fin k → E), Neighborhood (Fin k) r y R M N →
      ∃ z, Placement r y U M N z)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ k) {r : ι → ι → E} {y : ι → E}
    (hr : Neighborhood ι r y R M N) : ∃ z, Placement r y U M N z := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι₀ =>
    exact ⟨0, ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩⟩
  | inr hι₀ =>
    let e := Fintype.equivFin ι
    let f (i : Fin k) : ι :=
      if hi : i.val < Fintype.card ι then e.symm ⟨i.val, hi⟩ else Classical.arbitrary ι
    have hf (i : ι) : f ⟨(e i).val, (e i).isLt.trans_le hι⟩ = i := by simp [f]
    obtain ⟨z, hz⟩ := h (fun i j => r (f i) (f j)) (y ∘ f)
      ⟨fun i j => hr.skew (f i) (f j), fun i j => hr.edge (f i) (f j),
        fun i j => hr.defect (f i) (f j), fun i j l => hr.hol (f i) (f j) (f l),
        fun i j l => hr.tri (f i) (f j) (f l), fun i j l m => hr.tet (f i) (f j) (f l) (f m)⟩
    use z
    constructor
    · intro i
      simpa [Function.comp_def, hf] using hz.edge ⟨(e i).val, (e i).isLt.trans_le hι⟩
    · intro i j
      simpa [Function.comp_def, hf] using hz.tri
        ⟨(e i).val, (e i).isLt.trans_le hι⟩ ⟨(e j).val, (e j).isLt.trans_le hι⟩
    · intro i j l
      simpa [Function.comp_def, hf, holonomy] using hz.tet
        ⟨(e i).val, (e i).isLt.trans_le hι⟩ ⟨(e j).val, (e j).isLt.trans_le hι⟩
        ⟨(e l).val, (e l).isLt.trans_le hι⟩

variable {G : SimpleGraph V}

def Triangle (G : SimpleGraph V) (a b c : V) : Prop :=
  G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

def Tetrahedron (G : SimpleGraph V) (a b c d : V) : Prop :=
  Triangle G a b c ∧ G.Adj a d ∧ G.Adj b d ∧ G.Adj c d

private theorem Triangle.rotate {a b c : V} (h : Triangle G a b c) : Triangle G b c a :=
  ⟨h.2.1, h.2.2.symm, h.1.symm⟩

private theorem Tetrahedron.rotate {a b c d : V} (h : Tetrahedron G a b c d) :
    Tetrahedron G b c d a :=
  ⟨⟨h.1.2.1, h.2.2.2, h.2.2.1⟩, h.1.1.symm, h.1.2.2.symm, h.2.1.symm⟩

def residual (g : V → V → E) (p : V → E) (a b : V) : E :=
  g a b - (p b - p a)

theorem residual_skew {g : V → V → E} (hg : Skew g) (p : V → E) :
    Skew (residual g p) := by
  intro a b
  unfold residual
  rw [hg a b]
  abel

theorem residual_holonomy (g : V → V → E) (p : V → E) (a b c : V) :
    holonomy (residual g p) a b c = holonomy g a b c := by
  unfold holonomy residual
  abel

variable [NormedSpace ℝ E]

private theorem repeated_triangle {ι : Type*} {r : ι → ι → E}
    (hr : Skew r) {M : ℝ} (hM : ∀ i j, 2 * ‖r i j‖ ^ 2 ≤ M)
    {a b c : ι} (h : a = b ∨ b = c ∨ a = c) : triangle r a b c ≤ M := by
  rcases h with rfl | rfl | rfl
  · simpa [triangle, holonomy, hr.diagonal, ← two_mul] using hM a c
  · simpa [triangle, holonomy, hr.diagonal, ← two_mul] using hM a b
  · rw [← triangle_rotate r hr a b a, ← triangle_rotate r hr b a a]
    simpa [triangle, holonomy, hr.diagonal, ← two_mul] using hM a b

private theorem repeated_tetrahedron {ι : Type*} {r : ι → ι → E}
    (hr : Skew r) {R N : ℝ} (hR : ∀ i j, ‖r i j‖ ≤ R) (hN : 5 * R ^ 2 ≤ N)
    {a b c d : ι} (h : a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) :
    tetrahedron r a b c d ≤ N := by
  have hab := pow_le_pow_left₀ (norm_nonneg _) (hR a b) 2
  have hac := pow_le_pow_left₀ (norm_nonneg _) (hR a c) 2
  have had := pow_le_pow_left₀ (norm_nonneg _) (hR a d) 2
  have hbc := pow_le_pow_left₀ (norm_nonneg _) (hR b c) 2
  have hbd := pow_le_pow_left₀ (norm_nonneg _) (hR b d) 2
  have hcd := pow_le_pow_left₀ (norm_nonneg _) (hR c d) 2
  have h₁ := sq_nonneg ‖holonomy r a b c‖
  have h₂ := sq_nonneg ‖holonomy r a b d‖
  have h₃ := sq_nonneg ‖holonomy r a c d‖
  have h₄ := sq_nonneg ‖holonomy r b c d‖
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [tetrahedron, hr.diagonal, norm_zero, zero_pow (by decide : 2 ≠ 0)] <;>
    linarith only [hab, hac, had, hbc, hbd, hcd, h₁, h₂, h₃, h₄, hN]

/-- A placement rule that preserves the residual invariants extends to every
finite chordal graph whose cliques have at most `k+1` vertices. -/
theorem reconstruct [Finite V] (hG : G.IsChordal) {k : ℕ} {R U M N : ℝ}
    (hU : 0 ≤ U) (hUR : U ≤ R) (hM : 2 * R ^ 2 ≤ M) (hN : 5 * R ^ 2 ≤ N)
    (hclique : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ k + 1)
    (hplace : ∀ (r : Fin k → Fin k → E) (y : Fin k → E), Neighborhood (Fin k) r y R M N →
      ∃ z, Placement r y U M N z)
    (g : V → V → E) (hg : Skew g) (ht : ∀ a b c, Triangle G a b c → ‖holonomy g a b c‖ ≤ 1) :
    ∃ p : V → E, ∀ a b, G.Adj a b → ‖residual g p a b‖ ≤ U := by
  classical
  let := Fintype.ofFinite V
  have main (S : Finset V) : ∃ p : V → E,
      (∀ a ∈ S, ∀ b ∈ S, G.Adj a b → ‖residual g p a b‖ ≤ U) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, Triangle G a b c → triangle (residual g p) a b c ≤ M) ∧
      (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, Tetrahedron G a b c d →
        tetrahedron (residual g p) a b c d ≤ N) := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hS : S.Nonempty
      · let : Nonempty (S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
        obtain ⟨v, hv⟩ := (hG.induce (S : Set V)).exists_isSimplicial
        let a : V := v.val
        have ha : a ∈ S := v.property
        obtain ⟨p, he, hq, hi⟩ := ih (S.erase a) (Finset.erase_ssubset ha)
        let K := S.filter fun x => G.Adj x a
        let ι := ↥(K : Set V)
        let r : ι → ι → E := fun x y => residual g p x y
        let y : ι → E := fun x => p x + g x a
        have haK : a ∉ K := fun h => (Finset.mem_filter.mp h).2.ne rfl
        have hxS (x : ι) : x.val ∈ S.erase a :=
          Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp x.property).2.ne, (Finset.mem_filter.mp x.property).1⟩
        have hxA (x : ι) : G.Adj x.val a := (Finset.mem_filter.mp x.property).2
        have hK (x z : ι) (h : x ≠ z) : G.Adj x.val z.val :=
          hv (show (⟨x.val, (Finset.mem_erase.mp (hxS x)).2⟩ : (S : Set V)) ∈ _ from (hxA x).symm)
            (show (⟨z.val, (Finset.mem_erase.mp (hxS z)).2⟩ : (S : Set V)) ∈ _ from (hxA z).symm)
            (fun heq => h (Subtype.ext (congrArg (fun t : (S : Set V) => t.val) heq)))
        have hKcl : G.IsClique (↑(insert a K) : Set V) := by
          intro x hx z hz hne
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hz
          rcases hx with rfl | hx
          · exact (hxA ⟨z, hz.resolve_left hne.symm⟩).symm
          · rcases hz with rfl | hz
            · exact hxA ⟨x, hx⟩
            · exact hK ⟨x, hx⟩ ⟨z, hz⟩ (fun heq => hne (congrArg Subtype.val heq))
        let : Fintype ι := Fintype.ofFinite ι
        have hcard : Fintype.card ι ≤ k := by
          have hc := hclique (insert a K) hKcl
          rw [Finset.card_insert_of_notMem haK] at hc
          have heq : Fintype.card ι = K.card := by
            let e : ι ≃ ↥K := Equiv.refl _
            rw [Fintype.card_congr e, Fintype.card_coe]
          omega
        have hsk : Skew r := fun i j => residual_skew hg p i j
        have hr (i j : ι) : ‖r i j‖ ≤ R := by
          by_cases h : i = j
          · subst j
            simpa [hsk.diagonal] using hU.trans hUR
          · exact (he i (hxS i) j (hxS j) (hK i j h)).trans hUR
        have hdef (i j : ι) : r i j - (y i - y j) = holonomy g i j a := by
          dsimp [r, y, residual, holonomy]
          abel
        have hzero (i j l : ι) (h : i = j ∨ j = l ∨ i = l) : holonomy r i j l = 0 := by
          rcases h with rfl | rfl | rfl
          · simp [holonomy, hsk.diagonal]
          · simp [holonomy, hsk.diagonal]
          · simp [holonomy, hsk.diagonal, hsk i j]
        have hdata : Neighborhood ι r y R M N := by
          refine ⟨hsk, hr, ?_, ?_, ?_, ?_⟩
          · intro i j
            by_cases h : i = j
            · subst j
              simp [hsk.diagonal]
            · rw [hdef]
              exact ht i j a ⟨hK i j h, hxA j, hxA i⟩
          · intro i j l
            by_cases h : i = j ∨ j = l ∨ i = l
            · simp [hzero i j l h]
            · change ‖holonomy (residual g p) i.val j.val l.val‖ ≤ 1
              rw [residual_holonomy]
              push Not at h
              exact ht i j l ⟨hK i j h.1, hK j l h.2.1, hK i l h.2.2⟩
          · intro i j l
            by_cases h : i = j ∨ j = l ∨ i = l
            · apply repeated_triangle hsk _ h
              intro x z
              have hc := pow_le_pow_left₀ (norm_nonneg _) (hr x z) 2
              linarith
            · push Not at h
              exact hq i (hxS i) j (hxS j) l (hxS l)
                ⟨hK i j h.1, hK j l h.2.1, hK i l h.2.2⟩
          · intro i j l m
            by_cases h : i = j ∨ i = l ∨ i = m ∨ j = l ∨ j = m ∨ l = m
            · exact repeated_tetrahedron hsk hr hN h
            · push Not at h
              exact hi i (hxS i) j (hxS j) l (hxS l) m (hxS m)
                ⟨⟨hK i j h.1, hK j l h.2.2.2.1, hK i l h.2.1⟩,
                  hK i m h.2.2.1, hK j m h.2.2.2.2.1, hK l m h.2.2.2.2.2⟩
        obtain ⟨z, hz⟩ := placement_of_fin hplace hcard hdata
        let p' (x : V) := if x = a then z else p x
        let s := residual g p'
        have hs : Skew s := residual_skew hg p'
        have keep {x w : V} (hx : x ≠ a) (hw : w ≠ a) : s x w = residual g p x w := by
          simp [s, residual, p', hx, hw]
        have new (x : ι) : s x a = y x - z := by
          have hn := (hxA x).ne
          simp only [s, residual, p', hn, ite_false, ite_true, y]
          abel
        have newTri (x w : ι) : holonomy s x w a = r x w - (y x - y w) := by
          rw [residual_holonomy, hdef]
        have triLast {x w : V} (hx : x ∈ S) (hw : w ∈ S)
            (h : Triangle G x w a) : triangle s x w a ≤ M := by
          let i : ι := ⟨x, Finset.mem_filter.mpr ⟨hx, h.2.2⟩⟩
          let j : ι := ⟨w, Finset.mem_filter.mpr ⟨hw, h.2.1⟩⟩
          have hh := hz.tri i j
          rwa [triangle, keep h.2.2.ne h.2.1.ne, new i, new j, newTri i j]
        have tetLast {x w u : V} (hx : x ∈ S) (hw : w ∈ S) (hu : u ∈ S)
            (h : Tetrahedron G x w u a) : tetrahedron s x w u a ≤ N := by
          let i : ι := ⟨x, Finset.mem_filter.mpr ⟨hx, h.2.1⟩⟩
          let j : ι := ⟨w, Finset.mem_filter.mpr ⟨hw, h.2.2.1⟩⟩
          let l : ι := ⟨u, Finset.mem_filter.mpr ⟨hu, h.2.2.2⟩⟩
          have hhol : holonomy s x w u = holonomy r i j l := by
            unfold holonomy
            rw [keep h.2.1.ne h.2.2.1.ne, keep h.2.2.1.ne h.2.2.2.ne,
              keep h.2.1.ne h.2.2.2.ne]
          rw [tetrahedron, hhol, newTri i j, newTri i l, newTri j l, new i, new j, new l,
            keep h.2.1.ne h.2.2.1.ne, keep h.2.1.ne h.2.2.2.ne, keep h.2.2.1.ne h.2.2.2.ne]
          exact hz.tet i j l
        have old (x : V) (hx : x ∈ S) (h : x ≠ a) : x ∈ S.erase a :=
          Finset.mem_erase.mpr ⟨h, hx⟩
        refine ⟨p', ?_, ?_, ?_⟩
        · intro x hx w hw h
          change ‖s x w‖ ≤ U
          by_cases hx' : x = a
          · subst x
            rw [hs w a, norm_neg]
            let i : ι := ⟨w, Finset.mem_filter.mpr ⟨hw, h.symm⟩⟩
            rw [new i]
            exact hz.edge i
          by_cases hw' : w = a
          · subst w
            let i : ι := ⟨x, Finset.mem_filter.mpr ⟨hx, h⟩⟩
            rw [new i]
            exact hz.edge i
          rw [keep hx' hw']
          exact he x (old x hx hx') w (old w hw hw') h
        · intro x hx w hw u hu h
          change triangle s x w u ≤ M
          by_cases hx' : x = a
          · subst x
            rw [← triangle_rotate s hs]
            exact triLast hw hu h.rotate
          by_cases hw' : w = a
          · subst w
            rw [← triangle_rotate s hs, ← triangle_rotate s hs]
            exact triLast hu hx h.rotate.rotate
          by_cases hu' : u = a
          · subst u
            exact triLast hx hw h
          unfold triangle holonomy
          rw [keep hx' hw', keep hw' hu', keep hx' hu']
          exact hq x (old x hx hx') w (old w hw hw') u (old u hu hu') h
        · intro x hx w hw u hu b hb h
          change tetrahedron s x w u b ≤ N
          by_cases hx' : x = a
          · subst x
            rw [← tetrahedron_rotate s hs]
            exact tetLast hw hu hb h.rotate
          by_cases hw' : w = a
          · subst w
            rw [← tetrahedron_rotate s hs, ← tetrahedron_rotate s hs]
            exact tetLast hu hb hx h.rotate.rotate
          by_cases hu' : u = a
          · subst u
            rw [← tetrahedron_rotate s hs, ← tetrahedron_rotate s hs, ← tetrahedron_rotate s hs]
            exact tetLast hb hx hw h.rotate.rotate.rotate
          by_cases hb' : b = a
          · subst b
            exact tetLast hx hw hu h
          unfold tetrahedron holonomy
          rw [keep hx' hw', keep hx' hu', keep hx' hb', keep hw' hu', keep hw' hb', keep hu' hb']
          exact hi x (old x hx hx') w (old w hw hw') u (old u hu hu') b (old b hb hb') h
      · exact ⟨fun _ => 0, ⟨fun i hi => (hS ⟨i, hi⟩).elim,
          fun i hi => (hS ⟨i, hi⟩).elim, fun i hi => (hS ⟨i, hi⟩).elim⟩⟩
  obtain ⟨p, hp, _, _⟩ := main Finset.univ
  exact ⟨p, fun a b hab => hp a (Finset.mem_univ a) b (Finset.mem_univ b) hab⟩

end Local

end SimpleGraph.ChordalResidualExtension
