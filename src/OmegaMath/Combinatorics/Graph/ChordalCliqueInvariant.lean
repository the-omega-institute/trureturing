import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.EliminationForest
import OmegaMath.Combinatorics.Graph.ChordalResidualExtension
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-! # Clique invariants under simplicial insertion

The invariant may be any predicate on finite cliques that depends only on the
residual restricted to the clique. The gain field is fixed throughout. Local
placement is separated from graph induction; in particular, an analytic center
rule can supply all subset rows simultaneously.
-/

compile_only_with_mathlib

open scoped BigOperators

namespace SimpleGraph.ChordalCliqueInvariant

open ChordalResidualExtension

variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E]

/-- Insert the residuals incident with `a`, retaining all old residuals. -/
def attach (a : V) (r : V → V → E) (c : V → E) (z : E)
    (i j : V) : E :=
  if i = a then if j = a then 0 else -(c j - z)
  else if j = a then c i - z else r i j

/-- Changing the potential only at the new vertex realizes `attach` exactly. -/
theorem residual_update [NormedSpace ℝ E] (g : V → V → E) (hg : Skew g)
    (p : V → E) (a : V) (z : E) :
    ChordalResidualExtension.residual g (Function.update p a z) =
      attach a (ChordalResidualExtension.residual g p) (fun i => g i a + p i) z := by
  funext i j
  by_cases hi : i = a <;> by_cases hj : j = a
  · subst i; subst j
    simp [ChordalResidualExtension.residual, attach, hg.diagonal]
  · subst i
    simp [ChordalResidualExtension.residual, attach, hj, hg j a]
    abel
  · subst j
    simp [ChordalResidualExtension.residual, attach, hi]
    abel
  · simp [ChordalResidualExtension.residual, attach, hi, hj]

/-- Exact compatibility with the fixed gain field. Neither identity involves
the center chosen for the new vertex. -/
structure Compatible (g : V → V → E) (a : V) (K : Finset V)
    (r : V → V → E) (c : V → E) : Prop where
  defect : ∀ i ∈ K, ∀ j ∈ K, r i j - (c i - c j) = holonomy g i j a
  curl : ∀ i ∈ K, ∀ j ∈ K, ∀ k ∈ K, holonomy r i j k = holonomy g i j k

/-- An invariant reads only residuals with both endpoints in its finite set.
Other fixed data, such as the gain curls, may occur freely in the predicate. -/
def Local (P : Finset V → (V → V → E) → Prop) : Prop :=
  ∀ W r r', (∀ i ∈ W, ∀ j ∈ W, r i j = r' i j) → (P W r ↔ P W r')

/-- All finite subcliques of size at most `s` satisfy the invariant. -/
def OnCliques (G : SimpleGraph V) (P : Finset V → (V → V → E) → Prop)
    (s : ℕ) (S : Finset V) (r : V → V → E) : Prop :=
  ∀ W ⊆ S, G.IsClique (W : Set V) → W.card ≤ s → P W r

/-- A local placement rule gives a uniform squared edge cap and preserves any
local invariant on every finite subclique. The rule is needed only for actual
predecessor-clique sizes, selected by `sizeAllowed`. No padding is required. -/
theorem reconstruct [NormedSpace ℝ E] [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (s : ℕ) (cap : ℝ) (P : Finset V → (V → V → E) → Prop)
    (hlocal : Local P) (hempty : ∀ r, P ∅ r)
    (sizeAllowed : ℕ → Prop)
    (hsize : ∀ W : Finset V, G.IsClique (W : Set V) → W.Nonempty →
      sizeAllowed (W.card - 1))
    (g : V → V → E) (hg : Skew g)
    (ht : ∀ i j k, Triangle G i j k → ‖holonomy g i j k‖ ≤ 1)
    (place : ∀ (a : V) (K : Finset V), a ∉ K → G.IsClique (K : Set V) →
      sizeAllowed K.card → ∀ (r : V → V → E) (c : V → E), Skew r →
      (∀ i ∈ K, ∀ j ∈ K, i ≠ j → ‖r i j‖ ^ 2 ≤ cap) →
      (∀ W ⊆ K, W.card ≤ s → P W r) →
      (∀ i ∈ K, ∀ j ∈ K, i ≠ j → ‖r i j - (c i - c j)‖ ≤ 1) →
      (∀ i ∈ K, ∀ j ∈ K, ∀ k ∈ K, Triangle G i j k →
        ‖holonomy r i j k‖ ≤ 1) → Compatible g a K r c →
      ∃ z, (∀ i ∈ K, ‖c i - z‖ ^ 2 ≤ cap) ∧
        ∀ W ⊆ K, W.card < s → P (insert a W) (attach a r c z)) :
    ∃ p : V → E, (∀ i j, G.Adj i j → ‖ChordalResidualExtension.residual g p i j‖ ^ 2 ≤ cap) ∧
      ∀ W : Finset V, G.IsClique (W : Set V) → W.card ≤ s →
        P W (ChordalResidualExtension.residual g p) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have main (S : Finset V) : ∃ p : V → E,
      (∀ i ∈ S, ∀ j ∈ S, G.Adj i j → ‖ChordalResidualExtension.residual g p i j‖ ^ 2 ≤ cap) ∧
      OnCliques G P s S (ChordalResidualExtension.residual g p) := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hS : S.Nonempty
      · obtain ⟨a, ha, hsimp⟩ := hG.exists_simplicial_in_finset S hS
        obtain ⟨p, he, hp⟩ := ih (S.erase a) (Finset.erase_ssubset ha)
        let K := S.filter fun i => G.Adj i a
        have haK : a ∉ K := by simp [K]
        have hKS : K ⊆ S.erase a := by
          intro i hi
          obtain ⟨hiS, hiA⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_erase.mpr ⟨hiA.ne, hiS⟩
        have hK : G.IsClique (K : Set V) := by
          intro i hi j hj hij
          obtain ⟨hiS, hiA⟩ := Finset.mem_filter.mp hi
          obtain ⟨hjS, hjA⟩ := Finset.mem_filter.mp hj
          exact hsimp i hiS j hjS hiA.symm hjA.symm hij
        have hbag : G.IsClique (↑(insert a K) : Set V) := by
          intro i hi j hj hij
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi hj
          rcases hi with rfl | hi
          · exact (Finset.mem_filter.mp (hj.resolve_left hij.symm)).2.symm
          · rcases hj with rfl | hj
            · exact (Finset.mem_filter.mp hi).2
            · exact hK hi hj hij
        have hsz := hsize (insert a K) hbag (Finset.insert_nonempty a K)
        rw [Finset.card_insert_of_notMem haK, Nat.add_sub_cancel] at hsz
        let r := ChordalResidualExtension.residual g p
        let c := fun i => g i a + p i
        have hdef (i j : V) : r i j - (c i - c j) = holonomy g i j a := by
          dsimp [r, c, ChordalResidualExtension.residual, holonomy]
          abel
        obtain ⟨z, hz, hchild⟩ := place a K haK hK hsz r c (residual_skew hg p)
          (fun i hi j hj hij => he i (hKS hi) j (hKS hj) (hK hi hj hij))
          (fun W hWK hWs => hp W (hWK.trans hKS)
            (fun i hi j hj hij => hK (hWK hi) (hWK hj) hij) hWs)
          (fun i hi j hj hij => by
            rw [hdef]
            exact ht i j a ⟨hK hi hj hij, (Finset.mem_filter.mp hj).2,
              (Finset.mem_filter.mp hi).2⟩)
          (fun i _ j _ k _ h => by rw [residual_holonomy]; exact ht i j k h)
          ⟨fun i _ j _ => hdef i j, fun i _ j _ k _ => residual_holonomy g p i j k⟩
        let p' := Function.update p a z
        have keep {i j : V} (hi : i ∈ S.erase a) (hj : j ∈ S.erase a) :
            ChordalResidualExtension.residual g p' i j = r i j := by
          simp [p', r, ChordalResidualExtension.residual,
            (Finset.mem_erase.mp hi).1, (Finset.mem_erase.mp hj).1]
        have hatt : ChordalResidualExtension.residual g p' = attach a r c z :=
          residual_update g hg p a z
        refine ⟨p', ?_, ?_⟩
        · intro i hi j hj hij
          by_cases hiA : i = a
          · subst i
            rw [residual_skew hg p' j a, norm_neg, hatt]
            simpa [attach, hij.ne.symm] using
              hz j (Finset.mem_filter.mpr ⟨hj, hij.symm⟩)
          by_cases hjA : j = a
          · subst j
            rw [hatt]
            simpa [attach, hiA] using hz i (Finset.mem_filter.mpr ⟨hi, hij⟩)
          rw [keep (Finset.mem_erase.mpr ⟨hiA, hi⟩) (Finset.mem_erase.mpr ⟨hjA, hj⟩)]
          exact he i (Finset.mem_erase.mpr ⟨hiA, hi⟩) j (Finset.mem_erase.mpr ⟨hjA, hj⟩) hij
        · intro W hWS hW hcard
          by_cases haW : a ∈ W
          · have hWK : W.erase a ⊆ K := by
              intro i hi
              obtain ⟨hiA, hiW⟩ := Finset.mem_erase.mp hi
              exact Finset.mem_filter.mpr ⟨hWS hiW, hW hiW haW hiA⟩
            have hc : (W.erase a).card < s := by
              rw [Finset.card_erase_of_mem haW]
              have := Finset.card_pos.mpr (⟨a, haW⟩)
              omega
            have hh := hchild (W.erase a) hWK hc
            rwa [Finset.insert_erase haW, ← hatt] at hh
          · have hWe : W ⊆ S.erase a := by
              intro i hi
              exact Finset.mem_erase.mpr ⟨fun h => haW (h ▸ hi), hWS hi⟩
            exact (hlocal W r (ChordalResidualExtension.residual g p')
              (fun i hi j hj => (keep (hWe hi) (hWe hj)).symm)).mp
              (hp W hWe hW hcard)
      · refine ⟨fun _ => 0, ?_, ?_⟩
        · intro i hi
          exact (hS ⟨i, hi⟩).elim
        · intro W hW _ _
          have : W = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i hi => hS ⟨i, hW hi⟩
          subst W
          exact hempty _
  obtain ⟨p, he, hp⟩ := main Finset.univ
  exact ⟨p, fun i j hij => he i (Finset.mem_univ _) j (Finset.mem_univ _) hij,
    fun W hW hc => hp W (Finset.subset_univ _) hW hc⟩

/-- The subset rows used for retained-curl insertion. Empty subsets are included;
that row is the harmless identity `0 ≤ 0`. The pair charge can depend on fixed
gain defects, but does not depend on the candidate center. -/
def SubsetRows (s : ℕ) (cap beta : ℝ) (K : Finset V) (c : V → E)
    (charge : Finset V → ℝ) (z : E) : Prop :=
  ∀ W ⊆ K, W.card < s →
    (∑ i ∈ W, ‖c i - z‖ ^ 2) ≤ (W.card : ℝ) * cap -
      beta * (W.card.choose 2 : ℝ) + beta * ∑ A ∈ W.powersetCard 2, charge A

omit [DecidableEq V] in
/-- Singleton subset rows supply the uniform edge cap. -/
theorem SubsetRows.edge {s : ℕ} {cap beta : ℝ} {K : Finset V} {c : V → E}
    {charge : Finset V → ℝ} {z : E} (h : SubsetRows s cap beta K c charge z)
    (hs : 2 ≤ s) {i : V} (hi : i ∈ K) : ‖c i - z‖ ^ 2 ≤ cap := by
  classical
  have hh := h {i} (Finset.singleton_subset_iff.mpr hi) (by simp; omega)
  have hem : ({i} : Finset V).powersetCard 2 = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simp)
  simpa [hem] using hh


/-- Application interface for a simultaneous subset-row center theorem. The
analytic rule supplies only squared-distance inequalities. `step` identifies
those rows with the chosen invariant on child cliques. -/
theorem reconstruct_of_subset_rows [NormedSpace ℝ E] [Finite V]
    {G : SimpleGraph V} (hG : G.IsChordal)
    (s : ℕ) (hs : 2 ≤ s) (cap beta : ℝ)
    (P : Finset V → (V → V → E) → Prop)
    (hlocal : Local P) (hempty : ∀ r, P ∅ r)
    (charge : V → (V → V → E) → (V → E) → Finset V → ℝ)
    (step : ∀ (a : V) (W : Finset V), a ∉ W → W.card < s →
      ∀ (r : V → V → E) (c : V → E) (z : E), P W r →
      ((∑ i ∈ W, ‖c i - z‖ ^ 2) ≤ (W.card : ℝ) * cap -
        beta * (W.card.choose 2 : ℝ) +
          beta * ∑ A ∈ W.powersetCard 2, charge a r c A) →
      P (insert a W) (attach a r c z))
    (sizeAllowed : ℕ → Prop)
    (hsize : ∀ W : Finset V, G.IsClique (W : Set V) → W.Nonempty →
      sizeAllowed (W.card - 1))
    (g : V → V → E) (hg : Skew g)
    (ht : ∀ i j k, Triangle G i j k → ‖holonomy g i j k‖ ≤ 1)
    (place : ∀ (a : V) (K : Finset V), a ∉ K → G.IsClique (K : Set V) →
      sizeAllowed K.card → ∀ (r : V → V → E) (c : V → E), Skew r →
      (∀ i ∈ K, ∀ j ∈ K, i ≠ j → ‖r i j‖ ^ 2 ≤ cap) →
      (∀ W ⊆ K, W.card ≤ s → P W r) →
      (∀ i ∈ K, ∀ j ∈ K, i ≠ j → ‖r i j - (c i - c j)‖ ≤ 1) →
      (∀ i ∈ K, ∀ j ∈ K, ∀ k ∈ K, Triangle G i j k →
        ‖holonomy r i j k‖ ≤ 1) → Compatible g a K r c →
      ∃ z, SubsetRows s cap beta K c (charge a r c) z) :
    ∃ p : V → E, (∀ i j, G.Adj i j → ‖ChordalResidualExtension.residual g p i j‖ ^ 2 ≤ cap) ∧
      ∀ W : Finset V, G.IsClique (W : Set V) → W.card ≤ s →
        P W (ChordalResidualExtension.residual g p) := by
  apply reconstruct hG s cap P hlocal hempty sizeAllowed hsize g hg ht _
  intro a K ha hK hsize r c hr he hP hd hh hc
  obtain ⟨z, hz⟩ := place a K ha hK hsize r c hr he hP hd hh hc
  refine ⟨z, fun i hi => hz.edge hs hi, ?_⟩
  intro W hWK hWs
  exact step a W (fun h => ha (hWK h)) hWs r c z
    (hP W hWK hWs.le) (hz W hWK hWs)

/-- Sum an arbitrary weight over the unordered `n`-subsets of a clique. -/
def cliqueSum (n : ℕ) (W : Finset V) (f : Finset V → ℝ) : ℝ :=
  ∑ A ∈ W.powersetCard n, f A

/-- The retained deficit/curl inequality. `curl` is fixed gain data; only the
edge deficit weight is changed when the potential is changed. -/
def Retained (beta : ℝ) (deficit curl : Finset V → ℝ) (W : Finset V) : Prop :=
  beta * (W.card.choose 3 : ℝ) ≤ cliqueSum 2 W deficit + beta * cliqueSum 3 W curl

/-- Inserting one vertex splits unordered subsets into old subsets and subsets
containing the new vertex. -/
theorem cliqueSum_insert {a : V} {W : Finset V} (ha : a ∉ W)
    (n : ℕ) (f : Finset V → ℝ) :
    cliqueSum (n + 1) (insert a W) f = cliqueSum (n + 1) W f +
      cliqueSum n W (fun A => f (insert a A)) := by
  unfold cliqueSum
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union]
  · congr 1
    apply Finset.sum_image
    intro A hA B hB heq
    have haA : a ∉ A := fun h => ha ((Finset.mem_powersetCard.mp hA).1 h)
    have haB : a ∉ B := fun h => ha ((Finset.mem_powersetCard.mp hB).1 h)
    simpa [haA, haB] using congrArg (Finset.erase · a) heq
  · apply Finset.disjoint_left.mpr
    intro A hA hB
    obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hB
    exact ha ((Finset.mem_powersetCard.mp hA).1 (Finset.mem_insert_self a B))

omit [DecidableEq V] in
/-- The singleton sum in the insertion formula is an ordinary vertex sum. -/
theorem cliqueSum_one (W : Finset V) (f : Finset V → ℝ) :
    cliqueSum 1 W f = ∑ i ∈ W, f {i} := by
  classical
  unfold cliqueSum
  rw [Finset.powersetCard_one, Finset.sum_map]
  rfl

/-- Arithmetic telescoping on a child clique: the subset squared-distance row
adds exactly the new edge deficits and new fixed curl squares. This is (16)--(17),
including cliques with fewer than three vertices. No sign hypothesis on `beta`
is needed for this purely additive step. -/
theorem retained_insert {a : V} {W : Finset V} (ha : a ∉ W)
    (cap beta : ℝ) (deficit curl : Finset V → ℝ) (c : V → E) (z : E)
    (hold : Retained beta deficit curl W)
    (hedge : ∀ i ∈ W, deficit (insert a {i}) = cap - ‖c i - z‖ ^ 2)
    (hrow : (∑ i ∈ W, ‖c i - z‖ ^ 2) ≤ (W.card : ℝ) * cap -
      beta * (W.card.choose 2 : ℝ) +
        beta * cliqueSum 2 W (fun A => curl (insert a A))) :
    Retained beta deficit curl (insert a W) := by
  have he : cliqueSum 1 W (fun A => deficit (insert a A)) =
      (W.card : ℝ) * cap - ∑ i ∈ W, ‖c i - z‖ ^ 2 := by
    rw [cliqueSum_one]
    rw [Finset.sum_congr rfl hedge]
    simp [Finset.sum_sub_distrib]
  unfold Retained at hold ⊢
  rw [show 2 = 1 + 1 by rfl, cliqueSum_insert ha 1 deficit, he,
    show 3 = 2 + 1 by rfl, cliqueSum_insert ha 2 curl,
    Finset.card_insert_of_notMem ha, Nat.choose_succ_succ]
  push_cast
  linarith

/-- Deficit on an unordered edge. The symmetric formula avoids choosing an
order on the vertices. On a two-element set each edge is counted once. -/
noncomputable def edgeDeficit (cap : ℝ) (r : V → V → E) (A : Finset V) : ℝ :=
  (∑ i ∈ A, ∑ j ∈ A, if i = j then 0 else cap - ‖r i j‖ ^ 2) / 2

/-- Curl square on an unordered triangle, averaged over its six orientations.
For a skew gain field all six summands are the same squared norm. -/
noncomputable def curlSquare (g : V → V → E) (A : Finset V) : ℝ :=
  (∑ i ∈ A, ∑ j ∈ A, ∑ k ∈ A,
    if i = j ∨ j = k ∨ i = k then 0 else ‖holonomy g i j k‖ ^ 2) / 6

omit [DecidableEq V] in
/-- Reversing the first two vertices negates the curl. -/
theorem holonomy_swap (g : V → V → E) (hg : Skew g) (i j k : V) :
    holonomy g j i k = -holonomy g i j k := by
  unfold holonomy
  rw [hg i j]
  abel

/-- The symmetric triangle weight is the usual squared curl norm. -/
theorem curlSquare_triple (g : V → V → E) (hg : Skew g)
    {a i j : V} (hai : a ≠ i) (haj : a ≠ j) (hij : i ≠ j) :
    curlSquare g (insert a {i, j}) = ‖holonomy g i j a‖ ^ 2 := by
  have h₁ : holonomy g a i j = holonomy g i j a := (holonomy_rotate g hg a i j).symm
  have h₂ : holonomy g j a i = holonomy g i j a := holonomy_rotate g hg i j a
  have h₃ : holonomy g j i a = -holonomy g i j a := holonomy_swap g hg i j a
  have h₄ : holonomy g i a j = -holonomy g i j a := by
    rw [holonomy_swap g hg a i j, h₁]
  have h₅ : holonomy g a j i = -holonomy g i j a := by
    rw [holonomy_swap g hg j a i, h₂]
  simp [curlSquare, hai, haj, hij, hai.symm, haj.symm, hij.symm,
    h₁, h₂, h₃, h₄, h₅]
  ring

/-- The symmetric edge weight is the usual deficit for a skew residual. -/
theorem edgeDeficit_pair (cap : ℝ) (r : V → V → E) (hr : Skew r)
    {i j : V} (hij : i ≠ j) :
    edgeDeficit cap r {i, j} = cap - ‖r i j‖ ^ 2 := by
  simp [edgeDeficit, hij, hij.symm, hr i j]

/-- The charge in a new pair row is precisely the squared fixed gain defect. -/
theorem Compatible.curlSquare_pair {g : V → V → E} (hg : Skew g)
    {a : V} {K : Finset V} {r : V → V → E} {c : V → E}
    (hc : Compatible g a K r c) (ha : a ∉ K)
    {i j : V} (hi : i ∈ K) (hj : j ∈ K) (hij : i ≠ j) :
    curlSquare g (insert a {i, j}) = ‖r i j - (c i - c j)‖ ^ 2 := by
  rw [hc.defect i hi j hj]
  exact curlSquare_triple g hg (fun h => ha (h ▸ hi)) (fun h => ha (h ▸ hj)) hij

/-- Edge deficits depend only on residuals inside the edge set. -/
theorem edgeDeficit_congr (cap : ℝ) (A : Finset V) (r r' : V → V → E)
    (h : ∀ i ∈ A, ∀ j ∈ A, r i j = r' i j) :
    edgeDeficit cap r A = edgeDeficit cap r' A := by
  unfold edgeDeficit
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [h i hi j hj]

/-- On a new edge the deficit is exactly cap minus squared candidate distance. -/
theorem edgeDeficit_attach (cap : ℝ) (a i : V) (hai : a ≠ i)
    (r : V → V → E) (c : V → E) (z : E) :
    edgeDeficit cap (attach a r c z) (insert a {i}) = cap - ‖c i - z‖ ^ 2 := by
  simp [edgeDeficit, attach, hai, hai.symm, norm_sub_rev]

/-- The retained-curl predicate with concrete residual edge deficits and fixed
gain curl weights satisfies the locality requirement for graph induction. -/
theorem retained_local (cap beta : ℝ) (curl : Finset V → ℝ) :
    Local (fun W (r : V → V → E) => Retained beta (edgeDeficit cap r) curl W) := by
  intro W r r' h
  have he : cliqueSum 2 W (edgeDeficit cap r) = cliqueSum 2 W (edgeDeficit cap r') := by
    apply Finset.sum_congr rfl
    intro A hA
    have hAW := (Finset.mem_powersetCard.mp hA).1
    exact edgeDeficit_congr cap A r r' (fun i hi j hj => h i (hAW hi) j (hAW hj))
  simp only [Retained, he]

/-- A subset row preserves the concrete retained-curl inequality on the child.
The curl weights are fixed independently of the potential and the center. -/
theorem retained_attach {a : V} {W : Finset V} (ha : a ∉ W)
    (cap beta : ℝ) (curl : Finset V → ℝ) (r : V → V → E) (c : V → E) (z : E)
    (hold : Retained beta (edgeDeficit cap r) curl W)
    (hrow : (∑ i ∈ W, ‖c i - z‖ ^ 2) ≤ (W.card : ℝ) * cap -
      beta * (W.card.choose 2 : ℝ) +
        beta * cliqueSum 2 W (fun A => curl (insert a A))) :
    Retained beta (edgeDeficit cap (attach a r c z)) curl (insert a W) := by
  have heq : Retained beta (edgeDeficit cap (attach a r c z)) curl W := by
    apply (retained_local (E := E) cap beta curl W r (attach a r c z) ?_).mp hold
    intro i hi j hj
    have hiA : i ≠ a := fun h => ha (h ▸ hi)
    have hjA : j ≠ a := fun h => ha (h ▸ hj)
    simp [attach, hiA, hjA]
  exact retained_insert ha cap beta _ curl c z heq
    (fun i hi => edgeDeficit_attach cap a i (fun h => ha (h ▸ hi)) r c z) hrow

omit [DecidableEq V] in
/-- Fixed gain defects agree with the prospective new curls before placement;
the expression does not involve the chosen center. -/
theorem candidate_defect (g : V → V → E) (p : V → E) (a i j : V) :
    ChordalResidualExtension.residual g p i j -
      ((g i a + p i) - (g j a + p j)) = holonomy g i j a := by
  unfold ChordalResidualExtension.residual holonomy
  abel

/-- Retained-curl reconstruction from simultaneous subset squared-distance
inequalities, with the gain field and its unordered curl squares fixed. -/
theorem reconstruct_retained [NormedSpace ℝ E] [Finite V] {G : SimpleGraph V} (hG : G.IsChordal)
    (s : ℕ) (hs : 2 ≤ s) (cap beta : ℝ) (sizeAllowed : ℕ → Prop)
    (hsize : ∀ W : Finset V, G.IsClique (W : Set V) → W.Nonempty →
      sizeAllowed (W.card - 1))
    (g : V → V → E) (hg : Skew g)
    (ht : ∀ i j k, Triangle G i j k → ‖holonomy g i j k‖ ≤ 1)
    (place : ∀ (a : V) (K : Finset V), a ∉ K → G.IsClique (K : Set V) →
      sizeAllowed K.card → ∀ (r : V → V → E) (c : V → E), Skew r →
      (∀ i ∈ K, ∀ j ∈ K, i ≠ j → ‖r i j‖ ^ 2 ≤ cap) →
      (∀ W ⊆ K, W.card ≤ s → Retained beta (edgeDeficit cap r) (curlSquare g) W) →
      (∀ i ∈ K, ∀ j ∈ K, i ≠ j → ‖r i j - (c i - c j)‖ ≤ 1) →
      Compatible g a K r c →
      (∀ i ∈ K, ∀ j ∈ K, ∀ k ∈ K, Triangle G i j k →
        ‖holonomy r i j k‖ ≤ 1) →
      ∃ z, SubsetRows s cap beta K c (fun A => curlSquare g (insert a A)) z) :
    ∃ p : V → E, (∀ i j, G.Adj i j →
      ‖ChordalResidualExtension.residual g p i j‖ ^ 2 ≤ cap) ∧
      ∀ W : Finset V, G.IsClique (W : Set V) → W.card ≤ s →
        Retained beta (edgeDeficit cap (ChordalResidualExtension.residual g p))
          (curlSquare g) W := by
  apply reconstruct hG s cap (fun W r => Retained beta (edgeDeficit cap r) (curlSquare g) W)
    (retained_local (E := E) cap beta _) _ sizeAllowed hsize g hg ht _
  · intro r
    have h₂ : (∅ : Finset V).powersetCard 2 = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simp)
    have h₃ : (∅ : Finset V).powersetCard 3 = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simp)
    simp [Retained, cliqueSum, h₂, h₃]
  · intro a K ha hK hsz r c hr he hP hnew hh hc
    obtain ⟨z, hz⟩ := place a K ha hK hsz r c hr he hP hnew hc hh
    refine ⟨z, fun i hi => hz.edge hs hi, ?_⟩
    intro W hWK hWs
    exact retained_attach (fun h => ha (hWK h)) cap beta _ r c z
      (hP W hWK hWs.le) (hz W hWK hWs)

end SimpleGraph.ChordalCliqueInvariant
