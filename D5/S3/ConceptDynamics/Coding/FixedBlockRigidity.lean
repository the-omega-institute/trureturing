/- GID: D5/S3/ConceptDynamics/Coding/FixedBlockRigidity
   generality: G
   utility: fixed aligned block construction and one-block rigidity
   digest: Endpoint-preserving word bijections construct bilateral block homeomorphisms; unit-shift commutation forces an actual endpoint edge bijection and equality of free-expansion coefficients.
-/
import D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
import D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
import D5.S3.ConceptDynamics.Coding.BipartiteOverlapConjugacy
import D5.S3.ConceptDynamics.Coding.EquivariantOverlapRecoding
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import Mathlib.Logic.Function.Conjugate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FixedBlockRigidity

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion

universe u v w
variable {V : Type u} {E : Type v} {D : Type w}
variable {G : DirectedMultigraph V E} {F : DirectedMultigraph V D}

/-- The exact integer translation of the actual legal history. -/
def translate (G : DirectedMultigraph V E) (a : ℤ) (x : History G) : History G :=
  ⟨fun i => x.val (i + a), fun i => by
    simpa [add_assoc, add_comm, add_left_comm] using x.property (i + a)⟩

@[simp] private theorem translate_zero (x : History G) : translate G 0 x = x := by
  apply Subtype.ext
  funext i
  simp [translate]

@[simp] private theorem translate_add (a b : ℤ) (x : History G) :
    translate G a (translate G b x) = translate G (a + b) x := by
  apply Subtype.ext
  funext i
  simp [translate, add_assoc]

/-- Only the original one-step commutation is assumed. -/
private theorem translate_commutation
    (h : History G → History F)
    (hstep : ∀ x, h (shift G x) = shift F (h x)) :
    ∀ a x, h (translate G a x) = translate F a (h x) := by
  have one : ∀ x, h (translate G 1 x) = translate F 1 (h x) := hstep
  have negOne : ∀ x, h (translate G (-1) x) = translate F (-1) (h x) := by
    intro x
    have t := congrArg (translate F (-1)) (one (translate G (-1) x))
    simpa using t.symm
  have pos : ∀ n : ℕ, ∀ x, h (translate G (n : ℤ) x) = translate F (n : ℤ) (h x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      calc
        h (translate G ((n + 1 : ℕ) : ℤ) x) =
            h (translate G 1 (translate G (n : ℤ) x)) := by
          congr 1
          rw [translate_add]
          congr 1
          omega
        _ = translate F 1 (h (translate G (n : ℤ) x)) := one _
        _ = translate F ((n + 1 : ℕ) : ℤ) (h x) := by
          rw [ih, translate_add]
          congr 1
          omega
  have neg : ∀ n : ℕ, ∀ x, h (translate G (-(n : ℤ)) x) =
      translate F (-(n : ℤ)) (h x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      calc
        h (translate G (-((n + 1 : ℕ) : ℤ)) x) =
            h (translate G (-1) (translate G (-(n : ℤ)) x)) := by
          congr 1
          rw [translate_add]
          congr 1
          omega
        _ = translate F (-1) (h (translate G (-(n : ℤ)) x)) := negOne _
        _ = translate F (-((n + 1 : ℕ) : ℤ)) (h x) := by
          rw [ih, translate_add]
          congr 1
          omega
  intro a x
  cases a with
  | ofNat n => exact pos n x
  | negSucc n => simpa [Int.negSucc_eq] using neg (n + 1) x

/-- The law names the same f, the same h and every fixed aligned block. -/
def FixedBlockLaw {k : ℕ} (f : LegalWord G k ≃ LegalWord F k)
    (h : History G → History F) : Prop :=
  ∀ (x : History G) (j : ℤ),
    historyWindow F (h x) (j * (k : ℤ)) k =
      f (historyWindow G x (j * (k : ℤ)) k)

/-- The two original path endpoints, with no forgotten parallel-edge identities. -/
def PreservesBlockEndpoints {k : ℕ} (hk : 0 < k)
    (f : LegalWord G k ≃ LegalWord F k) : Prop :=
  ∀ w,
    F.source ((f w).edge ⟨0, hk⟩) = G.source (w.edge ⟨0, hk⟩) ∧
    F.target ((f w).edge ⟨k - 1, by omega⟩) =
      G.target (w.edge ⟨k - 1, by omega⟩)


/-- Euclidean addresses, including every negative position. -/
def blockAddress {k : ℕ} (hk : 0 < k) (i : ℤ) : ℤ × Fin k :=
  (i / (k : ℤ), ⟨(i % (k : ℤ)).toNat, by
    have hnonneg := Int.emod_nonneg i (show (k : ℤ) ≠ 0 by omega)
    have hlt := Int.emod_lt_of_pos i (show (0 : ℤ) < k by omega)
    omega⟩)

private def assemble (k : ℕ) (p : ℤ × Fin k) : ℤ := p.1 * (k : ℤ) + p.2.val

private theorem assemble_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective (assemble k) := by
  intro a b hab
  rcases a with ⟨a,r⟩
  rcases b with ⟨b,s⟩
  have hp : (0 : ℤ) < k := by omega
  have hr : (0 : ℤ) ≤ r.val ∧ (r.val : ℤ) < k := by omega
  have hs : (0 : ℤ) ≤ s.val ∧ (s.val : ℤ) < k := by omega
  change a * (k : ℤ) + r.val = b * (k : ℤ) + s.val at hab
  have qab : a = b := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hd : 1 ≤ b - a := by omega
      have hm : (k : ℤ) ≤ (b - a) * k := by nlinarith
      nlinarith
    · have hd : 1 ≤ a - b := by omega
      have hm : (k : ℤ) ≤ (a - b) * k := by nlinarith
      nlinarith
  subst b
  have rs : r = s := by apply Fin.ext; omega
  subst s
  rfl

theorem assemble_address {k : ℕ} (hk : 0 < k) (i : ℤ) :
    assemble k (blockAddress hk i) = i := by
  have hnonneg := Int.emod_nonneg i (show (k : ℤ) ≠ 0 by omega)
  have hdiv := Int.ediv_mul_add_emod i (k : ℤ)
  simp only [assemble, blockAddress, Int.toNat_of_nonneg hnonneg]
  nlinarith

private theorem address_assemble {k : ℕ} (hk : 0 < k) (p : ℤ × Fin k) :
    blockAddress hk (assemble k p) = p :=
  assemble_injective hk (assemble_address hk (assemble k p))

/-- The actual output formula: no edge map or one-blockness is assumed. -/
def blockOutput {k : ℕ} (hk : 0 < k)
    (f : LegalWord G k ≃ LegalWord F k) (x : History G) (i : ℤ) : D :=
  let a := blockAddress hk i
  (f (historyWindow G x (a.1 * (k : ℤ)) k)).edge a.2

private theorem blockOutput_at {k : ℕ} (hk : 0 < k)
    (f : LegalWord G k ≃ LegalWord F k) (x : History G) (q : ℤ) (r : Fin k) :
    blockOutput hk f x (assemble k (q,r)) =
      (f (historyWindow G x (q * (k : ℤ)) k)).edge r := by
  simp only [blockOutput, address_assemble]

private theorem inverse_endpoints {k : ℕ} (hk : 0 < k)
    (f : LegalWord G k ≃ LegalWord F k) (ep : PreservesBlockEndpoints hk f) :
    PreservesBlockEndpoints hk f.symm := by
  intro w
  have h := ep (f.symm w)
  simpa using And.intro h.1.symm h.2.symm

/-- Both internal edges and inter-block seams are checked on actual endpoints. -/
private theorem blockOutput_legal {k : ℕ} (hk : 0 < k)
    (f : LegalWord G k ≃ LegalWord F k) (ep : PreservesBlockEndpoints hk f)
    (x : History G) (i : ℤ) :
    F.target (blockOutput hk f x i) = F.source (blockOutput hk f x (i+1)) := by
  let q := (blockAddress hk i).1
  let r := (blockAddress hk i).2
  have rep : assemble k (q,r) = i := assemble_address hk i
  rw [← rep]
  by_cases hn : r.val + 1 < k
  · let r' : Fin k := ⟨r.val+1,hn⟩
    have next : assemble k (q,r) + 1 = assemble k (q,r') := by
      simp only [assemble, r', Int.natCast_add, Int.natCast_one]
      ring
    rw [next, blockOutput_at, blockOutput_at]
    exact (f (historyWindow G x (q * (k : ℤ)) k)).legal r hn
  · have hlast : r = (⟨k-1,by omega⟩ : Fin k) := by apply Fin.ext; dsimp; omega
    let zero : Fin k := ⟨0,hk⟩
    have next : assemble k (q,r)+1 = assemble k (q+1,zero) := by
      simp only [assemble, zero, Fin.val_mk, Int.natCast_zero]
      have hr : (r.val : ℤ) + 1 = k := by omega
      nlinarith
    rw [next, blockOutput_at, blockOutput_at]
    calc
      F.target ((f (historyWindow G x (q * (k : ℤ)) k)).edge r) =
          G.target (x.val (assemble k (q,r))) := by
        simpa [historyWindow, assemble, hlast] using (ep (historyWindow G x (q*(k:ℤ)) k)).2
      _ = G.source (x.val (assemble k (q+1,zero))) := by
        simpa [next] using x.property (assemble k (q,r))
      _ = F.source ((f (historyWindow G x ((q+1)*(k:ℤ)) k)).edge zero) := by
        simpa [historyWindow, assemble, zero] using
          (ep (historyWindow G x ((q+1)*(k:ℤ)) k)).1.symm

/-- Total fixed-alignment replacement of the full legal history. -/
def blockMap {k : ℕ} (hk : 0 < k) (f : LegalWord G k ≃ LegalWord F k)
    (ep : PreservesBlockEndpoints hk f) (x : History G) : History F :=
  ⟨blockOutput hk f x, blockOutput_legal hk f ep x⟩

private theorem blockMap_law {k : ℕ} (hk : 0 < k)
    (f : LegalWord G k ≃ LegalWord F k) (ep : PreservesBlockEndpoints hk f) :
    FixedBlockLaw f (blockMap hk f ep) := by
  intro x q
  apply legalWord_ext
  funext r
  change blockOutput hk f x (assemble k (q,r)) = _
  exact blockOutput_at hk f x q r

private theorem blockMap_leftInverse {k : ℕ} (hk : 0 < k)
    (f : LegalWord G k ≃ LegalWord F k) (ep : PreservesBlockEndpoints hk f) :
    Function.LeftInverse (blockMap hk f.symm (inverse_endpoints hk f ep))
      (blockMap hk f ep) := by
  intro x
  apply Subtype.ext
  funext i
  let q := (blockAddress hk i).1
  let r := (blockAddress hk i).2
  have rep : assemble k (q,r) = i := assemble_address hk i
  rw [← rep]
  change blockOutput hk f.symm (blockMap hk f ep x) (assemble k (q,r)) = _
  rw [blockOutput_at, blockMap_law hk f ep x q, f.symm_apply_apply]
  rfl

private theorem blockMap_rightInverse {k : ℕ} (hk : 0 < k)
    (f : LegalWord G k ≃ LegalWord F k) (ep : PreservesBlockEndpoints hk f) :
    Function.RightInverse (blockMap hk f.symm (inverse_endpoints hk f ep))
      (blockMap hk f ep) := by
  intro y
  simpa using blockMap_leftInverse hk f.symm (inverse_endpoints hk f ep) y

private theorem blockMap_continuous
    [TopologicalSpace E] [DiscreteTopology E] [TopologicalSpace D]
    {k : ℕ} (hk : 0 < k) (f : LegalWord G k ≃ LegalWord F k)
    (ep : PreservesBlockEndpoints hk f) : Continuous (blockMap hk f ep) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  let q := (blockAddress hk i).1
  let r := (blockAddress hk i).2
  have localContinuous : Continuous (fun w : LegalWord G k => (f w).edge r) :=
    continuous_of_discreteTopology
  exact localContinuous.comp (historyWindow_continuous G (q*(k:ℤ)) k)

/-- The homeomorphism in the source is constructed, not provided as a hypothesis. -/
def blockHomeomorph [TopologicalSpace E] [DiscreteTopology E]
    [TopologicalSpace D] [DiscreteTopology D]
    {k : ℕ} (hk : 0 < k) (f : LegalWord G k ≃ LegalWord F k)
    (ep : PreservesBlockEndpoints hk f) : History G ≃ₜ History F where
  toFun := blockMap hk f ep
  invFun := blockMap hk f.symm (inverse_endpoints hk f ep)
  left_inv := blockMap_leftInverse hk f ep
  right_inv := blockMap_rightInverse hk f ep
  continuous_toFun := blockMap_continuous hk f ep
  continuous_invFun := blockMap_continuous hk f.symm (inverse_endpoints hk f ep)

/-- Past from x, future from y, joined at their shared actual edge. -/
private def splice (x y : History G) (hzero : x.val 0 = y.val 0) : History G :=
  ⟨fun i => if i ≤ 0 then x.val i else y.val i, by
    intro i
    by_cases hi : i ≤ 0
    · by_cases hnext : i + 1 ≤ 0
      · simpa only [if_pos hi, if_pos hnext] using x.property i
      · have iz : i = 0 := by omega
        subst i
        simpa only [le_refl, if_true, show ¬ (1 : ℤ) ≤ 0 by omega, if_false,
          zero_add, hzero] using y.property 0
    · have hnext : ¬ i + 1 ≤ 0 := by omega
      simpa only [if_neg hi, if_neg hnext] using y.property i⟩

/-- The non-normalization step: two separated windows collapse to the shared edge. -/
private theorem center_depends_only_on_edge {k : ℕ} (hk : 0 < k)
    (f : LegalWord G k ≃ LegalWord F k) (h : History G → History F)
    (blocks : FixedBlockLaw f h)
    (hstep : ∀ x, h (shift G x) = shift F (h x))
    (x y : History G) (hzero : x.val 0 = y.val 0) :
    (h x).val 0 = (h y).val 0 := by
  have same_window_output (a b : History G)
      (same : ∀ j : Fin k, a.val (j.val : ℤ) = b.val (j.val : ℤ))
      (t : Fin k) : (h a).val (t.val : ℤ) = (h b).val (t.val : ℤ) := by
    have win : historyWindow G a 0 k = historyWindow G b 0 k := by
      apply legalWord_ext
      funext j
      simpa [historyWindow] using same j
    have out : historyWindow F (h a) 0 k = historyWindow F (h b) 0 k := by
      have ha := blocks a 0
      have hb := blocks b 0
      simp only [zero_mul] at ha hb
      exact ha.trans ((congrArg f win).trans hb.symm)
    simpa [historyWindow] using congrArg (fun w : LegalWord F k => w.edge t) out
  let z := splice x y hzero
  have zy : (h z).val 0 = (h y).val 0 := by
    apply same_window_output z y _ ⟨0, hk⟩
    intro j
    change (if (j.val : ℤ) ≤ 0 then x.val (j.val : ℤ) else y.val (j.val : ℤ)) = _
    by_cases hj : (j.val : ℤ) ≤ 0
    · have jz : (j.val : ℤ) = 0 := by omega
      simp [hj, jz, hzero]
    · exact if_neg hj
  have zx : (h z).val 0 = (h x).val 0 := by
    let t : Fin k := ⟨k - 1, by omega⟩
    let a : ℤ := -(t.val : ℤ)
    have shifted : (h (translate G a z)).val (t.val : ℤ) =
        (h (translate G a x)).val (t.val : ℤ) := by
      apply same_window_output _ _ _ t
      intro j
      have hj : (j.val : ℤ) + a ≤ 0 := by dsimp [a, t]; omega
      simp [translate, z, splice, hj]
    rw [translate_commutation h hstep, translate_commutation h hstep] at shifted
    simpa only [translate, a, add_neg_cancel] using shifted
  exact zx.symm.trans zy

section Finite
variable [Fintype V] [Fintype E] [Fintype D] [DecidableEq V]

private theorem edge_occurs (hG : Essential G) (e : E) :
    ∃ x : History G, x.val 0 = e := by
  let w : LegalWord G 1 := ⟨fun _ => e, by intro i hi; omega⟩
  obtain ⟨x, hx⟩ := exists_history_containing G hG w (by decide)
  exact ⟨x, by simpa [w] using hx ⟨0, by decide⟩⟩

/-- Extract the common edge map from the actual blocks, rather than assuming locality. -/
private theorem extract_edge_map {k : ℕ} (hk : 0 < k) (hG : Essential G)
    (f : LegalWord G k ≃ LegalWord F k) (h : History G → History F)
    (blocks : FixedBlockLaw f h)
    (hstep : ∀ x, h (shift G x) = shift F (h x)) :
    ∃ γ : E → D, ∀ x i, (h x).val i = γ (x.val i) := by
  classical
  let realized : E → History G := fun e => Classical.choose (edge_occurs hG e)
  have occurs (e : E) : (realized e).val 0 = e :=
    Classical.choose_spec (edge_occurs hG e)
  refine ⟨fun e => (h (realized e)).val 0, ?_⟩
  intro x i
  have hcenter := center_depends_only_on_edge hk f h blocks hstep
    (translate G i x) (realized (x.val i)) (by simpa [translate] using (occurs (x.val i)).symm)
  rw [translate_commutation h hstep] at hcenter
  simpa only [translate, zero_add] using hcenter

/-- Internal rigidity step for the actual block law; consumed by original18_3. -/
private theorem rigidity_of_fixed_block_law {k : ℕ} (hk : 0 < k)
    (hG : Essential G) (hF : Essential F)
    (f : LegalWord G k ≃ LegalWord F k)
    (endpoints : PreservesBlockEndpoints hk f)
    (h : History G ≃ History F)
    (blocks : FixedBlockLaw f h)
    (hstep : ∀ x, h (shift G x) = shift F (h x)) :
    ∃ γ : E ≃ D,
      (∀ x i, (h x).val i = γ (x.val i)) ∧
      (∀ e, F.source (γ e) = G.source e ∧ F.target (γ e) = G.target e) := by
  classical
  have invBlocks : FixedBlockLaw f.symm h.symm := by
    intro y j
    have hb := congrArg f.symm (blocks (h.symm y) j)
    simpa using hb.symm
  have invStep : ∀ y, h.symm (shift F y) = shift G (h.symm y) :=
    (show Function.Semiconj h (shift G) (shift F) from hstep).inverse_left
      h.left_inv h.right_inv
  obtain ⟨γ, hγ⟩ := extract_edge_map hk hG f h blocks hstep
  obtain ⟨δ, hδ⟩ := extract_edge_map hk hF f.symm h.symm invBlocks invStep
  have left : Function.LeftInverse δ γ := by
    intro e
    obtain ⟨x, hx⟩ := edge_occurs hG e
    calc
      δ (γ e) = δ ((h x).val 0) := by rw [hγ, hx]
      _ = (h.symm (h x)).val 0 := (hδ (h x) 0).symm
      _ = e := by simpa using hx
  have right : Function.RightInverse δ γ := by
    intro d
    obtain ⟨y, hy⟩ := edge_occurs hF d
    calc
      γ (δ d) = γ ((h.symm y).val 0) := by rw [hδ, hy]
      _ = (h (h.symm y)).val 0 := (hγ (h.symm y) 0).symm
      _ = d := by simpa using hy
  let edgeEquiv : E ≃ D := ⟨γ, δ, left, right⟩
  have source0 (x : History G) : F.source ((h x).val 0) = G.source (x.val 0) := by
    have zero := congrArg (fun w : LegalWord F k => w.edge ⟨0, hk⟩) (blocks x 0)
    simp only [zero_mul] at zero
    have ep := (endpoints (historyWindow G x 0 k)).1
    simpa only [historyWindow, add_zero, Int.natCast_zero] using (congrArg F.source zero).trans ep
  have sourceEvery (x : History G) (i : ℤ) :
      F.source ((h x).val i) = G.source (x.val i) := by
    have hs := source0 (translate G i x)
    rw [translate_commutation h hstep] at hs
    simpa only [translate, zero_add] using hs
  refine ⟨edgeEquiv, hγ, ?_⟩
  intro e
  obtain ⟨x, hx⟩ := edge_occurs hG e
  have hs := sourceEvery x 0
  have ht : F.target ((h x).val 0) = G.target (x.val 0) := by
    calc
      F.target ((h x).val 0) = F.source ((h x).val 1) := by simpa using (h x).property 0
      _ = G.source (x.val 1) := sourceEvery x 1
      _ = G.target (x.val 0) := by simpa using (x.property 0).symm
  exact ⟨by simpa [edgeEquiv, hγ, hx] using hs,
    by simpa [edgeEquiv, hγ, hx] using ht⟩


/-- Original18.3, referring to the exact homeomorphism constructed from f.
The only dynamical hypothesis is unit-time commutation of this same map. -/
theorem original18_3 [TopologicalSpace E] [DiscreteTopology E]
    [TopologicalSpace D] [DiscreteTopology D]
    {k : ℕ} (hk : 0 < k) (hG : Essential G) (hF : Essential F)
    (f : LegalWord G k ≃ LegalWord F k) (ep : PreservesBlockEndpoints hk f)
    (hstep : ∀ x, blockHomeomorph hk f ep (shift G x) =
      shift F (blockHomeomorph hk f ep x)) :
    ∃ γ : E ≃ D,
      (∀ x i, (blockHomeomorph hk f ep x).val i = γ (x.val i)) ∧
      (∀ e, F.source (γ e) = G.source e ∧ F.target (γ e) = G.target e) := by
  exact rigidity_of_fixed_block_law hk hG hF f ep
    (blockHomeomorph hk f ep).toEquiv (blockMap_law hk f ep) hstep

end Finite
end D5.S3.ConceptDynamics.Coding.FixedBlockRigidity

namespace D5.S3.ConceptDynamics.Coding.FixedBlockRigidity

open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat Edge)

universe u
variable {H : Type u} [Group H] [Fintype H] {n : ℕ}

private def edgeCoordinates (A : GroupMat H n n) : Edge A ≃
    (Σ i : Fin n, Σ j : Fin n, Σ g : H, Fin ((A i j).coeff g)) where
  toFun e := ⟨e.source, e.target, e.label, e.number⟩
  invFun e := ⟨e.1, e.2.1, e.2.2.1, e.2.2.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by rcases e with ⟨i,j,g,t⟩; rfl

private theorem edge_eq_of_coordinates {A : GroupMat H n n} {a b : Edge A}
    (hs : a.source = b.source) (ht : a.target = b.target)
    (hl : a.label = b.label) (hn : a.number.val = b.number.val) : a = b := by
  cases a with
  | mk i j g t =>
    cases b with
    | mk i' j' g' t' =>
      dsimp at hs ht hl hn
      subst i'
      subst j'
      subst g'
      have h : t = t' := Fin.ext hn
      subst t'
      rfl

private noncomputable instance edgeFintype (A : GroupMat H n n) : Fintype (Edge A) :=
  Fintype.ofEquiv _ (edgeCoordinates A).symm

/-- Existing counted edges, with their actual group coordinate retained. -/
def baseGraph (A : GroupMat H n n) : DirectedMultigraph (Fin n) (Edge A) :=
  ⟨Edge.source, Edge.target⟩

def expandedGraph (A : GroupMat H n n) :
    DirectedMultigraph (Fin n × H) (Edge A × H) :=
  ⟨fun p => (p.1.source, p.2), fun p => (p.1.target, p.2 * p.1.label)⟩

private theorem essential_expanded (A : GroupMat H n n)
    (hA : Essential (baseGraph A)) : Essential (expandedGraph A) := by
  constructor
  · intro v
    obtain ⟨e, he⟩ := hA.outgoing v.1
    exact ⟨(e, v.2), Prod.ext he rfl⟩
  · intro v
    obtain ⟨e, he⟩ := hA.incoming v.1
    refine ⟨(e, v.2 * e.label⁻¹), ?_⟩
    apply Prod.ext
    · exact he
    · simp [expandedGraph, mul_assoc]

private abbrev fixedFiber (A : GroupMat H n n) (i j : Fin n) (g : H) :=
  {p : Edge A × H //
    (expandedGraph A).source p = (i, 1) ∧
    (expandedGraph A).target p = (j, g)}

/-- No quotient forgets a parallel edge or a group coordinate. -/
private noncomputable def coefficientFiber (A : GroupMat H n n)
    (i j : Fin n) (g : H) : Fin ((A i j).coeff g) ≃ fixedFiber A i j g := by
  classical
  let put : Fin ((A i j).coeff g) → fixedFiber A i j g :=
    fun t => ⟨(⟨i,j,g,t⟩,1), by simp [expandedGraph]⟩
  apply Equiv.ofBijective put
  constructor
  · intro a b hab
    have hnum := congrArg (fun p : fixedFiber A i j g => p.val.1.number.val) hab
    exact Fin.ext hnum
  · intro p
    rcases p with ⟨⟨⟨i',j',g',t⟩,a⟩,hs,ht⟩
    have hi : i' = i := congrArg Prod.fst hs
    have ha : a = 1 := congrArg Prod.snd hs
    subst i'
    subst a
    have hj : j' = j := congrArg Prod.fst ht
    have hg : g' = g := by simpa [expandedGraph] using congrArg Prod.snd ht
    subst j'
    subst g'
    exact ⟨t, rfl⟩

/-- Original18.3's entire free-expansion clause: fixed base and group vertices
force literal equality of all natural group-ring coefficients. -/
theorem original18_3_freeExpansion [TopologicalSpace H] [DiscreteTopology H]
    (A B : GroupMat H n n)
    (hA : Essential (baseGraph A)) (hB : Essential (baseGraph B))
    {k : ℕ} (hk : 0 < k)
    (f : LegalWord (expandedGraph A) k ≃ LegalWord (expandedGraph B) k)
    (endpoints : PreservesBlockEndpoints hk f)
    (hstep : ∀ x, blockHomeomorph hk f endpoints (shift (expandedGraph A) x) =
      shift (expandedGraph B) (blockHomeomorph hk f endpoints x)) :
    A = B := by
  classical
  obtain ⟨γ, _, hγ⟩ := original18_3 hk (essential_expanded A hA)
    (essential_expanded B hB) f endpoints hstep
  have coeffEq (i j : Fin n) (g : H) : (A i j).coeff g = (B i j).coeff g := by
    let e : fixedFiber A i j g ≃ fixedFiber B i j g := {
      toFun := fun p => ⟨γ p.val,
        (hγ p.val).1.trans p.property.1,
        (hγ p.val).2.trans p.property.2⟩
      invFun := fun p => ⟨γ.symm p.val, by
        constructor
        · simpa using ((hγ (γ.symm p.val)).1.symm.trans
            (by simpa using p.property.1))
        · simpa using ((hγ (γ.symm p.val)).2.symm.trans
            (by simpa using p.property.2))⟩
      left_inv := by intro p; apply Subtype.ext; exact γ.symm_apply_apply p.val
      right_inv := by intro p; apply Subtype.ext; exact γ.apply_symm_apply p.val }
    let numbers := (coefficientFiber A i j g).trans (e.trans (coefficientFiber B i j g).symm)
    simpa using Fintype.card_congr numbers
  ext i j g
  exact coeffEq i j g

end D5.S3.ConceptDynamics.Coding.FixedBlockRigidity


noncomputable section
set_option autoImplicit false
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (GroupMat Edge)

namespace D5.S3.ConceptDynamics.Coding.FixedBlockRigidity
universe u
variable {H : Type u} [Group H] [Fintype H] {n : ℕ}
local instance : DecidableEq H := Classical.decEq H

/-- Ordered left-to-right prefix products; no commutative group assumption. -/
def prefixLabel {A : GroupMat H n n} {k : ℕ}
    (w : LegalWord (baseGraph A) k) : ℕ → H
  | 0 => 1
  | r + 1 => if hr : r < k then prefixLabel w r * (w.edge ⟨r,hr⟩).label
      else prefixLabel w r

def totalLabel {A : GroupMat H n n} {k : ℕ}
    (w : LegalWord (baseGraph A) k) : H := prefixLabel w k

def wordSource {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (w : LegalWord (baseGraph A) k) : Fin n := (w.edge ⟨0,hk⟩).source

def wordTarget {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (w : LegalWord (baseGraph A) k) : Fin n :=
  (w.edge ⟨k-1,by omega⟩).target

/-- Forget only the evolving group coordinate; every counted edge is retained. -/
def forgetWord {A : GroupMat H n n} {k : ℕ}
    (z : LegalWord (expandedGraph A) k) : LegalWord (baseGraph A) k where
  edge r := (z.edge r).1
  legal r hr := congrArg Prod.fst (z.legal r hr)

/-- The uniquely forced group coordinate before edge r is g times its prefix label. -/
def liftWord {A : GroupMat H n n} {k : ℕ}
    (w : LegalWord (baseGraph A) k) (g : H) : LegalWord (expandedGraph A) k where
  edge r := (w.edge r, g * prefixLabel w r.val)
  legal := by
    intro r hr
    apply Prod.ext
    · exact w.legal r hr
    · change (g * prefixLabel w r.val) * (w.edge r).label =
        g * prefixLabel w (r.val + 1)
      simp only [prefixLabel, dif_pos r.isLt]
      exact mul_assoc _ _ _

private theorem coordinate_forced {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (z : LegalWord (expandedGraph A) k) :
    ∀ r : Fin k, (z.edge r).2 =
      (z.edge ⟨0,hk⟩).2 * prefixLabel (forgetWord z) r.val := by
  have h : ∀ r : ℕ, ∀ hr : r < k,
      (z.edge ⟨r,hr⟩).2 =
        (z.edge ⟨0,hk⟩).2 * prefixLabel (forgetWord z) r := by
    intro r
    induction r with
    | zero => intro hr; simp [prefixLabel]
    | succ r ih =>
      intro hr
      have hprev : r < k := by omega
      have hs := congrArg Prod.snd (z.legal ⟨r,hprev⟩ hr)
      change (z.edge ⟨r,hprev⟩).2 * (z.edge ⟨r,hprev⟩).1.label =
        (z.edge ⟨r+1,hr⟩).2 at hs
      rw [← hs, ih hprev]
      simp only [prefixLabel, dif_pos hprev, forgetWord]
      exact mul_assoc _ _ _
  intro r
  exact h r.val r.isLt

private theorem forget_lift {A : GroupMat H n n} {k : ℕ}
    (w : LegalWord (baseGraph A) k) (g : H) :
    forgetWord (liftWord w g) = w := by
  apply legalWord_ext
  rfl

private theorem lift_forget {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (z : LegalWord (expandedGraph A) k) :
    liftWord (forgetWord z) (z.edge ⟨0,hk⟩).2 = z := by
  apply legalWord_ext
  funext r
  apply Prod.ext
  · rfl
  · exact (coordinate_forced hk z r).symm

/-- Positive expanded words are actual base words plus their initial group coordinate. -/
def expandedWordCoordinates (A : GroupMat H n n) {k : ℕ} (hk : 0 < k) :
    LegalWord (expandedGraph A) k ≃ LegalWord (baseGraph A) k × H where
  toFun z := (forgetWord z, (z.edge ⟨0,hk⟩).2)
  invFun p := liftWord p.1 p.2
  left_inv z := lift_forget hk z
  right_inv p := by
    apply Prod.ext
    · exact forget_lift p.1 p.2
    · simp [liftWord, prefixLabel]

private theorem lift_source {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (w : LegalWord (baseGraph A) k) (g : H) :
    (expandedGraph A).source ((liftWord w g).edge ⟨0,hk⟩) =
      (wordSource hk w,g) := by
  simp [expandedGraph, liftWord, wordSource, prefixLabel]

private theorem lift_target {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (w : LegalWord (baseGraph A) k) (g : H) :
    (expandedGraph A).target ((liftWord w g).edge ⟨k-1,by omega⟩) =
      (wordTarget hk w,g * totalLabel w) := by
  apply Prod.ext
  · rfl
  · have hlast : k-1 < k := by omega
    have hk' : k = (k-1)+1 := by omega
    change (g * prefixLabel w (k-1)) * (w.edge ⟨k-1,hlast⟩).label =
      g * prefixLabel w k
    conv_rhs => arg 2; arg 2; rw [hk']
    simp only [prefixLabel, dif_pos hlast]
    exact mul_assoc _ _ _

/-- This helper is consumed by the concrete fiber-choice construction below. -/
def liftEquiv {A B : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (f : LegalWord (baseGraph A) k ≃ LegalWord (baseGraph B) k) :
    LegalWord (expandedGraph A) k ≃ LegalWord (expandedGraph B) k :=
  (expandedWordCoordinates A hk).trans
    ((Equiv.prodCongr f (Equiv.refl H)).trans (expandedWordCoordinates B hk).symm)

private theorem liftEquiv_endpoints {A B : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (f : LegalWord (baseGraph A) k ≃ LegalWord (baseGraph B) k)
    (hf : ∀ w, wordSource hk (f w) = wordSource hk w ∧
      wordTarget hk (f w) = wordTarget hk w ∧ totalLabel (f w) = totalLabel w) :
    PreservesBlockEndpoints hk (liftEquiv hk f) := by
  intro z
  let w := forgetWord z
  let g := (z.edge ⟨0,hk⟩).2
  have hz : liftWord w g = z := lift_forget hk z
  have ho : liftEquiv hk f z = liftWord (f w) g := rfl
  constructor
  · rw [ho, ← hz, lift_source, lift_source, (hf w).1]
  · rw [ho, ← hz, lift_target hk, lift_target hk, (hf w).2.1, (hf w).2.2]

/-- The actual endpoint/ordered-total-label fiber, including edge numbers. -/
abbrev WordFiber (A : GroupMat H n n) {k : ℕ} (hk : 0 < k)
    (i j : Fin n) (g : H) :=
  {w : LegalWord (baseGraph A) k //
    wordSource hk w = i ∧ wordTarget hk w = j ∧ totalLabel w = g}



private def singletonWord {A : GroupMat H n n} (e : Edge A) :
    LegalWord (baseGraph A) 1 where
  edge _ := e
  legal r hr := by omega

private def oneWordFiberCoordinates (A : GroupMat H n n)
    (i j : Fin n) (g : H) :
    WordFiber A (by omega : 0 < 1) i j g ≃ fixedFiber A i j g where
  toFun w := ⟨(w.val.edge ⟨0,by omega⟩,1), by
    rcases w.property with ⟨hs,ht,hg⟩
    constructor
    · apply Prod.ext
      · exact hs
      · rfl
    · apply Prod.ext
      · simpa [wordTarget, expandedGraph] using ht
      · simpa [expandedGraph,totalLabel,prefixLabel] using hg⟩
  invFun p := ⟨singletonWord p.val.1, by
    have hs := congrArg Prod.fst p.property.1
    have hcoord : p.val.2 = 1 := congrArg Prod.snd p.property.1
    have ht := congrArg Prod.fst p.property.2
    have hg := congrArg Prod.snd p.property.2
    exact ⟨hs,ht,by simpa [totalLabel,prefixLabel,singletonWord,expandedGraph,hcoord] using hg⟩⟩
  left_inv w := by
    apply Subtype.ext
    apply legalWord_ext
    funext r
    have hr : r = (⟨0,by omega⟩ : Fin 1) := by apply Fin.ext; dsimp; omega
    cases hr
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (congrArg Prod.snd p.property.1).symm

private def initialWord {A : GroupMat H n n} {k : ℕ}
    (w : LegalWord (baseGraph A) (k+1)) : LegalWord (baseGraph A) k :=
  sliceWord (baseGraph A) w 0 k (by omega)

private theorem prefix_initial {A : GroupMat H n n} {k : ℕ}
    (w : LegalWord (baseGraph A) (k+1)) (r : ℕ) (hr : r ≤ k) :
    prefixLabel (initialWord w) r = prefixLabel w r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hsmall : r < k := by omega
    have hlarge : r < k+1 := by omega
    simp only [prefixLabel,dif_pos hsmall,dif_pos hlarge,ih (by omega)]
    simp only [initialWord, sliceWord, Nat.zero_add]

private theorem total_initial_last {A : GroupMat H n n} {k : ℕ}
    (w : LegalWord (baseGraph A) (k+1)) :
    totalLabel w = totalLabel (initialWord w) * (w.edge ⟨k,by omega⟩).label := by
  change prefixLabel w (k+1) = _
  rw [prefixLabel]
  simp only [dif_pos (by omega : k < k+1)]
  rw [← prefix_initial w k (by omega)]
  rfl

private theorem initial_last_seam {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (w : LegalWord (baseGraph A) (k+1)) :
    wordTarget hk (initialWord w) = (w.edge ⟨k,by omega⟩).source := by
  have h := w.legal ⟨k-1,by omega⟩ (by dsimp; omega)
  simpa [wordTarget,initialWord,sliceWord,baseGraph,show k-1+1=k by omega] using h

private def snocWord {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (w : LegalWord (baseGraph A) k) (e : Edge A)
    (seam : wordTarget hk w = e.source) : LegalWord (baseGraph A) (k+1) where
  edge r := if hr : r.val < k then w.edge ⟨r.val,hr⟩ else e
  legal r hr := by
    change (baseGraph A).target (if h : r.val < k then w.edge ⟨r.val,h⟩ else e) =
      (baseGraph A).source (if h : r.val + 1 < k then w.edge ⟨r.val + 1,h⟩ else e)
    have hprev : r.val < k := by omega
    by_cases hnext : r.val+1 < k
    · simpa only [dif_pos hprev,dif_pos hnext] using w.legal ⟨r.val,hprev⟩ hnext
    · have hlast : r.val = k-1 := by omega
      simp only [dif_pos hprev,dif_neg hnext]
      change (w.edge ⟨r.val,hprev⟩).target = e.source
      simpa only [hlast,wordTarget] using seam

private theorem snoc_last {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (w : LegalWord (baseGraph A) k) (e : Edge A) (seam : wordTarget hk w = e.source) :
    (snocWord hk w e seam).edge ⟨k,by omega⟩ = e := by
  simp [snocWord]

private theorem initial_snoc {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (w : LegalWord (baseGraph A) k) (e : Edge A) (seam : wordTarget hk w = e.source) :
    initialWord (snocWord hk w e seam) = w := by
  apply legalWord_ext
  funext r
  simp [initialWord,sliceWord,snocWord,r.isLt]

private theorem snoc_initial {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (w : LegalWord (baseGraph A) (k+1)) :
    snocWord hk (initialWord w) (w.edge ⟨k,by omega⟩) (initial_last_seam hk w) = w := by
  apply legalWord_ext
  funext r
  by_cases hr : r.val < k
  · change (if h : r.val < k then (initialWord w).edge ⟨r.val,h⟩ else _) = w.edge r
    simp only [dif_pos hr,initialWord,sliceWord,Nat.zero_add]
  · have heq : r = (⟨k,by omega⟩ : Fin (k+1)) := by apply Fin.ext; dsimp; omega
    rw [heq]
    exact snoc_last hk _ _ _

private theorem snoc_statistics {A : GroupMat H n n} {k : ℕ} (hk : 0 < k)
    (w : LegalWord (baseGraph A) k) (e : Edge A) (seam : wordTarget hk w = e.source) :
    wordSource (by omega : 0 < k+1) (snocWord hk w e seam) = wordSource hk w ∧
    wordTarget (by omega : 0 < k+1) (snocWord hk w e seam) = e.target ∧
    totalLabel (snocWord hk w e seam) = totalLabel w * e.label := by
  refine ⟨?_,?_,?_⟩
  · simp [wordSource,snocWord,hk]
  · simp [wordTarget,snocWord]
  · rw [total_initial_last,initial_snoc,snoc_last]

private abbrev SuccessorFiber (A : GroupMat H n n) {k : ℕ} (hk : 0 < k)
    (i j : Fin n) (g : H) :=
  Σ t : Fin n, Σ h : H,
    WordFiber A hk i t h × Fin ((A t j).coeff (h⁻¹*g))

private abbrev PrefixLastFiber (A : GroupMat H n n) {k : ℕ} (hk : 0 < k)
    (i j : Fin n) (g : H) :=
  {p : LegalWord (baseGraph A) k × Edge A //
    wordSource hk p.1 = i ∧ wordTarget hk p.1 = p.2.source ∧
    p.2.target = j ∧ totalLabel p.1 * p.2.label = g}

/-- Separate the actual prefix and last edge before reindexing their finite fibers. -/
private def prefixLastFiberEquiv (A : GroupMat H n n) {k : ℕ} (hk : 0 < k)
    (i j : Fin n) (g : H) :
    WordFiber A (by omega : 0 < k+1) i j g ≃ PrefixLastFiber A hk i j g where
  toFun z := ⟨(initialWord z.val,z.val.edge ⟨k,by omega⟩),by
    refine ⟨?_,initial_last_seam hk z.val,?_,?_⟩
    · simpa [wordSource,initialWord,sliceWord] using z.property.1
    · simpa [wordTarget] using z.property.2.1
    · exact (total_initial_last z.val).symm.trans z.property.2.2⟩
  invFun p := ⟨snocWord hk p.val.1 p.val.2 p.property.2.1,by
    have hs := snoc_statistics hk p.val.1 p.val.2 p.property.2.1
    exact ⟨hs.1.trans p.property.1,hs.2.1.trans p.property.2.2.1,
      hs.2.2.trans p.property.2.2.2⟩⟩
  left_inv z := by
    apply Subtype.ext
    exact snoc_initial hk z.val
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact initial_snoc hk p.val.1 p.val.2 p.property.2.1
    · exact snoc_last hk p.val.1 p.val.2 p.property.2.1

/-- Reindex a genuine prefix/last-edge pair by its common vertex and ordered label. -/
private def prefixLastCoordinates (A : GroupMat H n n) {k : ℕ} (hk : 0 < k)
    (i j : Fin n) (g : H) :
    PrefixLastFiber A hk i j g ≃ SuccessorFiber A hk i j g where
  toFun p := by
    let w := p.val.1
    let e := p.val.2
    have ht : e.target = j := p.property.2.2.1
    have hl : e.label = (totalLabel w)⁻¹*g := by
      have h := p.property.2.2.2
      change totalLabel w * e.label = g at h
      calc
        e.label = (totalLabel w)⁻¹ * (totalLabel w * e.label) := by simp
        _ = (totalLabel w)⁻¹*g := congrArg (fun q => (totalLabel w)⁻¹*q) h
    exact ⟨e.source,totalLabel w,⟨w,p.property.1,p.property.2.1,rfl⟩,
      ⟨e.number.val,by simpa only [ht,hl] using e.number.isLt⟩⟩
  invFun p := by
    let e : Edge A := ⟨p.1,j,p.2.1⁻¹*g,p.2.2.2⟩
    refine ⟨(p.2.2.1.val,e),p.2.2.1.property.1,p.2.2.1.property.2.1,rfl,?_⟩
    change totalLabel p.2.2.1.val * (p.2.1⁻¹*g) = g
    rw [p.2.2.1.property.2.2]
    simp
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply edge_eq_of_coordinates
      · rfl
      · exact p.property.2.2.1.symm
      · have h := p.property.2.2.2
        change totalLabel p.val.1 * p.val.2.label = g at h
        calc
          (totalLabel p.val.1)⁻¹*g =
              (totalLabel p.val.1)⁻¹*(totalLabel p.val.1*p.val.2.label) :=
            congrArg (fun q => (totalLabel p.val.1)⁻¹*q) h.symm
          _ = p.val.2.label := by simp
      · rfl
  right_inv p := by
    rcases p with ⟨t,h,⟨w,hs,ht,hg⟩,number⟩
    cases hg
    rfl

private def snocFiberEquiv (A : GroupMat H n n) {k : ℕ} (hk : 0 < k)
    (i j : Fin n) (g : H) :
    WordFiber A (by omega : 0 < k+1) i j g ≃ SuccessorFiber A hk i j g :=
  (prefixLastFiberEquiv A hk i j g).trans (prefixLastCoordinates A hk i j g)

/-- Exact arbitrary-positive-length coefficient counting. -/
private theorem wordFiber_card_succ (A : GroupMat H n n) :
    ∀ m : ℕ, ∀ i j : Fin n, ∀ g : H,
      Fintype.card (WordFiber A (Nat.succ_pos m) i j g) =
        ((A^(m+1)) i j).coeff g := by
  intro m
  induction m with
  | zero =>
    intro i j g
    have hc := Fintype.card_congr
      ((oneWordFiberCoordinates A i j g).trans (coefficientFiber A i j g).symm)
    simpa using hc
  | succ m ih =>
    intro i j g
    calc
      Fintype.card (WordFiber A (Nat.succ_pos (m+1)) i j g) =
          Fintype.card (SuccessorFiber A (Nat.succ_pos m) i j g) :=
        Fintype.card_congr (snocFiberEquiv A (Nat.succ_pos m) i j g)
      _ = Fintype.card
          (D5.S3.ConceptDynamics.Coding.CountedGroupOverlap.Fiber (A^(m+1)) A i j g) := by
        simp only [SuccessorFiber,
          D5.S3.ConceptDynamics.Coding.CountedGroupOverlap.Fiber,
          Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
        simp_rw [ih]
      _ = ((A^(m+1)*A) i j).coeff g := by
        have hc := Fintype.card_congr
          (D5.S3.ConceptDynamics.Coding.CountedGroupOverlap.fiberEquiv (A^(m+1)) A i j g)
        simpa using hc.symm
      _ = ((A^(m+1+1)) i j).coeff g := by rw [pow_succ _ (m+1)]

private theorem wordFiber_card (A : GroupMat H n n) {k : ℕ} (hk : 0 < k)
    (i j : Fin n) (g : H) :
    Fintype.card (WordFiber A hk i j g) = ((A^k) i j).coeff g := by
  obtain ⟨m,hm⟩ : ∃ m : ℕ, k = m+1 := ⟨k-1,by omega⟩
  subst k
  exact wordFiber_card_succ A m i j g

theorem fiber_counts_of_equal_power (A B : GroupMat H n n)
    {k : ℕ} (hk : 0 < k) (hpower : A^k = B^k) :
    ∀ i j g, Fintype.card (WordFiber A hk i j g) =
      Fintype.card (WordFiber B hk i j g) := by
  intro i j g
  rw [wordFiber_card A hk,wordFiber_card B hk,hpower]

private def fiberDecomposition (A : GroupMat H n n) {k : ℕ} (hk : 0 < k) :
    LegalWord (baseGraph A) k ≃
      Σ i : Fin n, Σ j : Fin n, Σ g : H, WordFiber A hk i j g where
  toFun w := ⟨wordSource hk w,wordTarget hk w,totalLabel w,⟨w,rfl,rfl,rfl⟩⟩
  invFun w := w.2.2.2.val
  left_inv w := rfl
  right_inv w := by
    rcases w with ⟨i,j,g,w,hs,ht,hg⟩
    subst i
    subst j
    subst g
    rfl

/-- Finite fiber choices are made separately for this k; no f is assumed. -/
def baseEquivFromCounts (A B : GroupMat H n n) {k : ℕ} (hk : 0 < k)
    (hc : ∀ i j g, Fintype.card (WordFiber A hk i j g) =
      Fintype.card (WordFiber B hk i j g)) :
    LegalWord (baseGraph A) k ≃ LegalWord (baseGraph B) k := by
  classical
  let fibers := Equiv.sigmaCongrRight fun i : Fin n =>
    Equiv.sigmaCongrRight fun j : Fin n =>
      Equiv.sigmaCongrRight fun g : H => Fintype.equivOfCardEq (hc i j g)
  exact (fiberDecomposition A hk).trans (fibers.trans (fiberDecomposition B hk).symm)

private theorem baseEquivFromCounts_preserves (A B : GroupMat H n n)
    {k : ℕ} (hk : 0 < k)
    (hc : ∀ i j g, Fintype.card (WordFiber A hk i j g) =
      Fintype.card (WordFiber B hk i j g)) :
    ∀ w, wordSource hk (baseEquivFromCounts A B hk hc w) = wordSource hk w ∧
      wordTarget hk (baseEquivFromCounts A B hk hc w) = wordTarget hk w ∧
      totalLabel (baseEquivFromCounts A B hk hc w) = totalLabel w := by
  classical
  intro w
  exact (Fintype.equivOfCardEq
    (hc (wordSource hk w) (wordTarget hk w) (totalLabel w))
    ⟨w,rfl,rfl,rfl⟩).property

/-- The finite-word lift used by the original construction, at this exact k. -/
def constructedExpandedEquiv (A B : GroupMat H n n) {k : ℕ} (hk : 0 < k)
    (hc : ∀ i j g, Fintype.card (WordFiber A hk i j g) =
      Fintype.card (WordFiber B hk i j g)) :
    LegalWord (expandedGraph A) k ≃ LegalWord (expandedGraph B) k :=
  liftEquiv hk (baseEquivFromCounts A B hk hc)

private theorem constructedExpandedEquiv_endpoints (A B : GroupMat H n n)
    {k : ℕ} (hk : 0 < k)
    (hc : ∀ i j g, Fintype.card (WordFiber A hk i j g) =
      Fintype.card (WordFiber B hk i j g)) :
    PreservesBlockEndpoints hk (constructedExpandedEquiv A B hk hc) :=
  liftEquiv_endpoints hk _ (baseEquivFromCounts_preserves A B hk hc)

/-- The required actual h is this constructor itself, on the original alignment. -/
def constructedHomeomorph [TopologicalSpace H] [DiscreteTopology H]
    (A B : GroupMat H n n) {k : ℕ} (hk : 0 < k)
    (hc : ∀ i j g, Fintype.card (WordFiber A hk i j g) =
      Fintype.card (WordFiber B hk i j g)) :
    History (expandedGraph A) ≃ₜ History (expandedGraph B) :=
  blockHomeomorph hk (constructedExpandedEquiv A B hk hc)
    (constructedExpandedEquiv_endpoints A B hk hc)



section OperationalAttachment
variable [TopologicalSpace H] [DiscreteTopology H]
variable (A B : GroupMat H n n) {k : ℕ} (hk : 0 < k)
variable (hc : ∀ i j g, Fintype.card (WordFiber A hk i j g) =
  Fintype.card (WordFiber B hk i j g))

private theorem constructed_block_law :
    FixedBlockLaw (constructedExpandedEquiv A B hk hc) (constructedHomeomorph A B hk hc) :=
  blockMap_law hk (constructedExpandedEquiv A B hk hc)
    (constructedExpandedEquiv_endpoints A B hk hc)

/-- The complete original propagation formula on every aligned integer block. -/
private theorem constructed_at (x : History (expandedGraph A)) (j : ℤ) (r : Fin k) :
    (constructedHomeomorph A B hk hc x).val (j*(k:ℤ)+(r.val:ℤ)) =
      let w := forgetWord (historyWindow (expandedGraph A) x (j*(k:ℤ)) k)
      let out := baseEquivFromCounts A B hk hc w
      (out.edge r, (x.val (j*(k:ℤ))).2 * prefixLabel out r.val) := by
  have h := congrArg (fun w : LegalWord (expandedGraph B) k => w.edge r)
    (constructed_block_law A B hk hc x j)
  change (constructedHomeomorph A B hk hc x).val (j*(k:ℤ)+(r.val:ℤ)) =
    ((baseEquivFromCounts A B hk hc
        (forgetWord (historyWindow (expandedGraph A) x (j*(k:ℤ)) k))).edge r,
     ((historyWindow (expandedGraph A) x (j*(k:ℤ)) k).edge ⟨0,hk⟩).2 *
        prefixLabel (baseEquivFromCounts A B hk hc
          (forgetWord (historyWindow (expandedGraph A) x (j*(k:ℤ)) k))) r.val) at h
  simpa only [historyWindow,Int.natCast_zero,add_zero] using h

/-- Direct original algorithm: divide the integer index, replace the base word,
then propagate from the unchanged input block's initial group coordinate. -/
def original181Output (x : History (expandedGraph A)) (i : ℤ) : Edge B × H :=
  let j := (blockAddress hk i).1
  let r := (blockAddress hk i).2
  let w := forgetWord (historyWindow (expandedGraph A) x (j*(k:ℤ)) k)
  let out := baseEquivFromCounts A B hk hc w
  (out.edge r, (x.val (j*(k:ℤ))).2 * prefixLabel out r.val)

/-- Operational identity, not an arbitrary assumed h with a fitted block law. -/
private theorem original181Output_eq (x : History (expandedGraph A)) (i : ℤ) :
    original181Output A B hk hc x i = (constructedHomeomorph A B hk hc x).val i := by
  let j := (blockAddress hk i).1
  let r := (blockAddress hk i).2
  have hi : j*(k:ℤ)+(r.val:ℤ) = i := assemble_address hk i
  have h := constructed_at A B hk hc x j r
  rw [hi] at h
  exact h.symm

/-- The direct output is a legal history because it is the proved constructor's
output, coordinate for coordinate, with the same actual endpoint data. -/
def original181History (x : History (expandedGraph A)) : History (expandedGraph B) :=
  ⟨original181Output A B hk hc x,by
    intro i
    rw [original181Output_eq,original181Output_eq]
    exact (constructedHomeomorph A B hk hc x).property i⟩

private theorem original181History_eq (x : History (expandedGraph A)) :
    original181History A B hk hc x = constructedHomeomorph A B hk hc x := by
  apply Subtype.ext
  funext i
  exact original181Output_eq A B hk hc x i

def groupHistory (A : GroupMat H n n) (a : H)
    (x : History (expandedGraph A)) : History (expandedGraph A) where
  val i := ((x.val i).1,a*(x.val i).2)
  property i := by
    apply Prod.ext
    · change (x.val i).1.target = (x.val (i+1)).1.source
      exact congrArg Prod.fst (x.property i)
    · have hg := congrArg Prod.snd (x.property i)
      change (a*(x.val i).2)*(x.val i).1.label = a*(x.val (i+1)).2
      rw [mul_assoc]
      exact congrArg (fun b => a*b) hg

private theorem forget_group_window (a : H) (x : History (expandedGraph A)) (j : ℤ) :
    forgetWord (historyWindow (expandedGraph A) (groupHistory A a x) j k) =
      forgetWord (historyWindow (expandedGraph A) x j k) := by
  apply legalWord_ext
  rfl

private theorem constructed_group_law (a : H) (x : History (expandedGraph A)) :
    constructedHomeomorph A B hk hc (groupHistory A a x) =
      groupHistory B a (constructedHomeomorph A B hk hc x) := by
  apply Subtype.ext
  funext i
  let j := (blockAddress hk i).1
  let r := (blockAddress hk i).2
  have hi : j*(k:ℤ)+(r.val:ℤ) = i := assemble_address hk i
  rw [← hi,constructed_at]
  change _ = (((constructedHomeomorph A B hk hc x).val (j*(k:ℤ)+(r.val:ℤ))).1,
    a*((constructedHomeomorph A B hk hc x).val (j*(k:ℤ)+(r.val:ℤ))).2)
  rw [constructed_at,forget_group_window]
  simp only [groupHistory]
  exact Prod.ext rfl (mul_assoc _ _ _)

private theorem translate_block_window (x : History (expandedGraph A)) (j : ℤ) :
    historyWindow (expandedGraph A) (translate (expandedGraph A) (k:ℤ) x) (j*(k:ℤ)) k =
      historyWindow (expandedGraph A) x ((j+1)*(k:ℤ)) k := by
  apply legalWord_ext
  funext r
  change x.val (j*(k:ℤ)+(r.val:ℤ)+(k:ℤ)) =
    x.val ((j+1)*(k:ℤ)+(r.val:ℤ))
  congr 1
  ring

private theorem constructed_k_translate (x : History (expandedGraph A)) :
    constructedHomeomorph A B hk hc (translate (expandedGraph A) (k:ℤ) x) =
      translate (expandedGraph B) (k:ℤ) (constructedHomeomorph A B hk hc x) := by
  apply Subtype.ext
  funext i
  let j := (blockAddress hk i).1
  let r := (blockAddress hk i).2
  have hi : j*(k:ℤ)+(r.val:ℤ) = i := assemble_address hk i
  rw [← hi,constructed_at]
  have hj : j*(k:ℤ)+(k:ℤ) = (j+1)*(k:ℤ) := by ring
  have hcoord : j*(k:ℤ)+(r.val:ℤ)+(k:ℤ) = (j+1)*(k:ℤ)+(r.val:ℤ) := by ring
  change _ = (constructedHomeomorph A B hk hc x).val (j*(k:ℤ)+(r.val:ℤ)+(k:ℤ))
  rw [hcoord,constructed_at,translate_block_window]
  simp only [translate,hj]

private theorem shift_iterate_translate {V E : Type*} (G : DirectedMultigraph V E)
    (m : ℕ) (x : History G) : (shift G)^[m] x = translate G (m:ℤ) x := by
  induction m with
  | zero => exact (translate_zero x).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply',ih]
    apply Subtype.ext
    funext i
    change x.val (i+1+(m:ℤ)) = x.val (i+((m+1:ℕ):ℤ))
    apply congrArg x.val
    simp only [Int.natCast_add, Int.natCast_one]
    omega

private theorem constructed_k_shift (x : History (expandedGraph A)) :
    constructedHomeomorph A B hk hc ((shift (expandedGraph A))^[k] x) =
      (shift (expandedGraph B))^[k] (constructedHomeomorph A B hk hc x) := by
  rw [shift_iterate_translate,shift_iterate_translate]
  exact constructed_k_translate A B hk hc x

end OperationalAttachment

/-- The constructor takes the exact power equality. All finite fiber choices,
ordered lifts, endpoint data and the homeomorphism are produced here for this k. -/
def equalPowerHomeomorph [TopologicalSpace H] [DiscreteTopology H]
    (A B : GroupMat H n n) {k : ℕ} (hk : 0 < k) (hpower : A^k=B^k) :
    History (expandedGraph A) ≃ₜ History (expandedGraph B) :=
  constructedHomeomorph A B hk (fiber_counts_of_equal_power A B hk hpower)

/-- The exact equal-power construction satisfies the original ordered-coordinate
algorithm, group action and k-time law. Its one-step commutation forces equality.
The dimension-group inertness and exact positive cutoff bridge are separate obligations. -/
theorem equalPower_attachment [TopologicalSpace H] [DiscreteTopology H]
    (A B : GroupMat H n n) (hA : Essential (baseGraph A)) (hB : Essential (baseGraph B))
    {k : ℕ} (hk : 0 < k) (hpower : A^k = B^k) :
    (∀ x, original181History A B hk (fiber_counts_of_equal_power A B hk hpower) x =
      equalPowerHomeomorph A B hk hpower x) ∧
    (∀ a x, equalPowerHomeomorph A B hk hpower (groupHistory A a x) =
      groupHistory B a (equalPowerHomeomorph A B hk hpower x)) ∧
    (∀ x, equalPowerHomeomorph A B hk hpower ((shift (expandedGraph A))^[k] x) =
      (shift (expandedGraph B))^[k] (equalPowerHomeomorph A B hk hpower x)) ∧
    ((∀ x, equalPowerHomeomorph A B hk hpower (shift (expandedGraph A) x) =
      shift (expandedGraph B) (equalPowerHomeomorph A B hk hpower x)) → A = B) := by
  refine ⟨original181History_eq A B hk _, constructed_group_law A B hk _,
    constructed_k_shift A B hk _, ?_⟩
  intro hstep
  exact original18_3_freeExpansion A B hA hB hk
    (constructedExpandedEquiv A B hk (fiber_counts_of_equal_power A B hk hpower))
    (constructedExpandedEquiv_endpoints A B hk (fiber_counts_of_equal_power A B hk hpower)) hstep

end D5.S3.ConceptDynamics.Coding.FixedBlockRigidity
