/- GID: D5/S3/Quantum/Routing/HannExactForest
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/HannExactForest
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-coordinate node lifts for actual signed loaded router records. -/

import D5.S3.Quantum.Routing.HannSignedCertificate
import D5.S3.Combinatorics.Graph.Jacobi.LeafPruningRanks

/-! The literal node equations, with independent leaf and address variables. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Routing.HannExactForest

open ReversibleQram (Address)
open HannRouterProfiles (Router)
open HannSpatialQram (Qutrit)
open HannSignedCertificate

/-- All binary words of length at most the height, in head-first coordinates. -/
abbrev Node : ℕ → Type
  | 0 => Unit
  | n + 1 => Option (Bool × Node n)

instance nodeFintype : (n : ℕ) → Fintype (Node n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
      letI := nodeFintype n
      exact inferInstanceAs (Fintype (Option (Bool × Node n)))

instance nodeDecidableEq (n : ℕ) : DecidableEq (Node n) := Classical.decEq _

/-- The empty word; at height zero it is also the unique leaf. -/
def root : (n : ℕ) → Node n
  | 0 => ()
  | _ + 1 => none

/-- Literal restriction of the node variables to a child. -/
def childValues (n : ℕ) (c : Node (n + 1) → ℂ) (b : Bool) : Node n → ℂ :=
  fun v => c (some (b, v))

/-- The prescribed clauses at one router. -/
def Local (t : ℝ) (z l r : ℂ) : Prop :=
  if t = 1 then z - l - r = 0
  else if t = -(1 / 2 : ℝ) then l + z = 0 ∧ r + z = 0
  else z = 0 ∧ l = 0 ∧ r = 0

/-- Every leaf and every router clause is imposed; no extra root equation. -/
def Equations : (n : ℕ) → (Router n → ℝ) → Coeff n → (Node n → ℂ) → Prop
  | 0, _, x, c => c () - x () = 0
  | n + 1, q, x, c =>
      Local (q none) (c none)
        (childValues n c false (root n)) (childValues n c true (root n)) ∧
      ∀ b, Equations n (restrict n q b) (childCoeff n x b) (childValues n c b)

/-- Projection forgets only nonroot node variables, retaining every address. -/
def Projected (n : ℕ) (q : Router n → ℝ) (x : Coeff n) (z : ℂ) : Prop :=
  ∃ c : Node n → ℂ, c (root n) = z ∧ Equations n q x c

private theorem local_synthesis_converse (n : ℕ) (q : Router (n + 1) → ℝ)
    (bus : Qutrit) (x : Coeff (n + 1)) (z l r : ℂ)
    (hl : synthesis n (restrict n q false) bus (childCoeff n x false) =
      l • vacuumRecord n (restrict n q false))
    (hr : synthesis n (restrict n q true) bus (childCoeff n x true) =
      r • vacuumRecord n (restrict n q true))
    (h : Local (q none) z l r) :
    synthesis (n + 1) q bus x = z • vacuumRecord (n + 1) q := by
  ext e
  rw [synthesis_split, hl, hr]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [vacuum_split]
  unfold Local at h
  split_ifs at h with hu hd
  · have he : z = l + r := by linear_combination h
    rw [hu, local_upper Qutrit.zero, local_upper Qutrit.one, he]
    ring
  · rcases h with ⟨hlz, hrz⟩
    have hel : l = -z := by linear_combination hlz
    have her : r = -z := by linear_combination hrz
    rw [hd, local_lower, hel, her]
    ring
  · rcases h with ⟨rfl, rfl, rfl⟩
    ring

/-- Exact all-height bidirectional node lift of the actual loaded-record relation. -/
private theorem relation_iff_projected (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1) (x : Coeff n) (z : ℂ) :
    synthesis n q bus x = z • vacuumRecord n q ↔ Projected n q x z := by
  induction n generalizing z with
  | zero =>
    have he : synthesis 0 q bus x = z • vacuumRecord 0 q ↔ x () = z := by
      constructor
      · intro h
        simpa [synthesis, record, vacuumRecord] using congrFun h (fun v => v.elim)
      · intro h
        ext e
        simpa [synthesis, record, vacuumRecord] using h
    rw [he]
    constructor
    · intro h
      exact ⟨fun _ => z, rfl, by simpa [Equations, h]⟩
    · rintro ⟨c, hc, h⟩
      change c () = z at hc
      change c () - x () = 0 at h
      linear_combination hc - h
  | succ n ih =>
    have hchild (b : Bool) := ih (restrict n q b) (fun v => hq (some (b, v)))
    constructor
    · intro hx
      have hloc : ∃ l r : ℂ,
          synthesis n (restrict n q false) bus (childCoeff n x false) =
            l • vacuumRecord n (restrict n q false) ∧
          synthesis n (restrict n q true) bus (childCoeff n x true) =
            r • vacuumRecord n (restrict n q true) ∧ Local (q none) z l r := by
        by_cases hu : q none = 1
        · obtain ⟨l, hl, hr⟩ := upper_relation n q bus (fun v => (hq v).1) hu x z hx
          exact ⟨l, z - l, hl, hr, by simp [Local, hu]⟩
        · obtain ⟨hl, hr, hz⟩ := below_upper_relation n q bus (fun v => (hq v).1)
            (lt_of_le_of_ne (hq none).2 hu) x z hx
          refine ⟨-z, -z, hl, hr, ?_⟩
          by_cases hd : q none = -(1 / 2 : ℝ)
          · simp only [Local, ite_eq_right hu, ite_eq_left hd]
            exact ⟨by ring, by ring⟩
          · simp only [Local, ite_eq_right hu, ite_eq_right hd]
            simp [hz hd]
      obtain ⟨l, r, hl, hr, hloc⟩ := hloc
      obtain ⟨cl, hcl, hel⟩ := (hchild false (childCoeff n x false) l).mp hl
      obtain ⟨cr, hcr, her⟩ := (hchild true (childCoeff n x true) r).mp hr
      let c : Node (n + 1) → ℂ
        | none => z
        | some (false, v) => cl v
        | some (true, v) => cr v
      refine ⟨c, rfl, ?_⟩
      change Local (q none) z (cl (root n)) (cr (root n)) ∧ _
      refine ⟨by simpa [hcl, hcr] using hloc, ?_⟩
      intro b
      cases b
      · exact hel
      · exact her
    · rintro ⟨c, hc, hloc, hsub⟩
      have hl := (hchild false (childCoeff n x false) (childValues n c false (root n))).mpr
        ⟨childValues n c false, rfl, hsub false⟩
      have hr := (hchild true (childCoeff n x true) (childValues n c true (root n))).mpr
        ⟨childValues n c true, rfl, hsub true⟩
      exact local_synthesis_converse n q bus x z _ _ hl hr (by change c none = z at hc; simpa only [hc] using hloc)

/-- Clause labels are retained even when their coefficient rows coincide. -/
def Clause (t : ℝ) := {i : Fin 3 //
  if t = 1 then i = 0 else if t = -(1 / 2 : ℝ) then i ≠ 2 else True}

instance (t : ℝ) : Fintype (Clause t) := by
  classical
  unfold Clause
  infer_instance

/-- Root clauses, followed by the separately identified rows of each child. -/
abbrev Row : (n : ℕ) → (Router n → ℝ) → Type
  | 0, _ => Unit
  | n + 1, q => Clause (q none) ⊕ (Σ b : Bool, Row n (restrict n q b))

instance rowFintype : (n : ℕ) → (q : Router n → ℝ) → Fintype (Row n q)
  | 0, _ => inferInstanceAs (Fintype Unit)
  | n + 1, q => by
      letI (b : Bool) := rowFintype n (restrict n q b)
      exact inferInstanceAs (Fintype (Clause (q none) ⊕ (Σ b : Bool, Row n (restrict n q b))))


/-- Distinct summands prevent identification of a leaf node and its address. -/
abbrev Variable (n : ℕ) := Address n ⊕ Node n

def rootCoefficient (t : ℝ) (i : Clause t) : ℝ :=
  if t = 1 then 1 else if t = -(1 / 2 : ℝ) then 1 else if i.val = 0 then 1 else 0

def branchCoefficient (t : ℝ) (i : Clause t) (b : Bool) : ℝ :=
  if t = 1 then -1 else if t = -(1 / 2 : ℝ) then
    if i.val = (if b then 1 else 0) then 1 else 0
  else if i.val = (if b then 2 else 1) then 1 else 0

/-- The exact real matrix: no row merging, column scaling, or extra equation. -/
def matrix : (n : ℕ) → (q : Router n → ℝ) → Matrix (Row n q) (Variable n) ℝ
  | 0, _, _, .inl _ => -1
  | 0, _, _, .inr _ => 1
  | n + 1, q, .inl i, .inl _ => 0
  | n + 1, q, .inl i, .inr none => rootCoefficient (q none) i
  | n + 1, q, .inl i, .inr (some (b, v)) =>
      if v = root n then branchCoefficient (q none) i b else 0
  | n + 1, q, .inr ⟨b, i⟩, .inl (d, a) =>
      if h : d = b then matrix n (restrict n q b) i (.inl a) else 0
  | n + 1, q, .inr ⟨b, i⟩, .inr none => 0
  | n + 1, q, .inr ⟨b, i⟩, .inr (some (d, v)) =>
      if h : d = b then matrix n (restrict n q b) i (.inr v) else 0

/-- Complexification changes the scalar field, not the matrix coefficients. -/
def complexMatrix (n : ℕ) (q : Router n → ℝ) : Matrix (Row n q) (Variable n) ℂ :=
  fun i v => (matrix n q i v : ℂ)

def coordinates (n : ℕ) (x : Coeff n) (c : Node n → ℂ) : Variable n → ℂ :=
  Sum.elim x c

private theorem local_rows_iff (t : ℝ) (z l r : ℂ) :
    (∀ i : Clause t, (rootCoefficient t i : ℂ) * z +
      (branchCoefficient t i false : ℂ) * l +
      (branchCoefficient t i true : ℂ) * r = 0) ↔ Local t z l r := by
  classical
  by_cases hu : t = 1
  · have hc : ∀ i : Clause t, i.val = 0 := fun i => by simpa [Clause, hu] using i.property
    have hi : (0 : Fin 3) ∈ {i : Fin 3 | if t = 1 then i = 0 else
        if t = -(1 / 2 : ℝ) then i ≠ 2 else True} := by simp [hu]
    constructor
    · intro h
      have hh := h ⟨0, hi⟩
      simpa [rootCoefficient, branchCoefficient, hu, Local, sub_eq_add_neg, add_assoc] using hh
    · intro h i
      simpa [rootCoefficient, branchCoefficient, hu, Local, sub_eq_add_neg, add_assoc] using h
  · by_cases hd : t = -(1 / 2 : ℝ)
    · have hc : ∀ i : Clause t, i.val ≠ 2 := fun i => by simpa only [ite_eq_right hu, ite_eq_left hd] using i.property
      constructor
      · intro h
        have h0 := h ⟨0, by simp only [ite_eq_right hu, ite_eq_left hd]; decide⟩
        have h1 := h ⟨1, by simp only [ite_eq_right hu, ite_eq_left hd]; decide⟩
        simp only [Local, ite_eq_right hu, ite_eq_left hd]
        constructor <;> norm_num [rootCoefficient, branchCoefficient, hu, hd, add_comm] at * <;> assumption
      · intro h i
        simp only [Local, ite_eq_right hu, ite_eq_left hd] at h
        have hi := hc i
        rcases i with ⟨i, hi'⟩
        fin_cases i <;> norm_num [rootCoefficient, branchCoefficient, hu, hd, add_comm] at * <;> tauto
    · constructor
      · intro h
        have h0 := h ⟨0, by simp only [ite_eq_right hu, ite_eq_right hd]⟩
        have h1 := h ⟨1, by simp only [ite_eq_right hu, ite_eq_right hd]⟩
        have h2 := h ⟨2, by simp only [ite_eq_right hu, ite_eq_right hd]⟩
        simp only [Local, ite_eq_right hu, ite_eq_right hd]
        simp only [rootCoefficient, branchCoefficient, ite_eq_right hu, ite_eq_right hd] at h0 h1 h2
        norm_num at h0 h1 h2
        exact ⟨h0, h1, h2⟩
      · intro h i
        simp only [Local, ite_eq_right hu, ite_eq_right hd] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        simp

private theorem node_sum_succ (n : ℕ) (f : Node (n + 1) → ℂ) :
    (∑ v, f v) = f none + (∑ v : Node n, f (some (false, v))) +
      (∑ v : Node n, f (some (true, v))) := by
  change (∑ v : Option (Bool × Node n), f v) = _
  rw [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

private theorem mulVec_root (n : ℕ) (q : Router (n + 1) → ℝ)
    (i : Clause (q none)) (x : Coeff (n + 1)) (c : Node (n + 1) → ℂ) :
    (complexMatrix (n + 1) q).mulVec (coordinates (n + 1) x c) (.inl i) =
      (rootCoefficient (q none) i : ℂ) * c none +
      (branchCoefficient (q none) i false : ℂ) * c (some (false, root n)) +
      (branchCoefficient (q none) i true : ℂ) * c (some (true, root n)) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  rw [node_sum_succ]
  simp [complexMatrix, coordinates, Sum.elim, matrix, apply_ite, ite_mul, add_assoc]

private theorem mulVec_child (n : ℕ) (q : Router (n + 1) → ℝ)
    (b : Bool) (i : Row n (restrict n q b))
    (x : Coeff (n + 1)) (c : Node (n + 1) → ℂ) :
    (complexMatrix (n + 1) q).mulVec (coordinates (n + 1) x c) (.inr ⟨b, i⟩) =
      (complexMatrix n (restrict n q b)).mulVec
        (coordinates n (childCoeff n x b) (childValues n c b)) i := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  rw [node_sum_succ]
  cases b <;>
    simp [complexMatrix, coordinates, Sum.elim, matrix, childCoeff, childValues,
      Fintype.sum_prod_type, Fintype.sum_bool]

theorem kernel_iff_equations (n : ℕ) (q : Router n → ℝ)
    (x : Coeff n) (c : Node n → ℂ) :
    (complexMatrix n q).mulVec (coordinates n x c) = 0 ↔ Equations n q x c := by
  induction n with
  | zero =>
      rw [funext_iff]
      change (∀ i : Unit, (∑ v : Address 0 ⊕ Unit,
        (matrix 0 q i v : ℂ) * coordinates 0 x c v) = 0) ↔ c () - x () = 0
      simp [Fintype.sum_sum_type, matrix, coordinates, Sum.elim, sub_eq_add_neg, add_comm]
  | succ n ih =>
      rw [funext_iff]
      simp only [Pi.zero_apply, Equations]
      constructor
      · intro h
        refine ⟨(local_rows_iff _ _ _ _).mp (fun i => ?_), ?_⟩
        · have hh := h (.inl i)
          rw [mulVec_root n q i x c] at hh
          exact hh
        · intro b
          apply (ih (restrict n q b) (childCoeff n x b) (childValues n c b)).mp
          ext i
          have hh := h (.inr ⟨b, i⟩)
          rw [mulVec_child n q b i x c] at hh
          exact hh
      · rintro ⟨h, hs⟩ i
        cases i with
        | inl i =>
            rw [mulVec_root n q i x c]
            exact (local_rows_iff _ _ _ _).mpr h i
        | inr i =>
            obtain ⟨b, i⟩ := i
            rw [mulVec_child n q b i x c]
            exact congrFun ((ih _ _ _).mpr (hs b)) i

/-- B1 for the specified real homogeneous matrix, complexified entrywise. -/
theorem relation_iff_matrix_kernel (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v ∧ q v ≤ 1) (x : Coeff n) (z : ℂ) :
    synthesis n q bus x = z • vacuumRecord n q ↔
      ∃ c : Node n → ℂ, c (root n) = z ∧
        (complexMatrix n q).mulVec (coordinates n x c) = 0 := by
  rw [relation_iff_projected n q bus hq]
  simp only [Projected, kernel_iff_equations]

/-- Height order used only to prove absence of cycles in the literal support. -/
private def nodeRank : (n : ℕ) → Node n → ℕ
  | 0, _ => 2
  | n + 1, none => 3 * (n + 1) + 2
  | n + 1, some (_, v) => nodeRank n v

private def rowRank : (n : ℕ) → (q : Router n → ℝ) → Row n q → ℕ
  | 0, _, _ => 1
  | n + 1, _, .inl _ => 3 * (n + 1) + 1
  | n + 1, q, .inr ⟨b, i⟩ => rowRank n (restrict n q b) i

private def variableRank (n : ℕ) : Variable n → ℕ
  | .inl _ => 0
  | .inr v => nodeRank n v

private theorem node_rank_le (n : ℕ) (v : Node n) : nodeRank n v ≤ 3 * n + 2 := by
  induction n with
  | zero => simp [nodeRank]
  | succ n ih =>
      cases v with
      | none => simp [nodeRank]
      | some v =>
          have := ih v.2
          change nodeRank n v.2 ≤ _
          omega

private theorem node_rank_root (n : ℕ) : nodeRank n (root n) = 3 * n + 2 := by
  cases n <;> rfl

private theorem row_rank_bounds (n : ℕ) (q : Router n → ℝ) (i : Row n q) :
    0 < rowRank n q i ∧ rowRank n q i ≤ 3 * n + 1 := by
  induction n with
  | zero => simp [rowRank]
  | succ n ih =>
      cases i with
      | inl i => simp [rowRank]
      | inr i =>
          obtain ⟨b, i⟩ := i
          have := ih (restrict n q b) i
          change 0 < rowRank n (restrict n q b) i ∧
            rowRank n (restrict n q b) i ≤ 3 * (n + 1) + 1
          omega

/-- The node attached above a row in the height order. -/
private def rowNode : (n : ℕ) → (q : Router n → ℝ) → Row n q → Node n
  | 0, _, _ => ()
  | _ + 1, _, .inl _ => none
  | n + 1, q, .inr ⟨b, i⟩ => some (b, rowNode n (restrict n q b) i)

private theorem row_later_node (n : ℕ) (q : Router n → ℝ) (i : Row n q) (v : Node n)
    (h : matrix n q i (.inr v) ≠ 0) (hr : rowRank n q i ≤ nodeRank n v) :
    v = rowNode n q i := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
      cases i with
      | inl i =>
          cases v with
          | none => rfl
          | some v =>
              have hv := node_rank_le n v.2
              change 3 * (n + 1) + 1 ≤ nodeRank n v.2 at hr
              omega
      | inr i =>
          obtain ⟨b, i⟩ := i
          cases v with
          | none => exact (h rfl).elim
          | some v =>
              obtain ⟨d, v⟩ := v
              by_cases hd : d = b
              · subst d
                have hh : matrix n (restrict n q b) i (.inr v) ≠ 0 := by
                  simpa only [matrix, dite_true] using h
                have he := ih (restrict n q b) i v hh hr
                exact congrArg (fun v => some (b, v)) he
              · simp [matrix, hd] at h

private theorem row_later_unique (n : ℕ) (q : Router n → ℝ) (i : Row n q)
    (a b : Variable n) (ha : matrix n q i a ≠ 0) (hb : matrix n q i b ≠ 0)
    (hra : rowRank n q i ≤ variableRank n a) (hrb : rowRank n q i ≤ variableRank n b) :
    a = b := by
  cases a with
  | inl a => have := (row_rank_bounds n q i).1; change _ ≤ 0 at hra; omega
  | inr a =>
      cases b with
      | inl b => have := (row_rank_bounds n q i).1; change _ ≤ 0 at hrb; omega
      | inr b =>
          exact congrArg Sum.inr ((row_later_node n q i a ha hra).trans
            (row_later_node n q i b hb hrb).symm)

private theorem branch_clause_unique (t : ℝ) (i j : Clause t) (b : Bool)
    (hi : branchCoefficient t i b ≠ 0) (hj : branchCoefficient t j b ≠ 0) : i = j := by
  apply Subtype.ext
  by_cases hu : t = 1
  · have hi0 : i.val = 0 := by simpa only [ite_eq_left hu] using i.property
    have hj0 : j.val = 0 := by simpa only [ite_eq_left hu] using j.property
    exact hi0.trans hj0.symm
  · by_cases hd : t = -(1 / 2 : ℝ)
    · simp only [branchCoefficient, ite_eq_right hu, ite_eq_left hd] at hi hj
      have hi' : i.val = (if b then 1 else 0) := by
        by_contra hn
        simp [hn] at hi
      have hj' : j.val = (if b then 1 else 0) := by
        by_contra hn
        simp [hn] at hj
      exact hi'.trans hj'.symm
    · simp only [branchCoefficient, ite_eq_right hu, ite_eq_right hd] at hi hj
      have hi' : i.val = (if b then 2 else 1) := by
        by_contra hn
        simp [hn] at hi
      have hj' : j.val = (if b then 2 else 1) := by
        by_contra hn
        simp [hn] at hj
      exact hi'.trans hj'.symm

private theorem variable_later_unique (n : ℕ) (q : Router n → ℝ) (v : Variable n)
    (i j : Row n q) (hi : matrix n q i v ≠ 0) (hj : matrix n q j v ≠ 0)
    (hri : variableRank n v ≤ rowRank n q i) (hrj : variableRank n v ≤ rowRank n q j) :
    i = j := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
      cases v with
      | inl a =>
          obtain ⟨d, a⟩ := a
          cases i with
          | inl i => exact (hi rfl).elim
          | inr i =>
              obtain ⟨b, i⟩ := i
              cases j with
              | inl j => exact (hj rfl).elim
              | inr j =>
                  obtain ⟨e, j⟩ := j
                  by_cases hd : d = b
                  · subst d
                    by_cases he : b = e
                    · subst e
                      have hi' : matrix n (restrict n q b) i (.inl a) ≠ 0 := by
                        simpa only [matrix, dite_true] using hi
                      have hj' : matrix n (restrict n q b) j (.inl a) ≠ 0 := by
                        simpa only [matrix, dite_true] using hj
                      have hh := ih (restrict n q b) (.inl a) i j hi' hj' hri hrj
                      exact congrArg (fun r : Row n (restrict n q b) =>
                        (Sum.inr ⟨b, r⟩ : Row (n + 1) q)) hh
                    · simp [matrix, he] at hj
                  · simp [matrix, hd] at hi
      | inr v =>
          cases v with
          | none =>
              have hh := (row_rank_bounds (n + 1) q i).2
              change 3 * (n + 1) + 2 ≤ rowRank (n + 1) q i at hri
              omega
          | some v =>
              obtain ⟨d, v⟩ := v
              cases i with
              | inl i =>
                  have hv : v = root n := by
                    by_contra hn
                    simp [matrix, hn] at hi
                  subst v
                  cases j with
                  | inl j =>
                      have hi' : branchCoefficient (q none) i d ≠ 0 := by simpa [matrix] using hi
                      have hj' : branchCoefficient (q none) j d ≠ 0 := by simpa [matrix] using hj
                      exact congrArg Sum.inl (branch_clause_unique _ i j d hi' hj')
                  | inr j =>
                      obtain ⟨e, j⟩ := j
                      have hh := (row_rank_bounds n (restrict n q e) j).2
                      change nodeRank n (root n) ≤ rowRank n (restrict n q e) j at hrj
                      rw [node_rank_root] at hrj
                      omega
              | inr i =>
                  obtain ⟨b, i⟩ := i
                  by_cases hd : d = b
                  · subst d
                    cases j with
                    | inl j =>
                        have hv : v = root n := by
                          by_contra hn
                          simp [matrix, hn] at hj
                        subst v
                        have hh := (row_rank_bounds n (restrict n q b) i).2
                        change nodeRank n (root n) ≤ rowRank n (restrict n q b) i at hri
                        rw [node_rank_root] at hri
                        omega
                    | inr j =>
                        obtain ⟨e, j⟩ := j
                        by_cases he : b = e
                        · subst e
                          have hi' : matrix n (restrict n q b) i (.inr v) ≠ 0 := by
                            simpa only [matrix, dite_true] using hi
                          have hj' : matrix n (restrict n q b) j (.inr v) ≠ 0 := by
                            simpa only [matrix, dite_true] using hj
                          have hh := ih (restrict n q b) (.inr v) i j hi' hj' hri hrj
                          exact congrArg (fun r : Row n (restrict n q b) =>
                            (Sum.inr ⟨b, r⟩ : Row (n + 1) q)) hh
                        · simp [matrix, he] at hj
                  · simp [matrix, hd] at hi

/-- Row vertices and variable vertices are distinct, and adjacency is exactly nonzero entry. -/
def support (n : ℕ) (q : Router n → ℝ) : SimpleGraph (Row n q ⊕ Variable n) where
  Adj u v := match u, v with
    | .inl i, .inr a => matrix n q i a ≠ 0
    | .inr a, .inl i => matrix n q i a ≠ 0
    | _, _ => False
  symm := ⟨by intro u v h; cases u <;> cases v <;> exact h⟩
  loopless := ⟨by intro u; cases u <;> simp⟩

/-- B2: the support of this very matrix has no undirected simple cycle. -/
theorem support_is_acyclic (n : ℕ) (q : Router n → ℝ) : (support n q).IsAcyclic := by
  apply D5.S3.Combinatorics.Graph.Jacobi.Pruning.acyclic_of_unique_later
    (support n q) (Sum.elim (rowRank n q) (variableRank n))
  intro v a b ha hb hra hrb
  cases v with
  | inl i =>
      cases a with
      | inl a => exact ha.elim
      | inr a =>
          cases b with
          | inl b => exact hb.elim
          | inr b => exact congrArg Sum.inr (row_later_unique n q i a b ha hb hra hrb)
  | inr v =>
      cases a with
      | inr a => exact ha.elim
      | inl i =>
          cases b with
          | inr b => exact hb.elim
          | inl j => exact congrArg Sum.inl (variable_later_unique n q v i j ha hb hra hrb)

end D5.S3.Quantum.Routing.HannExactForest
