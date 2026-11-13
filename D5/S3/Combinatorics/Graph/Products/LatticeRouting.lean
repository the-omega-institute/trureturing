/- GID: D5/S3/Combinatorics/Graph/Products/LatticeRouting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Products/LatticeRouting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Prod, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Maps]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.exact_square_routing; instance=D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.routing_check_success
   digest: Fresh occupancy insertion and four-neighbor lookup certify induced square-lattice routing and finite strong-product embeddings. -/
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Products.LatticeRouting

universe u v w

abbrev Point := ℤ × ℤ

def squareAdj (p q : Point) : Prop := |p.1 - q.1| + |p.2 - q.2| = 1

instance (p q : Point) : Decidable (squareAdj p q) := by
  unfold squareAdj
  infer_instance

theorem squareAdj_symm (p q : Point) : squareAdj p q ↔ squareAdj q p := by
  simp only [squareAdj, abs_sub_comm]

def neighbors (p : Point) : List Point :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

theorem squareAdj_iff_mem (p q : Point) : squareAdj p q ↔ q ∈ neighbors p := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp only [squareAdj, neighbors, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq]
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> omega

/-- A sparse lookup tree. Terminal keys are arbitrary finite bit strings. -/
inductive Occupancy (V : Type u) where
  | empty
  | node (value : Option V) (low high : Occupancy V)

namespace Occupancy
variable {V : Type u}

def value : Occupancy V → Option V
  | .empty => none
  | .node v _ _ => v

def branch (b : Bool) : Occupancy V → Occupancy V
  | .empty => .empty
  | .node _ l r => if b then r else l

def setValue (t : Occupancy V) (v : Option V) : Occupancy V :=
  .node v (t.branch false) (t.branch true)

def setBranch (t : Occupancy V) (b : Bool) (u : Occupancy V) : Occupancy V :=
  if b then .node t.value (t.branch false) u
  else .node t.value u (t.branch true)

def read (t : Occupancy V) : List Bool → Option V
  | [] => t.value
  | b :: bs => read (t.branch b) bs

/-- Reject every occupied key, even if the existing value happens to be equal. -/
def insert (t : Occupancy V) (key : List Bool) (v : V) : Option (Occupancy V) :=
  match key with
  | [] => match t.value with
    | none => some (t.setValue (some v))
    | some _ => none
  | b :: bs => (insert (t.branch b) bs v).map (t.setBranch b)

@[simp] theorem value_setValue (t : Occupancy V) (v : Option V) :
    (t.setValue v).value = v := rfl

@[simp] theorem branch_setValue (t : Occupancy V) (v : Option V) (b : Bool) :
    (t.setValue v).branch b = t.branch b := by cases b <;> rfl

@[simp] theorem value_setBranch (t : Occupancy V) (b : Bool) (u : Occupancy V) :
    (t.setBranch b u).value = t.value := by cases b <;> rfl

@[simp] theorem branch_setBranch_same (t : Occupancy V) (b : Bool) (u : Occupancy V) :
    (t.setBranch b u).branch b = u := by cases b <;> rfl

@[simp] theorem branch_setBranch_other (t : Occupancy V) (b : Bool) (u : Occupancy V) :
    (t.setBranch b u).branch (!b) = t.branch (!b) := by cases b <;> rfl

/-- Successful fresh insertion records the new value and preserves every old lookup. -/
theorem insert_spec (key : List Bool) (t t' : Occupancy V) (v : V)
    (h : t.insert key v = some t') :
    t'.read key = some v ∧
      ∀ q w, t.read q = some w → t'.read q = some w := by
  induction key generalizing t t' with
  | nil =>
    cases hv : t.value with
    | some w => simp [insert, hv] at h
    | none =>
      simp only [insert, hv, Option.some.injEq] at h
      subst t'
      constructor
      · rfl
      · intro q w hq
        cases q with
        | nil => simp [read, hv] at hq
        | cons b bs => simpa only [read, branch_setValue] using hq
  | cons b bs ih =>
    cases hu : (t.branch b).insert bs v with
    | none => simp [insert, hu] at h
    | some u =>
      simp only [insert, hu, Option.map_some, Option.some.injEq] at h
      subst t'
      obtain ⟨hn, hp⟩ := ih (t.branch b) u hu
      constructor
      · simpa only [read, branch_setBranch_same] using hn
      · intro q w hq
        cases q with
        | nil => simpa only [read, value_setBranch] using hq
        | cons c cs =>
          by_cases hc : c = b
          · subst c
            simpa only [read, branch_setBranch_same] using hp cs w hq
          · have hc' : c = !b := by cases b <;> cases c <;> simp_all
            subst c
            simpa only [read, branch_setBranch_other] using hq

def fill (key : V → List Bool) : List V → Occupancy V → Option (Occupancy V)
  | [], t => some t
  | a :: as, t => (t.insert (key a) a).bind (fill key as)

theorem fill_spec (key : V → List Bool) (xs : List V) (t t' : Occupancy V)
    (h : fill key xs t = some t') :
    (∀ q w, t.read q = some w → t'.read q = some w) ∧
      ∀ a ∈ xs, t'.read (key a) = some a := by
  induction xs generalizing t with
  | nil =>
    simp only [fill, Option.some.injEq] at h
    subst t
    exact ⟨fun _ _ hq => hq, by simp⟩
  | cons a as ih =>
    cases hu : t.insert (key a) a with
    | none => simp [fill, hu] at h
    | some u =>
      simp only [fill, hu, Option.bind_some] at h
      obtain ⟨hnew, hkeep⟩ := insert_spec (key a) t u a hu
      obtain ⟨hkeep', hall⟩ := ih u h
      refine ⟨fun q w hq => hkeep' q w (hkeep q w hq), ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · subst b
        exact hkeep' (key a) a hnew
      · exact hall b hb

end Occupancy

/-- Fixed depth, hence bounded lookup cost. Injectivity of this coding is NOT an
assumption: a successful `fill` forces unique keys on the enumerated vertices.
Coordinate equality always gives key equality. Local lookup additionally checks
the retrieved coordinate, so a hash collision at an unoccupied query cannot
silently create or erase an actual adjacency. -/
def bits : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, k => (k % 2 == 1) :: bits n (k / 2)

def pointKey (p : Point) : List Bool :=
  bits 27 ((p.1 + 4096).toNat + 16384 * (p.2 + 4096).toNat)

section Checker
variable {V : Type u} {B : Type v} [DecidableEq B]
  (bucket : Point → B) (bs : List B) (vs : List V) (es : List (V × V)) (c : V → Point)

def bucketVertices (b : B) : List V := vs.filter fun v => decide (bucket (c v) = b)

def bucketEdges (b : B) : List (V × V) :=
  es.filter fun e => decide (bucket (c e.1) = b)

def bucketFill (b : B) : Option (Occupancy V) :=
  Occupancy.fill (fun v => pointKey (c v)) (bucketVertices bucket vs c b) .empty

def bucketTree (b : B) : Occupancy V := (bucketFill bucket vs c b).getD .empty

/-- Select a tree using a key from the supplied list. The returned tree therefore
uses the list's key, independently of the expression computing the query key. -/
def selectTree (trees : B → Occupancy V) (b : B) : List B → Occupancy V
  | [] => .empty
  | a :: as => if b = a then trees a else selectTree trees b as

theorem selectTree_eq (trees : B → Occupancy V) (b : B) (hb : b ∈ bs) :
    selectTree trees b bs = trees b := by
  induction bs with
  | nil => simp at hb
  | cons a as ih =>
    by_cases h : b = a
    · subst b; simp only [selectTree, ↓reduceIte]
    · have hm : b ∈ as := (List.mem_cons.mp hb).resolve_left h
      simpa only [selectTree, h, ↓reduceIte] using ih hm

def routingLookup (trees : B → Occupancy V) (q : Point) : Option V :=
  (selectTree trees (bucket q) bs).read (pointKey q)

def edgeCheck : Bool := es.all fun e => decide (squareAdj (c e.1) (c e.2))

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def localCheck (trees : B → Occupancy V) (xs : List V) : Bool :=
  xs.all fun v => (neighbors (c v)).all fun q =>
    match routingLookup bucket bs trees q with
    | none => true
    | some w => decide (c w ≠ q ∨ G.Adj v w)

/-- Each bucket checks every outgoing listed edge and all four spatial queries
of each vertex. Queries use their own coordinate bucket, including queries
across boundaries. The soundness theorem separately requires the exact fill
equations for the supplied trees. -/
def bucketCheck (trees : B → Occupancy V) (b : B) : Bool :=
  edgeCheck (bucketEdges bucket es c b) c &&
    localCheck bucket bs c G trees (bucketVertices bucket vs c b)

def routingCheck (trees : B → Occupancy V) : Bool :=
  bs.all (bucketCheck bucket bs vs es c G trees)

/-- The coding is injective, complete and exact for the original graph. Each
supplied tree must equal the actual successful fresh fill of its bucket. -/
theorem routingCheck_sound {W : Type w} (trees : B → Occupancy V)
    (H : SimpleGraph W) (f : W → V)
    (hb : ∀ q, bucket q ∈ bs)
    (hfilled : ∀ b ∈ bs, bucketFill bucket vs c b = some (trees b))
    (hf : Function.Injective f)
    (hvs : ∀ w, f w ∈ vs)
    (hes : ∀ w z, H.Adj w z ↔ (f w, f z) ∈ es ∨ (f z, f w) ∈ es)
    (hgraph : ∀ w z, G.Adj (f w) (f z) ↔ H.Adj w z)
    (h : routingCheck bucket bs vs es c G trees = true) :
    Function.Injective (fun w => c (f w)) ∧
      ∀ w z, H.Adj w z ↔ squareAdj (c (f w)) (c (f z)) := by
  have parts (b : B) (hmem : b ∈ bs) :
      edgeCheck (bucketEdges bucket es c b) c = true ∧
      localCheck bucket bs c G trees (bucketVertices bucket vs c b) = true := by
    simpa only [bucketCheck, Bool.and_eq_true] using
      (List.all_eq_true.mp h b hmem)
  have hread (w : W) : routingLookup bucket bs trees (c (f w)) = some (f w) := by
    unfold routingLookup
    rw [selectTree_eq bs trees _ (hb _)]
    exact (Occupancy.fill_spec (fun v => pointKey (c v))
      (bucketVertices bucket vs c (bucket (c (f w)))) .empty
      (trees (bucket (c (f w)))) (hfilled _ (hb _))).2
      (f w) (by simp [bucketVertices, hvs w])
  have hedge (a b : V) (he : (a, b) ∈ es) : squareAdj (c a) (c b) := by
    have he' : (a, b) ∈ bucketEdges bucket es c (bucket (c a)) := by
      simp [bucketEdges, he]
    exact of_decide_eq_true
      (List.all_eq_true.mp (parts _ (hb (c a))).1 (a, b) he')
  constructor
  · intro w z heq
    change c (f w) = c (f z) at heq
    have hw := hread w
    rw [heq, hread z] at hw
    exact hf (Option.some.inj hw.symm)
  · intro w z
    constructor
    · intro hwz
      rcases (hes w z).mp hwz with he | he
      · exact hedge _ _ he
      · exact (squareAdj_symm _ _).mpr (hedge _ _ he)
    · intro hsq
      have hq : c (f z) ∈ neighbors (c (f w)) := (squareAdj_iff_mem _ _).mp hsq
      have hw := List.all_eq_true.mp (parts _ (hb (c (f w)))).2
        (f w) (by simp [bucketVertices, hvs w])
      have hz := List.all_eq_true.mp hw (c (f z)) hq
      rw [hread z] at hz
      have hresult : c (f z) ≠ c (f z) ∨ G.Adj (f w) (f z) := of_decide_eq_true hz
      exact (hgraph w z).mp (hresult.resolve_left (fun hne => hne rfl))

end Checker

/-- Exact integral rotation identity, including both signs of both coordinates. -/
theorem rotation_identity (a b : ℤ) : max |a + b| |a - b| = |a| + |b| := by
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> omega

def rotate (p : Point) : Point := (p.1 + p.2 + 25, p.1 - p.2 + 1705)

theorem rotate_injective : Function.Injective rotate := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [rotate] at hx hy
  exact Prod.ext (by omega) (by omega)

def kingAdj (p q : Point) : Prop := max |p.1 - q.1| |p.2 - q.2| = 1

theorem rotation_adjacency (p q : Point) :
    kingAdj (rotate p) (rotate q) ↔ squareAdj p q := by
  have hid := rotation_identity (p.1 - q.1) (p.2 - q.2)
  have hx : (rotate p).1 - (rotate q).1 = (p.1 - q.1) + (p.2 - q.2) := by
    dsimp [rotate]; omega
  have hy : (rotate p).2 - (rotate q).2 = (p.1 - q.1) - (p.2 - q.2) := by
    dsimp [rotate]; omega
  simp only [kingAdj, squareAdj, hx, hy, hid]

/-- Strong product: the union of categorical and box-product edges.
Mathlib's pinned `Prod` supplies only the box product. -/
def strongProduct {V : Type u} {W : Type v} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V × W) where
  Adj x y := (G.boxProd H).Adj x y ∨ (G.Adj x.1 y.1 ∧ H.Adj x.2 y.2)
  symm.symm x y h := by
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl x h := by
    rcases h with h | h
    · exact (G.boxProd H).loopless.irrefl _ h
    · exact G.loopless.irrefl _ h.1

instance {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (strongProduct G H).Adj := by
  intro x y
  change Decidable (((G.Adj x.1 y.1 ∧ x.2 = y.2) ∨
    (H.Adj x.2 y.2 ∧ x.1 = y.1)) ∨ (G.Adj x.1 y.1 ∧ H.Adj x.2 y.2))
  infer_instance

def finPoint {n m : ℕ} (p : Point)
    (hp : 0 ≤ p.1 ∧ p.1 < n ∧ 0 ≤ p.2 ∧ p.2 < m) : Fin n × Fin m :=
  (⟨p.1.toNat, by omega⟩, ⟨p.2.toNat, by omega⟩)

@[simp] theorem finPoint_cast {n m : ℕ} (p : Point)
    (hp : 0 ≤ p.1 ∧ p.1 < n ∧ 0 ≤ p.2 ∧ p.2 < m) :
    (((finPoint p hp).1.val : ℤ), ((finPoint p hp).2.val : ℤ)) = p := by
  apply Prod.ext <;> simp only [finPoint] <;> omega

theorem strong_paths_iff {n m : ℕ} (p q : Fin n × Fin m) :
    (strongProduct (SimpleGraph.pathGraph n) (SimpleGraph.pathGraph m)).Adj p q ↔
      kingAdj ((p.1.val : ℤ), (p.2.val : ℤ)) ((q.1.val : ℤ), (q.2.val : ℤ)) := by
  simp only [strongProduct, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, Fin.ext_iff, kingAdj]
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> omega

/-- Explicit conversion from the paper's `{1,...,n}` labels to `Fin n`.
The supplied rotation has extrema 1 and n, so this conversion is essential. -/
def zeroBased (p : Point) : Point := (p.1 - 1, p.2 - 1)

theorem zeroBased_injective : Function.Injective zeroBased := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [zeroBased] at hx hy
  exact Prod.ext (by omega) (by omega)

theorem kingAdj_zeroBased (p q : Point) :
    kingAdj (zeroBased p) (zeroBased q) ↔ kingAdj p q := by
  have hx : (zeroBased p).1 - (zeroBased q).1 = p.1 - q.1 := by dsimp [zeroBased]; omega
  have hy : (zeroBased p).2 - (zeroBased q).2 = p.2 - q.2 := by dsimp [zeroBased]; omega
  simp only [kingAdj, hx, hy]

def oneBasedRectangleEmbedding {V : Type u} (G : SimpleGraph V) (c : V → Point)
    (hinj : Function.Injective c)
    (hadj : ∀ v w, G.Adj v w ↔ squareAdj (c v) (c w))
    {n m : ℕ}
    (hb : ∀ v, 1 ≤ (rotate (c v)).1 ∧ (rotate (c v)).1 ≤ n ∧
      1 ≤ (rotate (c v)).2 ∧ (rotate (c v)).2 ≤ m) :
    G ↪g strongProduct (SimpleGraph.pathGraph n) (SimpleGraph.pathGraph m) := by
  have bounds (v : V) :
      0 ≤ (zeroBased (rotate (c v))).1 ∧ (zeroBased (rotate (c v))).1 < n ∧
      0 ≤ (zeroBased (rotate (c v))).2 ∧ (zeroBased (rotate (c v))).2 < m := by
    have h := hb v
    dsimp [zeroBased]
    omega
  let f (v : V) : Fin n × Fin m := finPoint (zeroBased (rotate (c v))) (bounds v)
  have hf (v : V) : (((f v).1.val : ℤ), ((f v).2.val : ℤ)) =
      zeroBased (rotate (c v)) := finPoint_cast _ _
  refine { toFun := f, inj' := ?_, map_rel_iff' := ?_ }
  · intro v w h
    apply hinj
    apply rotate_injective
    apply zeroBased_injective
    have h' := congrArg (fun x : Fin n × Fin m => ((x.1.val : ℤ), (x.2.val : ℤ))) h
    exact (hf v).symm.trans (h'.trans (hf w))
  · intro v w
    change (strongProduct (SimpleGraph.pathGraph n) (SimpleGraph.pathGraph m)).Adj
      (f v) (f w) ↔ G.Adj v w
    rw [strong_paths_iff, hf, hf, kingAdj_zeroBased, rotation_adjacency]
    exact (hadj v w).symm

end D5.S3.Combinatorics.Graph.Products.LatticeRouting
