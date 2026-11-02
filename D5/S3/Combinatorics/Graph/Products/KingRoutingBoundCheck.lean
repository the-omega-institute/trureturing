import D5.S3.Combinatorics.Graph.Products.LatticeRouting
set_option autoImplicit false
open D5.S3.Combinatorics.Graph.Products.LatticeRouting
example {V : Type} (vs : List V) (c : V → Point) (bucket : Point → ℕ)
    (v : V) (hv : v ∈ vs) :
    v ∈ bucketVertices bucket vs c (bucket (c v)) := by
  simp only [bucketVertices, List.mem_filter, decide_eq_true_eq]
  exact ⟨hv, True.intro⟩
