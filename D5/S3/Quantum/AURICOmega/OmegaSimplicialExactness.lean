/- GID: D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaSimplicialExactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite chain endpoint sums and pointwise simplicial cone exactness. -/

module
prelude
public import OmegaMath.Topology.SimplicialCoboundary

namespace D5.S3.Quantum.AURICOmega.OmegaSimplicialExactness

open Omega Omega.SimplicialCoboundary

variable {V : Sort u} {A : Type v}

/-- The sum of the edge differences is the endpoint difference. -/
public theorem sum_d0 (G : AddCommGroup A) (laws : G.Laws) (f : C0 V A)
    {first last : V} (chain : VertexChain V first last) :
    Eq (chain.sum G (d0 G f)) (d0 G f first last) :=
  Omega.SimplicialCoboundary.VertexChain.sum_d0 G laws f chain

/-- The sum of the edge differences along a closed chain is zero. -/
public theorem sum_d0_loop (G : AddCommGroup A) (laws : G.Laws) (f : C0 V A)
    {base : V} (chain : VertexChain V base base) :
    Eq (chain.sum G (d0 G f)) G.zero :=
  Omega.SimplicialCoboundary.VertexChain.sum_d0_loop G laws f chain

/-- The triangle coboundary of a vertex difference vanishes pointwise. -/
public theorem d1_d0 (G : AddCommGroup A) (laws : G.Laws) (f : C0 V A) (x y z : V) :
    Eq (d1 G (d0 G f) x y z) G.zero :=
  Omega.SimplicialCoboundary.d1_d0 G laws f x y z

/-- The tetrahedron coboundary of a triangle coboundary vanishes pointwise. -/
public theorem d2_d1 (G : AddCommGroup A) (laws : G.Laws) (e : C1 V A) (x y z w : V) :
    Eq (d2 G (d1 G e) x y z w) G.zero :=
  Omega.SimplicialCoboundary.d2_d1 G laws e x y z w

/-- Prepending a chosen vertex gives the degree-one cone identity. -/
public theorem d0_H1_add_H2_d1 (G : AddCommGroup A) (laws : G.Laws) (base : V)
    (e : C1 V A) (x y : V) :
    Eq (G.add (d0 G (H1 base e) x y) (H2 base (d1 G e) x y)) (e x y) :=
  Omega.SimplicialCoboundary.d0_H1_add_H2_d1 G laws base e x y

/-- Prepending a chosen vertex gives the degree-two cone identity. -/
public theorem d1_H2_add_H3_d2 (G : AddCommGroup A) (laws : G.Laws) (base : V)
    (F : C2 V A) (x y z : V) :
    Eq (G.add (d1 G (H2 base F) x y z) (H3 base (d2 G F) x y z)) (F x y z) :=
  Omega.SimplicialCoboundary.d1_H2_add_H3_d2 G laws base F x y z

/-- A closed degree-two cochain has the cone primitive at any chosen vertex. -/
public theorem d1_H2_of_d2_eq_zero (G : AddCommGroup A) (laws : G.Laws) (base : V) (F : C2 V A)
    (closed : ∀ x y z w, Eq (d2 G F x y z w) G.zero) (x y z : V) :
    Eq (d1 G (H2 base F) x y z) (F x y z) :=
  Omega.SimplicialCoboundary.d1_H2_of_d2_eq_zero G laws base F closed x y z

/-- With a chosen vertex, closedness and exactness in degree two are equivalent. -/
public theorem d2_eq_zero_iff (G : AddCommGroup A) (laws : G.Laws) (base : V) (F : C2 V A) :
    Iff (∀ x y z w, Eq (d2 G F x y z w) G.zero)
      (Exists fun e : C1 V A => ∀ x y z, Eq (d1 G e x y z) (F x y z)) :=
  Omega.SimplicialCoboundary.d2_eq_zero_iff G laws base F

end D5.S3.Quantum.AURICOmega.OmegaSimplicialExactness
