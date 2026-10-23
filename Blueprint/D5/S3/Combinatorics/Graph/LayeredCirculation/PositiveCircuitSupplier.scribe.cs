using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LayeredCirculation;

internal sealed class PositiveCircuitSupplierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact supplier exists_simpleSignedCircuit_decomposition is retained from Maths/Multitubes/Additive/CirculationDecomposition.lean at elazarg/multitubes commit 20d22aa7ca67f9843e5adf9edf173403a2f4033a. A normalized nonnegative real signed-incidence certificate has a finite convex decomposition into simple circuits, with exact coordinate reconstruction. This does not itself supply a greedy support-decreasing certificate; that certificate is proved in LayeredFlow. Copyright, the upstream license notice, full Apache-2.0 text and the retirement condition against this repository pinned mathlib are in the Lean sources.",
        H("PositiveCircuitSupplier"),
        Blocks(
            Paragraph(Text("Generic declarations use these source contexts: universe uV uE variable {V : Type uV} {E : Type uE} {G : EdgeGraph V E} universe uV uE variable {V : Type uV} {E : Type uE} universe uV uE variable {V : Type uV} {E : Type uE}")),
            Describe.Lean(
                DescribeId.Create("issimplecycle"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.IsSimpleCycle"),
                H("IsSimpleCycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def IsSimpleCycle {base : V} (cycle : G.Walk base base) : Prop := 0 < cycle.length ∧ ∀ (vertex : V) (before : G.Walk base vertex) (inner : G.Walk vertex vertex) (after : G.Walk vertex base), cycle.edges = before.edges ++ inner.edges ++ after.edges → 0 < inner.length → 0 < before.length + after.length → False"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cyclemeandominates"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.CycleMeanDominates"),
                H("CycleMeanDominates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def CycleMeanDominates (weight : E → ℝ) {firstBase secondBase : V} (first : G.Walk firstBase firstBase) (second : G.Walk secondBase secondBase) : Prop := second.length * MaxPlusPotential.walkWeight weight first ≥ first.length * MaxPlusPotential.walkWeight weight second"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signedgraph"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.signedGraph"),
                H("signedGraph"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def signedGraph (G : EdgeGraph V E) : EdgeGraph V (SignedEdge E) where source | (edge, false) => G.source edge | (edge, true) => G.target edge target | (edge, false) => G.target edge | (edge, true) => G.source edge"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("circuitcoefficient"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.circuitCoefficient"),
                H("circuitCoefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def circuitCoefficient [DecidableEq E] {G : EdgeGraph V E} {base : V} (cycle : G.Walk base base) (edge : E) : ℝ := cycle.edgeMultiplicity edge / cycle.length"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sum-edgemultiplicity-eq-length"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.sum_edgeMultiplicity_eq_length"),
                H("sum edgeMultiplicity eq length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem sum_edgeMultiplicity_eq_length [Fintype E] [DecidableEq E] {G : EdgeGraph V E} {start finish : V} (walk : G.Walk start finish) : ∑ edge, walk.edgeMultiplicity edge = walk.length"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edgelistcoefficient"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.edgeListCoefficient"),
                H("edgeListCoefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def edgeListCoefficient [DecidableEq E] (edges : List E) (edge : E) : ℝ := edges.count edge / edges.length"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("simplesignedcircuitcoefficients"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.simpleSignedCircuitCoefficients"),
                H("simpleSignedCircuitCoefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: def simpleSignedCircuitCoefficients [DecidableEq E] (G : EdgeGraph V E) : Set (SignedEdge E → ℝ) := {coefficient | ∃ (base : V) (cycle : (signedGraph G).Walk base base), IsSimpleCycle cycle ∧ circuitCoefficient cycle = coefficient}"))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("length-le-card"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.length_le_card"),
                H("length le card"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem IsSimpleCycle.length_le_card [Fintype V] {G : EdgeGraph V E} {base : V} {cycle : G.Walk base base} (hsimple : IsSimpleCycle cycle) : cycle.length ≤ Fintype.card V"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sum-edgemultiplicity-mul-eq-walkweight-general"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.sum_edgeMultiplicity_mul_eq_walkWeight_general"),
                H("sum edgeMultiplicity mul eq walkWeight general"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem sum_edgeMultiplicity_mul_eq_walkWeight_general [Fintype E] [DecidableEq E] {G : EdgeGraph V E} (weight : E → ℝ) {start finish : V} (walk : G.Walk start finish) : ∑ edge, (walk.edgeMultiplicity edge : ℝ) * weight edge = MaxPlusPotential.walkWeight weight walk"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-simplesignedcircuit-decomposition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LayeredCirculation/PositiveCircuitSupplier.exists_simpleSignedCircuit_decomposition"),
                H("exists simpleSignedCircuit decomposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact source telescope, in the module declared generic contexts: theorem exists_simpleSignedCircuit_decomposition [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdgeGraph V E) (coefficient : SignedEdge E → ℝ) (hcoefficient : FiniteInequality.IsNormalizedCertificate (signedDelta G) coefficient) : ∃ (ι : Type) (_ : Fintype ι) (convexWeight : ι → ℝ) (base : ι → V) (cycle : ∀ i, (signedGraph G).Walk (base i) (base i)), (∀ i, 0 ≤ convexWeight i) ∧ (∑ i, convexWeight i) = 1 ∧ (∀ i, IsSimpleCycle (cycle i)) ∧ ∀ edge, coefficient edge = ∑ i, convexWeight i * circuitCoefficient (cycle i) edge"))),
                DescribeRole.Theorem))));
}
