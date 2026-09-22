using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class FiniteColoringCompactnessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/FiniteColoringCompactness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-palette graph coloring is compact, and countably infinite palettes fail on an uncountable complete graph.",
        H("Finite Coloring Compactness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-palette-coloring-compactness"),
                DeclarationHandle.Create(Prefix + "finite_palette_coloring_compactness"),
                H("Finite-palette coloring is determined by finite induced subgraphs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every simple graph G and natural number k, G is colorable by Fin k "
                            + "if and only if every subgraph induced by a finite vertex set is "
                            + "colorable by Fin k.")),
                    Paragraph(Text(
                        "The reverse implication treats adjacent ordered pairs as constraints. "
                            + "For an arbitrary finite constraint family it takes the finite union "
                            + "of all endpoints, colors the induced graph there, extends that "
                            + "coloring to a total assignment, and verifies every selected edge. "
                            + "The frozen compact-local-realization theorem then supplies one "
                            + "global proper coloring.")),
                    Paragraph(Text(
                        "This is the classical finite-palette graph-coloring compactness theorem "
                            + "of de Bruijn and Erdos (1951). The pinned Mathlib compactness module "
                            + "cites the same source and supplies Rado selection; the present proof "
                            + "instead reuses the repository compactness engine so that the "
                            + "graph-specific endpoint-support bridge remains explicit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("infinite-palette-coloring-compactness-failure"),
                DeclarationHandle.Create(
                    Prefix + "infinite_palette_coloring_compactness_failure"),
                H("A countably infinite palette does not satisfy the same compactness principle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the complete graph on Set Nat, every finite induced subgraph has a "
                            + "proper Nat coloring: enumerate its finite vertex subtype and use "
                            + "the enumeration index as the color.")),
                    Paragraph(Text(
                        "Any global Nat coloring of this complete graph would be injective. "
                            + "Cardinal.cantor and Cardinal.mk_set state that Set Nat has strictly "
                            + "larger cardinality than Nat, so no such injection and hence no such "
                            + "global coloring exists. This identifies finiteness of the palette, "
                            + "not finiteness of each tested subgraph, as the sharp boundary."))),
                DescribeRole.Theorem))));
}
