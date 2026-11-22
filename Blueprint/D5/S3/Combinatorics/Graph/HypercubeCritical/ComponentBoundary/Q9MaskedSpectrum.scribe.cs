using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9MaskedSpectrumDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedSpectrum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral saturation of masked nine-cube components",
        H("The masked Huang eigenfunction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-positive-masked-component"),
                DeclarationHandle.Create(Module + ".exists_positive_masked_component"),
                H("A singular mask forces a strictly positive eigenfunction on a component"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In a balanced actual component, a singular defect on one parity for a nonempty "
                        + "mask I gives a connected component of the graph retaining only the axes in I. "
                        + "The unsigned adjacency on that component has a strictly positive eigenfunction "
                        + "at the square root of the cardinality of I.")),
                    Paragraph(Text(
                        "A nonzero kernel vector satisfies the parity Gram equation. Extend it by zero "
                        + "to the cube. Its Huang image already spends its full squared norm on the "
                        + "opposite parity in the component, by the weighted Clifford square identity. "
                        + "This yields a supported signed eigenvector. Switching to the unsigned rows "
                        + "and taking absolute values gives a row inequality. The same squared norm "
                        + "identity forces equality in each row. Positivity propagates from a nonzero "
                        + "vertex along masked edges."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedGram"))]));
}
