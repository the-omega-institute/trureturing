using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SparseMaskCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite sparse mask certificate",
        H("Finite sparse mask certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mask-support"),
                DeclarationHandle.Create(Module + ".support"),
                H("Bit-vector characteristic support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer mask records membership of the 512 vertices in the cube."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mask-check"),
                DeclarationHandle.Create(Module + ".sparseMaskCheck"),
                H("Finite row and column contact checks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The row test counts masked directions reaching paired fibres at an occupied projected row. The column test counts occupied projected neighbors of each paired fibre."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mask-exclusion"),
                DeclarationHandle.Create(Module + ".not_universal_of_sparseMaskCheck"),
                H("Certified exclusion of universal weighted sharpness"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The bit-vector coordinate moves transport the two finite inequalities to the sparse Gram criterion for either retained parity and any coherent switching."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram"))]));
}
