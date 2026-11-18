using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class SlaterPrefixContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Slater prefix contraction with diagonal compression",
        H("Slater prefix contraction with diagonal compression"),
        Blocks(
            Entry("stackRows", "Stack the retained and discarded rows",
                "List the rows of the retained matrix first and then the rows of the discarded matrix.", DescribeRole.Definition),
            Entry("stackMinor", "Determinant rows at fixed occupation",
                "Stack the supplied retained rows above the increasing enumeration of the selected discarded rows. The retained row count plus the discarded occupation count is the column count.", DescribeRole.Definition),
            Entry("stackMinor_cast_selected", "Reindex a selected retained minor",
                "The equality of the occupied size and the row size lets either proof of the same column count be used to form the minor.", DescribeRole.Theorem),
            Entry("prefixAmplitudes", "Determinant amplitude matrix of a prefix",
                "Index rows and columns by the full retained and discarded occupation sets. A coefficient is the ordered occupied minor if the total occupation equals the particle count, and zero otherwise.", DescribeRole.Definition),
            Entry("diagonal_prefixMarginal", "Product weights for diagonal retained compression",
                "For rectangular complex matrices P and Y with the same column space index, assume P adjoint P plus Y adjoint Y is the identity. If P times P adjoint is diagonal with entries nu, the Gram matrix of the determinant amplitudes is diagonal over all retained occupation subsets. Its weight is the product of nu on occupied labels and one minus nu on unoccupied labels. The proof extracts the relevant weighted determinant coefficients using Cauchy–Binet.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("slater-prefix-contraction-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Fermionic/SlaterPrefixContraction." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
