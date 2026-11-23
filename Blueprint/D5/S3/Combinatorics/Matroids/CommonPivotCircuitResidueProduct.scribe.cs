using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class CommonPivotCircuitResidueProductDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/CommonPivotCircuitResidueProduct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A product identity for common-pivot sparse-paving omissions.",
        H("Residue Product at a Common Pivot"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-pivot-residue-product"),
                DeclarationHandle.Create(Module + ".common_pivot_residue_product"),
                H("Residue exchange for adding an omission"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Consider rank r with 3 <= r < K and a previous finite family of omitted bases together with one new omission."
                    + " All omissions have size r, share a pivot, and meet pairwise in at most r minus two indices."
                    + " For the same surjective parallel expansion, the product of the uniform and joint weighted residue modules is integrally linearly equivalent to the product of the previous and single-omission weighted residue modules."))),
                DescribeRole.Theorem))));
}
