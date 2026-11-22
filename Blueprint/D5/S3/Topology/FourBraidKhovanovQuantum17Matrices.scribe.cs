using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FourBraidKhovanovQuantum17MatricesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse integral matrices at quantum degree 17",
        H("Sparse integral matrices at quantum degree 17"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-braid-quantum-17-matrix-data"),
                DeclarationHandle.Create("D5/S3/Topology/FourBraidKhovanovQuantum17Matrices.d17"),
                H("Differential columns by cohomological degree"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sparse columns record the candidate coefficients of each integral "
                    + "differential at quantum degree 17. The proof of the row calculation "
                    + "verifies these coefficients against the signed merge and split rules."))),
                DescribeRole.Definition))));
}
