using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class DisjointVariablesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomials in disjoint variable sets have multiplicative product height.",
        H("Disjoint Variables"),
        Blocks(Describe.Lean(
            DescribeId.Create("disjoint-variables"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/DisjointVariables.mulHeight_rename_mul_rename_of_disjoint"),
            H("Disjoint Variables"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Polynomials in disjoint variable sets have multiplicative product height."))),
            DescribeRole.Theorem))));
}
