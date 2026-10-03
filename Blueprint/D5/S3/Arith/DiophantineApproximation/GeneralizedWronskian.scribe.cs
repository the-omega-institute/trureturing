using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class GeneralizedWronskianDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Linearly independent polynomials admit a nonzero generalized Wronskian.",
        H("Generalized Wronskian"),
        Blocks(Describe.Lean(
            DescribeId.Create("generalized-wronskian"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/GeneralizedWronskian.exists_genWronskian_ne_zero"),
            H("Generalized Wronskian"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Linearly independent polynomials admit a nonzero generalized Wronskian."))),
            DescribeRole.Theorem))));
}
