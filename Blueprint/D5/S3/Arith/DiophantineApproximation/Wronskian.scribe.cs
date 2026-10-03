using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class WronskianDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A linearly independent polynomial family has nonzero Hasse-Wronskian determinant.",
        H("Wronskian"),
        Blocks(Describe.Lean(
            DescribeId.Create("wronskian"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/Wronskian.hasseWronskianDet_ne_zero"),
            H("Wronskian"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A linearly independent polynomial family has nonzero Hasse-Wronskian determinant."))),
            DescribeRole.Theorem))));
}
