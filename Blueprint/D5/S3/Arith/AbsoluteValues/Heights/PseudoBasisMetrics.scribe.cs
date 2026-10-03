using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class PseudoBasisMetricsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The projective Arakelov height descends from the tuple height under nonzero scalar multiplication.",
        H("Pseudo Basis Metrics"),
        Blocks(Describe.Lean(
            DescribeId.Create("pseudo-basis-metrics"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/PseudoBasisMetrics.projectiveArakelovMulHeight"),
            H("Pseudo Basis Metrics"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The projective Arakelov height descends from the tuple height under nonzero scalar multiplication."))),
            DescribeRole.Definition))));
}
