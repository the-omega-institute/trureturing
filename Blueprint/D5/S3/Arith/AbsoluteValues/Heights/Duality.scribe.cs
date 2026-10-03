using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class DualityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Arakelov height of a subspace agrees with that of its dual annihilator.",
        H("Duality"),
        Blocks(Describe.Lean(
            DescribeId.Create("duality"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/Duality.arakelovMulHeight_comap_piEquiv_dualAnnihilator"),
            H("Duality"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The Arakelov height of a subspace agrees with that of its dual annihilator."))),
            DescribeRole.Theorem))));
}
