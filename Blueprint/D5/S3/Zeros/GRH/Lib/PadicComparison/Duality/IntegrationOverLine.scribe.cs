using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Duality;

internal sealed class IntegrationOverLineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integration Over Line", H("Integration Over Line"),
        Blocks(
            Paragraph(Text("Integration along P¹, natural operations, retract argument with the diagonal kernel on (P¹)^d.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Duality/IntegrationOverLine.isGood_topPoints_of_surjective"),
                H("isGood_topPoints_of_surjective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let I be a compatible family of ideals on points of (P¹)^m and U the locus where I is the unit ideal. If some Leray–Hirsch map from N to I.zerosCoeff is surjective at ℤ[(P¹)^m]/ℤ[U], then ComparedTheory.IsGood for D passes from N to ℤ[(P¹)^m]/ℤ[U].")))))));
}
