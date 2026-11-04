using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta;

internal sealed class QuadraticLValueSquareDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two genuine primitive functional equations for a self-dual nonprincipal character eliminate the root-number sign. Nonvanishing at one permits the cancellation. For odd characters the Gamma factors yield L(0)^2=N*(L(1)/pi)^2.", H("QuadraticLValueSquare"), Blocks(
            Paragraph(Text("Two genuine primitive functional equations for a self-dual nonprincipal character eliminate the root-number sign. Nonvanishing at one permits the cancellation. For odd characters the Gamma factors yield L(0)^2=N*(L(1)/pi)^2.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Describe.Lean(DescribeId.Create("quadraticlvaluesquare-completed-zero-sq"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticLValueSquare.completed_zero_sq"), H("completed_zero_sq"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Two applications of the functional equation eliminate the root number without choosing its sign. This is an equality for the actual completed L-functions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticlvaluesquare-zero-sq"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticLValueSquare.zero_sq"), H("zero_sq"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For odd characters the two Gamma factors are 1 and the reciprocal of pi. No root-number evaluation is used in this uncompleted L-value identity."))), DescribeRole.Theorem))));
}
