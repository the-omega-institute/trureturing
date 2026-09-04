using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeArenas;

internal sealed class CommutingCompletionExchangeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeArenas/CommutingCompletionExchange.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completion countermodel law uses two typed flows and one cut.",
        H("Commuting Completion Exchange Arena"),
        Blocks(Describe.Lean(
            DescribeId.Create("commuting-completion-arena"),
            DeclarationHandle.Create(Prefix + "commutingCompletionArena"),
            H("Completion countermodel arena"),
            StatementSource.FromAuthor(Disp(Seq(F.Id("commutingCompletionArena"),
                Colon, Sp, F.Id("PrimitiveLawArena"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Both completion orders are formed directly from realization FLOW and CUT slots."))),
            DescribeRole.Definition))));
}
