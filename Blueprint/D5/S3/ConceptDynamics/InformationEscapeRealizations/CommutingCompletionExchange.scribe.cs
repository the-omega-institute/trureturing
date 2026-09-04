using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class CommutingCompletionExchangeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The FourState countermodel realizes a discrete FLOW/FLOW/CUT kernel.",
        H("Commuting Completion Exchange Realization"),
        Blocks(
            Node("commutativity-necessary-realization",
                "commutativity_hypothesis_is_necessary_realization",
                "Countermodel realization equivalence",
                Call("LegacyPrimitiveRealization", F.Id("commutingCompletionArena"),
                    F.Id("CommutativityNecessaryStatement"),
                    F.Id("commutingCompletionRealization")),
                "Unfolding identifies both negated source clauses with the realization law."),
            Node("commutativity-necessary-partition-count",
                "commutativity_hypothesis_is_necessary_partition_count",
                "Four kernel classes", Seq(Call("card", F.Id("signatureClasses")), Sp, Eq, Sp, D(4)),
                "Exhaustive FourState evaluation gives four distinct signatures."),
            Node("commutativity-necessary-private-pair",
                "commutativity_hypothesis_is_necessary_private_pair",
                "Private pair separation",
                Call("Not", Call("agrees", F.Id("commutingCompletionRealization"),
                    F.Id("a"), F.Id("b"))),
                "The second flow sends a and b to different states."))));

    private static ScribeNode Node(string id, string declaration, string title,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(statement, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);
}
