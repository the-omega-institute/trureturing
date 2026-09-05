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
        Blocks(
            Definition("four-state-code", "fourStateCode", "Four-state constructor code",
                "The code sends the four source constructors to the corresponding elements of Fin four."),
            Definition("four-state-of-code", "fourStateOfCode", "Four-state code inverse",
                "The inverse sends each element of Fin four back to its source-state constructor."),
            Definition("four-state-equivalence", "fourStateEquiv", "Four-state equivalence",
                "The exhaustive code and inverse form the private equivalence with Fin four."),
            Definition("four-state-finite", "instFintypeFourState", "Finite four-state carrier",
                "The finite instance is obtained through a private equivalence."),
            Definition("four-state-decidable-equality", "instDecidableEqFourState",
                "Four-state decidable equality",
                "The decidable-equality instance is obtained through a private equivalence."),
            Definition("completion-readout", "CompletionReadout", "Completion readout indices",
                "The readout index type has two FLOW roles and one CUT role."),
            Definition("completion-readout-finite", "instFintypeCompletionReadout",
                "Finite completion readouts",
                "The finite instance lists the three readout constructors exhaustively."),
            Definition("completion-signature", "completionSignature", "Completion signature",
                "The signature assigns state-valued outputs to the FLOW slots and a Boolean output to the CUT slot."),
            Definition("commutativity-necessary-statement", "CommutativityNecessaryStatement",
                "Frozen commutativity statement",
                "This alias is definitionally the type of the frozen theorem D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange.commutativity_hypothesis_is_necessary."),
            Definition("commuting-completion-arena", "commutingCompletionArena",
                "Completion countermodel arena",
                "Both completion orders are formed directly from realization FLOW and CUT slots."),
            Describe.Lean(
                DescribeId.Create("commuting-completion-arena-nondegenerate"),
                DeclarationHandle.Create(Prefix + "commutingCompletionArena_nondegenerate"),
                H("Commuting-completion arena is nondegenerate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Nondegenerate")), Open,
                    Operatorname, Grp(F.Id("toArena")), Open,
                    F.Id("commutingCompletionArena"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four-state source carrier contains a pair of distinct states."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);
}
