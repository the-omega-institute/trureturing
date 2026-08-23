using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Communication;

internal sealed class PropositionLeakLowerBoundDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Communication/PropositionLeakLowerBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A transcript deciding a nonconstant Boolean proposition must reveal a distinction, "
            + "and the proposition itself realizes exact leakage.",
        H("Proposition Leak Lower Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("transcript-leaks-at-least-the-proposition"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "transcript_leaks_at_least_the_proposition"),
                H("A nonconstant proposition forces a transcript distinction"),
                StatementSource.FromAuthor(LowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose a deterministic decoder recovers a Boolean proposition from "
                            + "the transcript, and two secret states have different proposition "
                            + "values. If those states had the same transcript, the decoder would "
                            + "give them the same value, contradicting nonconstancy.")),
                    Paragraph(Text(
                        "Consequently the transcript must separate at least one pair already "
                            + "separated by the proposition. In particular, no constant transcript "
                            + "can decide a nonconstant proposition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("proposition-only-transcript-exists"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "proposition_only_transcript_exists"),
                H("The proposition itself is an exact transcript"),
                StatementSource.FromAuthor(ExactTranscriptFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every Boolean proposition, use its truth value as the transcript. Two "
                        + "states then have equal transcripts exactly when they have equal "
                        + "proposition values, and the identity decoder recovers the proposition. "
                        + "Thus the lower bound is attained without revealing any finer "
                        + "distinction."))),
                DescribeRole.Lemma))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula LowerBoundFormula()
    {
        Formula secretType = F.Id("Secret");
        Formula transcriptType = F.Id("Transcript");
        Formula boolean = F.Id("Bool");
        Formula transcript = F.Id("transcript");
        Formula proposition = F.Id("Q");
        Formula firstState = F.Id("s1");
        Formula secondState = F.Id("s2");
        Formula nontrivial = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("s1", secretType), Bound("s2", secretType)],
            NotEqual(
                Apply(proposition, firstState),
                Apply(proposition, secondState)));
        Formula transcriptDistinction = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("s1", secretType), Bound("s2", secretType)],
            NotEqual(
                Apply(transcript, firstState),
                Apply(transcript, secondState)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Secret", F.Id("Type")),
                Bound("Transcript", F.Id("Type")),
                Bound("transcript", Arrow(secretType, transcriptType)),
                Bound("Q", Arrow(secretType, boolean)),
            ],
            ImpliesFormula(
                And(Call("ProvesProposition", transcript, proposition), nontrivial),
                transcriptDistinction)));
    }

    private static Formula ExactTranscriptFormula()
    {
        Formula secretType = F.Id("Secret");
        Formula boolean = F.Id("Bool");
        Formula proposition = F.Id("Q");
        Formula transcript = F.Id("transcript");
        Formula transcriptType = Arrow(secretType, boolean);
        Formula exactTranscript = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("transcript"),
            transcriptType,
            And(
                Call("LeaksExactlyProposition", transcript, proposition),
                Call("ProvesProposition", transcript, proposition)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Secret", F.Id("Type")),
                Bound("Q", transcriptType),
            ],
            exactTranscript));
    }
}
