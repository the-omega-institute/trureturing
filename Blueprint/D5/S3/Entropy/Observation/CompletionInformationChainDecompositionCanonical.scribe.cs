using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class CompletionInformationChainDecompositionCanonicalDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Observation/CompletionInformationChainDecompositionCanonical."
            + "completion_information_chain_decomposition_canonical";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical source laws express the observation-word chain rule and stable completion "
            + "information decomposition without redeclaring induced distributions.",
        H("Canonical Completion Information Chain Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-completion-information-chain-decomposition"),
                DeclarationHandle.Create(Declaration),
                H("Completion information decomposes through the canonical laws"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y and O be finite, with a deterministic update, a readout, and a "
                            + "normalized nonnegative initial mass. The word law is conceptLaw "
                            + "applied to futureReadoutWord, and each increment is the canonical "
                            + "nextReadoutJointLaw.")),
                    Paragraph(Text(
                        "At a depth where consecutive word kernels agree, the named stable "
                            + "realized-word equivalence computes to completionProjection on every "
                            + "source state. This is the canonical bijection used by the entropy "
                            + "identity, not an equivalence chosen from that identity.")),
                    Paragraph(Text(
                        "The final conditional entropy uses completionLaw on the initial readout "
                            + "and completionProjection. Unfolding these three imported canonical "
                            + "laws reduces the statement to the frozen chain-decomposition "
                            + "machinery.")),
                    Paragraph(Text(
                        "Pinned Mathlib searches found no matching finite real-valued Shannon "
                            + "chain rule. Repository exact hits entropy_chain_rule, "
                            + "shannonEntropy_extend_injective, finiteWordRangeEquiv, and "
                            + "stableCompletionEquiv supply the imported proof."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Entropy(Formula value) =>
        Seq(F.Id("H"), Open, value, Close);

    private static Formula ConditionalEntropy(Formula value, Formula given) =>
        Seq(F.Id("H"), Open, value, Sp, Mid, Sp, given, Close);

    private static Formula DecompositionFormula()
    {
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula stableDepth = Sub(F.Id("m"), Star);
        Formula observation = F.Id("O");
        Formula word = F.Id("W");
        Formula wordAtM = Sub(word, m);
        Formula stableWord = Sub(word, stableDepth);
        Formula initialObservation = Sub(observation, D(0));
        Formula kthObservation = Sub(observation, k);
        Formula priorWord = Sub(word, Seq(k, Minus, D(1)));
        Formula completion = F.Id("CompletedState");
        Formula equivalence = F.Id("E");
        Formula state = F.Id("y");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, m, Sp, Geq, Sp, D(0), Comma, Sp,
            Entropy(wordAtM), Sp, Eq, Sp, Entropy(initialObservation), Sp, Plus, Sp,
            Sum, Underscore, Grp(Seq(k, Eq, D(1))), Caret, Grp(m), Sp,
            ConditionalEntropy(kthObservation, priorWord), Comma, RowBreak, Grp(),
            equivalence, Colon, Sp,
            Operatorname, Grp(F.Id("range")), Open, stableWord, Close,
            Sp, Equiv, Sp, completion, Comma, RowBreak, Grp(),
            Forall, Sp, state, Comma, Sp,
            equivalence, Open, stableWord, Open, state, Close, Close,
            Sp, Eq, Sp,
            Operatorname, Grp(F.Id("completionProjection")), Open, state, Close,
            Comma, RowBreak, Grp(),
            ConditionalEntropy(completion, initialObservation), Sp, Eq, Sp,
            Sum, Underscore, Grp(Seq(k, Eq, D(1))),
            Caret, Grp(stableDepth), Sp,
            ConditionalEntropy(kthObservation, priorWord), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
