using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class CompletionInformationChainDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite observation words obey the Shannon chain rule, and stable completion information "
            + "is the sum of the later conditional observation entropies.",
        H("Observation-Word and Completion Information Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-information-chain-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Observation/CompletionInformationChainDecomposition."
                        + "completion_information_chain_decomposition"),
                H("Completion information decomposes along the observation chain"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y and O be finite, let tau : Y -> Y be a deterministic update, and "
                            + "let q : Y -> O be a readout. A normalized nonnegative initial mass "
                            + "function induces the law of each word W_m = (O_0, ..., O_m) by "
                            + "pushforward through the iterated readout map.")),
                    Paragraph(Text(
                        "For every m, splitting the final coordinate identifies the word law at "
                            + "depth m + 1 with the joint law of W_m and O_(m+1). The imported finite "
                            + "entropy chain rule gives one conditional term, and induction gives "
                            + "the displayed finite sum with H(O_0) as its base.")),
                    Paragraph(Text(
                        "At a depth where consecutive observation kernels agree, the named "
                            + "stableObservationCompletionEquiv composes the canonical kernel-range "
                            + "equivalence with the existing stable finite-to-complete quotient "
                            + "equivalence. Its public computation rule sends every realized word "
                            + "to the canonical completion class of the realizing state.")),
                    Paragraph(Text(
                        "The law of (O_0, completion) has the same joint entropy as the stable word "
                            + "law: both are injective relabelings of their common realized quotient. "
                            + "Applying the chain rule once more and canceling H(O_0) proves the "
                            + "stable conditional-entropy identity. No observation law, completion "
                            + "object, or stable depth is defined from the target equality.")),
                    Paragraph(Text(
                        "Pinned-library searches found no finite real-valued Shannon chain rule. "
                            + "Repository exact hits entropy_chain_rule, "
                            + "shannonEntropy_extend_injective, futureReadoutWord, "
                            + "finiteWordRangeEquiv, and stableCompletionEquiv are applied directly."))),
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
