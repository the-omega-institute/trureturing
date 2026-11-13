using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class AdaptiveMarkerFiniteLabelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula seedType = F.Id("U");
        Formula policy = F.Id("p");
        Formula seed = F.Id("u");
        Formula word = F.Id("w");
        Formula labels = F.Id("z");
        Formula side = F.Id("s");
        Formula index = F.Id("i");
        Formula depth = F.Id("k");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula length = Call("length", word);
        Formula source = Call("completion", labels);
        Formula total = Call("sideTotal", word, side);
        Formula prefixState = Call("State",
            Call("reverse", Call("actions", word, depth)),
            Call("reverse", Call("replies", word, depth)),
            Call("decide", Seq(depth, Eq, length)));
        Formula finalState = Call("State",
            Call("reverse", Call("map", F.Id("fst"), word)),
            Call("reverse", Call("map", F.Id("snd"), word)), F.Id("true"));
        Formula finiteLabels = All(side, F.Id("Bool"),
            All(index, Call("Fin", Seq(total, Plus, D(1))),
                Seq(Call("endpoint", source, side, index), Eq,
                    Call("bit", labels, side, index))));
        Formula prefixes = All(depth, naturals,
            Seq(Open, depth, Leq, Sp, length, Close, Rightarrow,
                Call("actualRun", policy, seed, source, depth), Eq, prefixState));
        Formula conclusion = Seq(
            Begin, Grp(F.Id("gathered")),
            Call("noAdjacentOnes", source), Land, RowBreak, Grp(),
            Open, finiteLabels, Close, Land, RowBreak, Grp(),
            Open, prefixes, Close, Land, RowBreak, Grp(),
            Open, Call("actualRun", policy, seed, source, length), Eq, finalState, Close,
            Land, RowBreak, Grp(),
            Open, Call("actualQueryCount", policy, seed, source, length), Eq, length, Close,
            Land, RowBreak, Grp(),
            Open, Call("stoppingTime", policy, seed, source), Eq, length, Close,
            End, Grp(F.Id("gathered")));
        Formula statement = Disp(All(seedType, F.Id("Type"),
            Seq(OpenBracket, Call("MeasurableSpace", seedType), CloseBracket,
                Rightarrow,
                All(policy, Call("Policy", seedType),
                    All(seed, seedType,
                        All(word, F.Id("Word"),
                            Seq(Call("terminalFirstTrue", word), Rightarrow,
                                Call("policyConformity", policy, seed, word), Rightarrow,
                                All(labels, Call("Labels", word), conclusion))))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite compatible two-arm labels realize a chronological stopped archive with its original seed.",
            H("Finite labels and causal acquired-prefix realization"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("finite-label-realization"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerFiniteLabels.finite_label_realization"),
                    H("One supported completion realizes every prefix and the first stopping time"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Word is a chronological List of pairs of a Boolean arm and a Boolean reply. "
                            + "The archive consists only of the original seed u and this word w; "
                            + "it contains neither a root bit nor an infinite source. False selects "
                            + "the left arm and true selects the right arm. For every natural k, "
                            + "actions(w,k) and replies(w,k) map the corresponding projections over "
                            + "take(k,w). The policy receives their reversals, because actualRun "
                            + "stores acquired histories newest first.")),
                        Paragraph(Text(
                            "terminalFirstTrue(w) requires positive length T and, for each zero-based "
                            + "index k below T, reply k equal to decide(k+1=T). policyConformity(p,u,w) "
                            + "requires action k to equal the same policy p evaluated at the original "
                            + "seed u and the reversed prefixes before k. The seed space is an arbitrary "
                            + "Type with an arbitrary measurable-space instance. No probability law, "
                            + "standard Borel assumption, or additional seed observation is used.")),
                        Paragraph(Text(
                            "sideTotal(w,s) counts arm s in the whole action word, and occurrences(w,s,k) "
                            + "counts it in the prefix before k. A Labels(w) witness supplies, on each arm s, "
                            + "a Boolean label at every index from zero through sideTotal(w,s). The two "
                            + "labels at zero agree. Consecutive finite labels never both equal true. "
                            + "For every query k, its reply is exactly the 00 predicate of the labels at "
                            + "occurrences(w,s,k) and its successor, where s is that query's arm. "
                            + "Finite compatibility means that a Labels(w) witness exists; these auxiliary "
                            + "labels are witnesses of compatibility and are not additional archive fields. "
                            + "Their conditions contain no actualRun equation, source, execution witness, "
                            + "or inverse normal form.")),
                        Paragraph(Text(
                            "extended(z,s,i) keeps every supplied finite label and is false for i beyond "
                            + "sideTotal(w,s). completion(z) has the common label at index zero as root and arm s "
                            + "entry i equal to extended(z,s,i+1). The theorem holds for every Labels witness, "
                            + "using that single completion at all depths. Fin indices in the label-preservation "
                            + "clause are coerced to natural endpoint indices. The last equality coerces T "
                            + "to WithTop Nat. Thus it identifies the first stopping time, as well as "
                            + "the complete terminal state and the number of acquired queries.")),
                        Paragraph(Text(
                            "The causal induction reconstructs the state before each next policy choice. "
                            + "The reconstructed action and reply lists select the recorded arm, and its "
                            + "occurrence count selects the finite-label 00 response. Earlier prefixes "
                            + "remain active; the final prefix is stopped. The zero tail ensures global "
                            + "no-adjacent-ones support beyond both acquired arm lengths.")),
                        Paragraph(Text(
                            "This finite realization establishes a support-level component of the "
                            + "common-parameter stopped-archive construction. It does not assert root recovery, "
                            + "an inverse normal form, opportunity enumeration, positive Markov cylinder mass, "
                            + "likelihood or posterior formulas, almost-sure termination, or measurability "
                            + "of the archive maps. Those require separate results."))),
                    DescribeRole.Theorem))));
    }

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, type, Comma, Sp, body);
}
