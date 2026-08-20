using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class RootPulseRefinementDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The root-pulse chain raises and then lowers completion depth while attaining the finite-state bound.",
        H("Root-Pulse Refinement Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("root-pulse-refinement-depth-counterexample"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/RootPulseRefinementDepth."
                        + "root_pulse_refinement_depth_counterexample"),
                H("Refinement depth is nonmonotone and the bound is sharp"),
                StatementSource.FromAuthor(RefinementDepthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For n at least three, the state carrier is Fin n and the update is "
                            + "truncated predecessor. The three readouts are the constant map r, "
                            + "the root-pulse map q, and the identity map e.")),
                    Paragraph(Text(
                        "For each readout, the completion state Z is constructed as the quotient "
                            + "by equality of every future readout coordinate. Its depth is the "
                            + "repository observationStabilityDepth, the least index at which two "
                            + "successive finite-word relations agree.")),
                    Paragraph(Text(
                        "The factorization r = hr composed with q states that q refines r; its "
                            + "depth rises strictly from zero to n minus two. The factorization q "
                            + "= hq composed with e states that e refines q; its depth falls "
                            + "strictly back to zero.")),
                    Paragraph(Text(
                        "The imported root-pulse sharpness theorem supplies the exact middle "
                            + "depth. Separating future profiles identify the root-pulse and "
                            + "identity completion quotients with Fin n, while the constant "
                            + "completion is a singleton. Surjectivity of q gives a two-element "
                            + "range and hence equality in the finite-state bound."))),
                DescribeRole.Theorem))));

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var content = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Cardinality(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula StableDepth(Formula readout) =>
        Call(Sub(F.Id("m"), Star), readout);

    private static Formula CompletionCardinality(Formula readout) =>
        Cardinality(Sub(F.Id("Z"), readout));

    private static Formula RefinementDepthFormula()
    {
        Formula n = F.Id("n");
        Formula r = F.Id("r");
        Formula q = F.Id("q");
        Formula e = F.Id("e");
        Formula hr = F.Id("hr");
        Formula hq = F.Id("hq");
        Formula chainDepth = Seq(n, Minus, D(2));
        Formula constantDepth = StableDepth(r);
        Formula rootDepth = StableDepth(q);
        Formula identityDepth = StableDepth(e);
        Formula stateCount = Cardinality(Call(
            Seq(Operatorname, Grp(F.Id("Fin"))), n));
        Formula rangeCount = Cardinality(Call(
            Seq(Operatorname, Grp(F.Id("range"))), q));

        Formula coarseRefinement = Seq(
            Open,
            Exists, Sp, hr, Colon, Sp,
            F.Id("Bool"), Sp, To, Sp, F.Id("PUnit"), Comma, Sp,
            r, Sp, Eq, Sp, hr, Sp, Circ, Sp, q,
            Close, Sp, Land, Sp,
            constantDepth, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            constantDepth, Sp, Lt, Sp, rootDepth, Sp, Land, Sp,
            rootDepth, Sp, Eq, Sp, chainDepth);

        Formula fineRefinement = Seq(
            Open,
            Exists, Sp, hq, Colon, Sp,
            Call(Seq(Operatorname, Grp(F.Id("Fin"))), n), Sp,
            To, Sp, F.Id("Bool"), Comma, Sp,
            q, Sp, Eq, Sp, hq, Sp, Circ, Sp, e,
            Close, Sp, Land, Sp,
            rootDepth, Sp, Eq, Sp, chainDepth, Sp, Land, Sp,
            identityDepth, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            identityDepth, Sp, Lt, Sp, rootDepth);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(3), Sp, Leq, Sp, n, Sp, Rightarrow, RowBreak,
            constantDepth, Sp, Eq, Sp, D(0), Sp, Land, RowBreak,
            rootDepth, Sp, Eq, Sp, chainDepth, Sp, Land, RowBreak,
            identityDepth, Sp, Eq, Sp, D(0), Sp, Land, RowBreak,
            CompletionCardinality(r), Sp, Eq, Sp, D(1), Sp, Land, RowBreak,
            CompletionCardinality(q), Sp, Eq, Sp, n, Sp, Land, RowBreak,
            CompletionCardinality(e), Sp, Eq, Sp, n, Sp, Land, RowBreak,
            Open, coarseRefinement, Close, Sp, Land, RowBreak,
            Open, fineRefinement, Close, Sp, Land, RowBreak,
            rootDepth, Sp, Eq, Sp, chainDepth, Sp, Land, RowBreak,
            chainDepth, Sp, Eq, Sp, stateCount, Sp, Minus, Sp, rangeCount, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
