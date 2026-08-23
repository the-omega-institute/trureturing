using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class MinimalPredictiveSummaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every future-sufficient linear summary factors uniquely onto the predictive space.",
        H("Minimal Predictive Summary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimal-predictive-summary-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fibers/MinimalPredictiveSummary."
                        + "minimal_predictive_summary"),
                H("Future sufficiency forces the minimal dimension bound"),
                StatementSource.FromAuthor(MinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the imported real HermitianTraceZero(d) space. The "
                            + "predictive space is constructed as the real span of every centered "
                            + "effect after every finite iterate of the given Heisenberg map.")),
                    Paragraph(Text(
                        "The hypothesis states directly that equality under the linear summary "
                            + "forces equality of every such future inner-product coordinate for "
                            + "all carrier vectors. Hence the summary kernel lies in the kernel "
                            + "of the canonical orthogonal projection onto the predictive space.")),
                    Paragraph(Text(
                        "The first isomorphism theorem then constructs a factor on the attainable "
                            + "summary range. Surjectivity of the orthogonal projection makes this "
                            + "factor surjective, giving the displayed finrank lower bound, while "
                            + "range witnesses prove uniqueness.")),
                    Paragraph(Text(
                        "Repository search found the canonical trace-zero carrier and finite tower, "
                            + "but no vector-valued range factorization with this dimension clause. "
                            + "Pinned Mathlib supplies projectionOnto, liftQ, quotKerEquivRange, "
                            + "and finrank_le_finrank_of_surjective, all applied by the proof."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula LinearMap(Formula scalar, Formula source, Formula target) =>
        Call("LinearMap", scalar, source, target);

    private static Formula Inner(Formula scalar, Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Rangle, Underscore, Grp(scalar));

    private static Formula MinimalityFormula()
    {
        Formula d = F.Id("d");
        Formula r = F.Id("r");
        Formula w = F.Id("W");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula carrier = Call("HermitianTraceZero", d);
        Formula heisenberg = F.Id("H");
        Formula effects = F.Id("E");
        Formula summary = F.Id("L");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula n = F.Id("n");
        Formula a = F.Id("a");
        Formula factor = F.Id("h");
        Formula visible = Call("predictiveSpace", heisenberg, effects);
        Formula projection = Call("predictiveProjection", heisenberg, effects);
        Formula summaryRange = Call("range", summary);
        Formula rangeRestrict = Call("rangeRestrict", summary);
        Formula iterate = Seq(heisenberg, Caret, Grp(n));
        Formula futureEffect = Apply(iterate, Apply(effects, a));

        return Disp(Seq(
            Forall, Sp, d, Comma, Sp, r, Comma, Sp, w, Comma, RowBreak, Grp(),
            heisenberg, Colon, Sp, LinearMap(real, carrier, carrier), Comma, Sp,
            effects, Colon, Sp, Call("Fin", Seq(r, Plus, D(1))), Sp, To, carrier,
            Comma, RowBreak, Grp(),
            summary, Colon, Sp, LinearMap(real, carrier, w), Comma, RowBreak, Grp(),
            Open,
            Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            Apply(summary, x), Sp, Eq, Sp, Apply(summary, y), Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, n, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            a, InMacro, Sp, Call("Fin", Seq(r, Plus, D(1))), Comma, Sp,
            Inner(real, x, futureEffect), Sp, Eq, Sp, Inner(real, y, futureEffect),
            Close, Sp, Rightarrow, RowBreak, Grp(),
            Open,
            Exists, Bang, Sp, factor, Colon, Sp,
            LinearMap(real, summaryRange, visible), Comma, Sp,
            projection, Sp, Eq, Sp, factor, Sp, Circ, Sp, rangeRestrict,
            Close, Sp, Land, RowBreak, Grp(),
            Call("finrank", real, visible), Sp, Leq, Sp,
            Call("finrank", real, summaryRange), Dot));
    }
}
