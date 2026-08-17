using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class RecurrentCoboundaryObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A recurrent nonvanishing cocycle cannot be a continuous coboundary.",
        H("Recurrence Obstructs Continuous Coboundaries"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-recurrent-nonzero-cocycle-is-not-a-continuous-coboundary"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/RecurrentCoboundaryObstruction."
                        + "recurrent_cocycle_not_continuous_coboundary"),
                H("A recurrent nonzero cocycle is not a continuous coboundary"),
                StatementSource.FromAuthor(RecurrentCoboundaryObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Phi be a real flow on a topological space X, let c take values in "
                            + "a topological additive group V, and let the times tend to positive "
                            + "infinity. Assume the sampled orbit returns to x while the sampled "
                            + "cocycle does not converge to zero.")),
                    Paragraph(Text(
                        "If c were the coboundary of a continuous h, continuity along the recurrent "
                            + "orbit would force h(Phi(times(n), x)) to converge to h(x). Subtracting "
                            + "the constant h(x) would then force the sampled cocycle to converge to "
                            + "zero, contradicting the hypothesis.")),
                    Paragraph(Text(
                        "Loogle supplied the exact supporting declarations Continuous.tendsto and "
                            + "Filter.Tendsto.sub_const, both applied in the proof. Repository and "
                            + "pinned-Mathlib searches found no full-statement match. LeanSearch's "
                            + "API search endpoint returned HTTP 404 and yielded no result.")),
                    Paragraph(Text(
                        "The natural-number times, the identity flow on Unit, and a real cocycle "
                            + "equal to time give checked jointly satisfiable limit hypotheses."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var separated = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                separated.Add(Comma);
                separated.Add(Sp);
            }

            separated.Add(arguments[index]);
        }

        return Seq(function, Open, Seq([.. separated]), Close);
    }

    private static Formula RecurrentCoboundaryObstructionFormula()
    {
        Formula xType = F.Id("X");
        Formula vType = F.Id("V");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula n = F.Id("n");
        Formula t = F.Id("t");
        Formula phi = Phi;
        Formula cocycle = F.Id("c");
        Formula times = F.Id("times");
        Formula h = F.Id("h");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula atTop = Seq(Operatorname, Grp(F.Id("atTop")));

        Formula Tendsto(Formula function, Formula source, Formula target) =>
            Apply(Seq(Operatorname, Grp(F.Id("Tendsto"))), function, source, target);

        Formula Nhds(Formula point) =>
            Apply(Seq(Operatorname, Grp(F.Id("nhds"))), point);

        Formula Sample(Formula function) =>
            Seq(Open, n, Sp, Mapsto, Sp,
                Apply(function, Apply(times, n), x), Close);

        Formula Coboundary(Formula time, Formula point) =>
            Seq(Apply(cocycle, time, point), Sp, Eq, Sp,
                Apply(h, Apply(phi, time, point)), Sp, Minus, Sp, Apply(h, point));

        return Disp(Seq(
            Forall, Sp, xType, Comma, Sp, vType, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("TopologicalSpace")),
            Open, xType, Close, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("AddGroup")),
            Open, vType, Close, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("TopologicalSpace")),
            Open, vType, Close, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("IsTopologicalAddGroup")),
            Open, vType, Close, CloseBracket, Comma, Esc,
            phi, Colon, Sp, Apply(Seq(Operatorname, Grp(F.Id("Flow"))), real, xType), Comma, Sp,
            cocycle, Colon, Sp, real, Sp, To, Sp, xType, Sp, To, Sp, vType, Comma, Sp,
            x, Colon, Sp, xType, Comma, Sp,
            times, Colon, Sp, naturals, Sp, To, Sp, real, Comma, Esc,
            Tendsto(times, atTop, atTop), Sp, Land, Sp,
            Tendsto(Sample(phi), atTop, Nhds(x)), Sp, Land, Sp,
            Neg, Tendsto(Sample(cocycle), atTop, Nhds(D(0))), Sp, Rightarrow, Esc,
            Neg, Exists, Sp, h, Colon, Sp, xType, Sp, To, Sp, vType, Comma, Esc,
            Apply(Seq(Operatorname, Grp(F.Id("Continuous"))), h), Sp, Land, Sp,
            Forall, Sp, t, Comma, Sp, y, Comma, Sp,
            Coboundary(t, y), Dot));
    }
}
