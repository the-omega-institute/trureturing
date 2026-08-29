using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class ConditionalNaturalBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Accumulating genuine poles force the conditional imaginary-axis boundary, while any "
        + "analytic gate exposes one of two rigid cancellation channels.",
        H("Conditional Natural Boundary and Gate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("accumulating-poles-force-the-boundary-and-classify-a-gate"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Boundary/ConditionalNaturalBoundary."
                    + "conditional_natural_boundary_and_gate"),
                H("Accumulating poles force the boundary and classify a gate"),
                StatementSource.FromAuthor(BoundaryAndGateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real target t, the transported candidates "
                        + "1/(2c_n) + i gamma_n(t)/c_n converge to it on the imaginary axis. "
                        + "Under tail nonvanishing and either zero-location condition, every "
                        + "candidate has negative meromorphic order and is therefore a genuine "
                        + "pole. Analyticity at it would hold throughout a neighborhood and hence "
                        + "eventually at the convergent candidates, contradicting their negative "
                        + "orders.")),
                    Paragraph(Text(
                        "The same neighborhood argument gives the unconditional gate theorem. "
                        + "If the function is analytic at an axis target, all sufficiently late "
                        + "transported candidates are analytic and thus cannot have negative "
                        + "order. The supplied cancellation classification then puts each of them "
                        + "in either the scaled-zero pattern or the tail-zero collision channel.")),
                    Paragraph(Text(
                        "Repository search found the exact candidate-accumulation theorem but no "
                        + "declaration combining it with both conclusions. The proof imports that "
                        + "limit directly and uses Mathlib's eventually_analyticAt and "
                        + "meromorphicOrderAt_nonneg. The analytic and number-theoretic inputs that "
                        + "make candidates into poles or classify their cancellation remain explicit "
                        + "hypotheses; this theorem closes their topological assembly.")),
                    Paragraph(Text(
                        "This is the complete two-part formalization of source theorem 6.62: the "
                        + "conditional boundary statement and its unconditional contrapositive gate "
                        + "statement are retained in one conjunction."))),
                DescribeRole.Theorem))));

    private static Formula BoundaryAndGateFormula()
    {
        Formula f = F.Id("f"), scale = F.Id("scale"), height = F.Id("height");
        Formula tailNonvanishing = F.Id("tailNonvanishing");
        Formula lineCondition = F.Id("lineCondition");
        Formula alternateCondition = F.Id("alternateCondition");
        Formula scaledZeroPattern = F.Id("scaledZeroPattern");
        Formula tailZeroCollision = F.Id("tailZeroCollision");
        Formula hscale = F.Id("hscale"), hheight = F.Id("hheight");
        Formula hpoles = F.Id("hpoles"), hchannels = F.Id("hchannels");
        Formula target = F.Id("target"), n = F.Id("n");
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula natural = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula complex = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula proposition = F.Seq(F.Operatorname, F.Grp(F.Id("Prop")));
        Formula atTop = F.Seq(F.Operatorname, F.Grp(F.Id("atTop")));
        Formula assumptions = F.Seq(
            tailNonvanishing, F.Sp, F.Land, F.Sp,
            F.Open, lineCondition, F.Sp, F.Lor, F.Sp, alternateCondition, F.Close);
        Formula candidate(Formula point, Formula index) => Call(
            "candidatePoint", scale, Call("height", point), index);
        Formula pole(Formula point, Formula index) => F.Seq(
            Call("meromorphicOrderAt", f, candidate(point, index)),
            F.Sp, F.Lt, F.Sp, F.D(0));
        Formula channels(Formula point, Formula index) => F.Seq(
            Call("scaledZeroPattern", point, index), F.Sp, F.Lor, F.Sp,
            Call("tailZeroCollision", point, index));
        Formula axisPoint(Formula point) => F.Seq(
            F.Open, point, F.Colon, F.Sp, complex, F.Close,
            F.Sp, F.Times, F.Sp, F.Id("I"));
        Formula analyticAt(Formula point) =>
            Call("AnalyticAt", complex, f, axisPoint(point));
        Formula poleInputs = F.Seq(
            F.Forall, F.Sp, target, F.Colon, F.Sp, real, F.Comma, F.Sp,
            F.Forall, F.Sp, n, F.Colon, F.Sp, natural, F.Comma, F.Sp,
            pole(target, n));
        Formula channelInputs = F.Seq(
            F.Forall, F.Sp, target, F.Colon, F.Sp, real, F.Comma, F.Sp,
            F.Forall, F.Sp, n, F.Colon, F.Sp, natural, F.Comma, F.Sp,
            F.Neg, F.Open, pole(target, n), F.Close, F.Sp, F.Rightarrow, F.Sp,
            channels(target, n));
        Formula boundary = F.Seq(
            assumptions, F.Sp, F.Rightarrow, F.Sp,
            F.Forall, F.Sp, target, F.Colon, F.Sp, real, F.Comma, F.Sp,
            F.Neg, analyticAt(target));
        Formula gate = F.Seq(
            F.Forall, F.Sp, target, F.Colon, F.Sp, real, F.Comma, F.Sp,
            analyticAt(target), F.Sp, F.Rightarrow, F.Sp,
            F.Operatorname, F.Grp(F.Id("Eventually")), F.Underscore,
            F.Grp(n, F.Sp, F.InMacro, F.Sp, atTop), F.Sp,
            F.Open, channels(target, n), F.Close);
        Formula normalizedHeight = F.Seq(
            Call("height", target, n), F.Sp, F.Slash, F.Sp, Call("scale", n));
        Formula heightLimit = F.Seq(
            F.Forall, F.Sp, target, F.Colon, F.Sp, real, F.Comma, F.Sp,
            Call("Tendsto",
                F.Seq(F.Open, n, F.Colon, F.Sp, natural, F.Sp, F.Mapsto, F.Sp,
                    normalizedHeight, F.Close),
                atTop, Call("nhds", target)));

        return F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("aligned")),
            F.Forall, F.Sp, f, F.Colon, F.Sp,
            complex, F.Sp, F.To, F.Sp, complex, F.Comma, F.RowBreak, F.Grp(),
            F.Forall, F.Sp, scale, F.Colon, F.Sp,
            natural, F.Sp, F.To, F.Sp, real, F.Comma, F.Sp,
            height, F.Colon, F.Sp,
            real, F.Sp, F.To, F.Sp, natural, F.Sp, F.To, F.Sp, real,
            F.Comma, F.RowBreak, F.Grp(),
            F.Forall, F.Sp, tailNonvanishing, F.Comma, F.Sp, lineCondition,
            F.Comma, F.Sp, alternateCondition, F.Colon, F.Sp, proposition,
            F.Comma, F.RowBreak, F.Grp(),
            F.Forall, F.Sp, scaledZeroPattern, F.Comma, F.Sp, tailZeroCollision,
            F.Colon, F.Sp, real, F.Sp, F.To, F.Sp, natural, F.Sp, F.To, F.Sp,
            proposition, F.Comma, F.RowBreak, F.Grp(),
            F.Forall, F.Sp, hscale, F.Colon, F.Sp,
            Call("Tendsto", scale, atTop, atTop), F.Comma, F.RowBreak, F.Grp(),
            F.Forall, F.Sp, hheight, F.Colon, F.Sp,
            F.Open, heightLimit, F.Close, F.Comma, F.RowBreak, F.Grp(),
            F.Forall, F.Sp, hpoles, F.Colon, F.Sp,
            F.Open, assumptions, F.Sp, F.Rightarrow, F.Sp, poleInputs, F.Close,
            F.Comma, F.RowBreak, F.Grp(),
            F.Forall, F.Sp, hchannels, F.Colon, F.Sp,
            F.Open, channelInputs, F.Close, F.Comma, F.RowBreak, F.Grp(),
            F.Open, boundary, F.Close, F.Sp, F.Land, F.RowBreak, F.Grp(),
            gate, F.Dot,
            F.End, F.Grp(F.Id("aligned"))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
