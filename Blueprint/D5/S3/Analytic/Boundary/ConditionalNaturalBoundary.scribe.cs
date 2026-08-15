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
        Formula assumptions = F.Seq(
            F.Id("TailNonvanishing"), F.Sp, F.Land, F.Sp,
            F.Open, F.Id("LineCondition"), F.Sp, F.Lor, F.Sp,
            F.Id("AlternateCondition"), F.Close);
        Formula axisPoint = F.Seq(F.Id("i"), F.Id("t"));
        Formula boundary = F.Seq(
            assumptions, F.Sp, F.Rightarrow, F.Sp,
            F.Forall, F.Sp, F.Id("t"), F.Sp, F.InMacro, F.Sp,
            F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Esc,
            F.Neg, Call("AnalyticAt", F.Id("f"), axisPoint));
        Formula gate = F.Seq(
            F.Forall, F.Sp, F.Id("t"), F.Sp, F.InMacro, F.Sp,
            F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Esc,
            Call("AnalyticAt", F.Id("f"), axisPoint), F.Sp, F.Rightarrow, F.Sp,
            F.Operatorname, F.Grp(F.Id("Eventually")), F.Underscore,
            F.Grp(F.Id("n"), F.To, F.Infty), F.Sp, F.Open,
            Call("ScaledZeroPattern", F.Id("t"), F.Id("n")),
            F.Sp, F.Lor, F.Sp,
            Call("TailZeroCollision", F.Id("t"), F.Id("n")), F.Close);

        return F.Disp(F.Seq(F.Open, boundary, F.Close, F.Sp, F.Land, F.RowBreak, gate, F.Dot));
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
