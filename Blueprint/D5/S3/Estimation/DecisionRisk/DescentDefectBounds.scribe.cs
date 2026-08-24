using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class DescentDefectBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The optimal finite quotient-descent error is controlled by the same-fiber "
            + "total-variation defect, and deterministic target postprocessing contracts that defect.",
        H("Bounds and Contraction for the Descent Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("best-descent-error-is-at-least-half-the-fiber-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/DescentDefectBounds."
                        + "best_descent_error_lower_bound"),
                H("Best descent error is at least half the fiber defect"),
                StatementSource.FromAuthor(LowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The descent defect is the largest total-variation distance between two "
                            + "rows of K whose source states have the same readout under q. The best "
                            + "descent error is the infimum, over row-stochastic kernels on B, of "
                            + "the largest distance from K at x to the candidate row at q(x).")),
                    Paragraph(Text(
                        "For any candidate quotient kernel, the triangle inequality bounds every "
                            + "same-fiber row distance by the sum of two candidate errors, hence by "
                            + "twice the uniform error. Maximizing over the fiber pairs and then "
                            + "taking the infimum gives the factor-one-half lower bound. Row "
                            + "stochasticity of K also supplies a constant admissible candidate, so "
                            + "the infimum is taken over a nonempty family bounded below by zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("representatives-bound-best-descent-error-by-the-fiber-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/DescentDefectBounds."
                        + "best_descent_error_upper_bound_of_representatives"),
                H("Fiber representatives bound the best descent error from above"),
                StatementSource.FromAuthor(RepresentativeUpperBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A representative map chooses a source state for every readout value. The "
                            + "required compatibility says that, for every source state x, the "
                            + "representative selected at q(x) lies in the same q-fiber as x.")),
                    Paragraph(Text(
                        "Using the row of K at each chosen representative defines a row-stochastic "
                            + "kernel on B. Its error at x is a same-fiber total-variation distance, "
                            + "so it is at most the descent defect. The infimum over all admissible "
                            + "kernels is therefore no larger than that defect."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "deterministic-postprocessing-does-not-increase-the-descent-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/DescentDefectBounds."
                        + "postprocessed_descent_defect_le"),
                H("Deterministic postprocessing contracts the descent defect"),
                StatementSource.FromAuthor(PostprocessingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A deterministic target map r induces the zero-one stochastic channel that "
                            + "sends each point of B to its image in C. Total variation cannot "
                            + "increase when the same channel is applied to both rows of a pair.")),
                    Paragraph(Text(
                        "Applying this contraction to every pair of source states in the same "
                            + "q-fiber and then taking the finite maximum proves that the "
                            + "postprocessed defect is at most the original defect. No "
                            + "row-stochasticity assumption on K is needed for this comparison."))),
                DescribeRole.Lemma))));

    private static Formula LowerBoundFormula()
    {
        Formula source = F.Id("X");
        Formula readout = F.Id("B");
        Formula q = F.Id("q");
        Formula kernel = F.Id("K");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, readout, Comma, Sp,
            Call("Fintype", source), Comma, Sp,
            Call("Nonempty", source), Comma, Sp,
            Call("Fintype", readout), Comma, RowBreak, Grp(),
            q, Colon, Sp, source, Sp, To, Sp, readout, Comma, Sp,
            kernel, Colon, Sp, source, Sp, To, Sp, readout, Sp, To, Sp, real,
            Comma, RowBreak, Grp(),
            Call("IsRowStochastic", kernel), Sp, Rightarrow, RowBreak, Grp(),
            Frac, Grp(D(1)), Grp(D(2)), Sp,
            Call("descentDefect", q, kernel), Sp, Leq, Sp,
            Call("bestDescentError", q, kernel), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula RepresentativeUpperBoundFormula()
    {
        Formula source = F.Id("X");
        Formula readout = F.Id("B");
        Formula q = F.Id("q");
        Formula kernel = F.Id("K");
        Formula representative = F.Id("rep");
        Formula state = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, readout, Comma, Sp,
            Call("Fintype", source), Comma, Sp,
            Call("Nonempty", source), Comma, Sp,
            Call("Fintype", readout), Comma, RowBreak, Grp(),
            q, Colon, Sp, source, Sp, To, Sp, readout, Comma, Sp,
            kernel, Colon, Sp, source, Sp, To, Sp, readout, Sp, To, Sp, real,
            Comma, RowBreak, Grp(),
            representative, Colon, Sp, readout, Sp, To, Sp, source, Comma, RowBreak, Grp(),
            Call("IsRowStochastic", kernel), Sp, Land, Sp,
            Open, Forall, Sp, state, Colon, Sp, source, Comma, Sp,
            At(q, At(representative, At(q, state))), Sp, Eq, Sp, At(q, state), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Call("bestDescentError", q, kernel), Sp, Leq, Sp,
            Call("descentDefect", q, kernel), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula PostprocessingFormula()
    {
        Formula source = F.Id("X");
        Formula target = F.Id("B");
        Formula output = F.Id("C");
        Formula q = F.Id("q");
        Formula kernel = F.Id("K");
        Formula postprocess = F.Id("r");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, target, Comma, Sp, output, Comma, Sp,
            Call("Fintype", source), Comma, Sp,
            Call("Nonempty", source), Comma, Sp,
            Call("Fintype", target), Comma, Sp,
            Call("Fintype", output), Comma, RowBreak, Grp(),
            q, Colon, Sp, source, Sp, To, Sp, target, Comma, Sp,
            kernel, Colon, Sp, source, Sp, To, Sp, target, Sp, To, Sp, real,
            Comma, RowBreak, Grp(),
            postprocess, Colon, Sp, target, Sp, To, Sp, output, Comma, RowBreak, Grp(),
            Call("postprocessedDescentDefect", q, kernel, postprocess), Sp, Leq, Sp,
            Call("descentDefect", q, kernel), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
