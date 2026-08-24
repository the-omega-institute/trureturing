using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class StochasticDescentLumpabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero finite same-fiber descent defect is equivalent to strong lumpability, which is "
            + "equivalent to exact quotient factorization and yields zero uniform descent error.",
        H("Zero Descent Defect and Exact Lumpability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-descent-defect-characterizes-strong-lumpability"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability."
                        + "descent_defect_zero_iff_strongly_lumpable"),
                H("Zero descent defect characterizes strong lumpability"),
                StatementSource.FromAuthor(ZeroDefectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The descent defect is the largest total-variation separation between "
                            + "rows indexed by source states in the same q-fiber. It vanishes "
                            + "exactly when every such pair of rows agrees, which is strong "
                            + "lumpability along q.")),
                    Paragraph(Text(
                        "In one direction, separation of total variation turns a zero pairwise "
                            + "distance into equality of rows. In the other, fiberwise constancy "
                            + "makes every term in the finite maximum zero; a diagonal pair "
                            + "supplies the matching lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strong-lumpability-is-exact-quotient-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability."
                        + "strongly_lumpable_iff_exact_quotient_kernel"),
                H("Strong lumpability is exact quotient factorization"),
                StatementSource.FromAuthor(ExactFactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A kernel is constant on q-fibers exactly when its row assignment factors "
                            + "through the readout space B. Thus one may assign to each attained "
                            + "readout value the common row of its fiber and choose arbitrary rows "
                            + "outside the image of q.")),
                    Paragraph(Text(
                        "Conversely, any quotient kernel that reproduces K at q(x) gives identical "
                            + "rows to source states with the same readout. This equivalence needs "
                            + "no finiteness or stochasticity assumptions."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("exact-quotient-kernel-has-zero-uniform-descent-error"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability."
                        + "uniform_descent_error_eq_zero_of_exact_quotient_kernel"),
                H("An exact quotient kernel has zero uniform descent error"),
                StatementSource.FromAuthor(ExactQuotientZeroErrorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When Kbar evaluated at q(x) reproduces the row K(x) for every source "
                            + "state, every total-variation discrepancy in the uniform descent "
                            + "error is zero. The finite maximum is therefore zero.")),
                    Paragraph(Text(
                        "The conclusion depends only on exact row reproduction. In particular, it "
                            + "does not require either K or Kbar to be row-stochastic."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("strong-lumpability-admits-zero-error-exact-quotient"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability."
                        + "strongly_lumpable_has_zero_uniform_descent_error"),
                H("Strong lumpability admits a zero-error exact quotient"),
                StatementSource.FromAuthor(LumpabilityZeroErrorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Strong lumpability supplies a kernel on the readout space whose row at "
                            + "q(x) equals the original row at x. For this same quotient kernel, "
                            + "the uniform descent error vanishes.")),
                    Paragraph(Text(
                        "The result packages exact factorization and zero approximation error into "
                            + "one witness. Strong lumpability alone is sufficient; no stochasticity "
                            + "hypothesis is imposed."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("zero-defect-makes-the-best-descent-error-nonnegative"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability."
                        + "best_descent_error_nonneg_of_zero_defect"),
                H("At zero defect the best descent error is nonnegative"),
                StatementSource.FromAuthor(BestErrorNonnegativeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a row-stochastic kernel, the general lower bound places half of the "
                            + "same-fiber descent defect below the best quotient-descent error. "
                            + "When that defect is zero, the bound reduces to nonnegativity.")),
                    Paragraph(Text(
                        "This is a boundary specialization of the defect lower bound, rather than "
                            + "an additional assertion that an optimizing quotient kernel exists."))),
                DescribeRole.Lemma))));

    private static Formula ZeroDefectFormula()
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
            Call("descentDefect", q, kernel), Sp, Eq, Sp, D(0), Sp,
            Iff, Sp, Call("StronglyLumpable", q, kernel), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ExactFactorizationFormula()
    {
        Formula source = F.Id("X");
        Formula readout = F.Id("B");
        Formula q = F.Id("q");
        Formula kernel = F.Id("K");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, readout, Comma, RowBreak, Grp(),
            q, Colon, Sp, source, Sp, To, Sp, readout, Comma, Sp,
            kernel, Colon, Sp, source, Sp, To, Sp, readout, Sp, To, Sp, real,
            Comma, RowBreak, Grp(),
            Call("StronglyLumpable", q, kernel), Sp,
            Iff, Sp, Call("ExactQuotientKernel", q, kernel), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ExactQuotientZeroErrorFormula()
    {
        Formula source = F.Id("X");
        Formula readout = F.Id("B");
        Formula q = F.Id("q");
        Formula kernel = F.Id("K");
        Formula quotient = F.Id("Kbar");
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
            quotient, Colon, Sp, readout, Sp, To, Sp, readout, Sp, To, Sp, real,
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, state, Colon, Sp, source, Comma, Sp,
            At(kernel, state), Sp, Eq, Sp, At(quotient, At(q, state)), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Call("uniformDescentError", q, kernel, quotient), Sp, Eq, Sp, D(0), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula LumpabilityZeroErrorFormula()
    {
        Formula source = F.Id("X");
        Formula readout = F.Id("B");
        Formula q = F.Id("q");
        Formula kernel = F.Id("K");
        Formula quotient = F.Id("Kbar");
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
            Call("StronglyLumpable", q, kernel), Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, quotient, Colon, Sp,
            readout, Sp, To, Sp, readout, Sp, To, Sp, real, Comma, RowBreak, Grp(),
            Open, Forall, Sp, state, Colon, Sp, source, Comma, Sp,
            At(kernel, state), Sp, Eq, Sp, At(quotient, At(q, state)), Close,
            Sp, Land, RowBreak, Grp(),
            Call("uniformDescentError", q, kernel, quotient), Sp, Eq, Sp, D(0), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula BestErrorNonnegativeFormula()
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
            Call("IsRowStochastic", kernel), Sp, Land, Sp,
            Call("descentDefect", q, kernel), Sp, Eq, Sp, D(0), Sp,
            Rightarrow, RowBreak, Grp(),
            D(0), Sp, Leq, Sp, Call("bestDescentError", q, kernel), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
