using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence.MeanKernels;

internal sealed class LogarithmicMeanSandwichDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Divergence/MeanKernels/LogarithmicMeanSandwich",
            "The logarithmic-mean kernel lies between the arithmetic and harmonic reciprocal kernels."),
        H("The Logarithmic-Mean Kernel Sandwich"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("logarithmic-mean-kernel-lies-between-arithmetic-and-harmonic"),
                H("The logarithmic-mean kernel lies between the arithmetic and harmonic kernels"),
                LeanTheorem(
                    "D5/S3/Divergence/MeanKernels/LogarithmicMeanSandwich.logMean_kernel_sandwich"),
                Disp(Seq(
                    Forall, Sp, F.Id("a"), Comma, F.Id("b"), Comma, Sp,
                    D(0), Lt, F.Id("a"), Sp, Rightarrow, Sp,
                    D(0), Lt, F.Id("b"), Sp, Rightarrow, Sp,
                    F.Id("a"), Neq, Sp, F.Id("b"), Sp, Rightarrow, RowBreak,
                    Frac, Grp(D(2)), Grp(F.Id("a"), Plus, F.Id("b")), Le, Sp,
                    Frac, Grp(Log, Sp, F.Id("a"), Minus, Log, Sp, F.Id("b")), Grp(F.Id("a"), Minus, F.Id("b")),
                    Le, Sp,
                    Frac,
                    Grp(F.Id("a"), Caret, Grp(Minus, D(1)), Plus, F.Id("b"), Caret, Grp(Minus, D(1))),
                    Grp(D(2)))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For distinct positive reals a and b, the reciprocal kernel of the logarithmic "
                        + "mean, (log a − log b)/(a − b), lies between the reciprocal kernel of the "
                        + "arithmetic mean, 2/(a + b), and the reciprocal kernel of the harmonic mean, "
                        + "(a⁻¹ + b⁻¹)/2. Inverting the three kernels, this is exactly the classical "
                        + "chain of harmonic, logarithmic and arithmetic means, H(a,b) ≤ L(a,b) ≤ A(a,b).")),
                    Paragraph(Text(
                        "The proof reduces each bound to a one-variable inequality in the ratio t = a/b "
                        + "(taken at least one by symmetry of the three kernels under exchanging a and b). "
                        + "The upper bound is 2(t − 1)/(t + 1) ≤ log t, obtained from the monotonicity of "
                        + "s ↦ log s − 2(s − 1)/(s + 1) on the ray from one, whose derivative "
                        + "(s − 1)²/(s(s + 1)²) is nonnegative. The lower bound is log t ≤ (t − 1/t)/2, "
                        + "which is the statement that a real number is at most its hyperbolic sine, applied "
                        + "at log t ≥ 0.")),
                    Paragraph(Text(
                        "This is not a restatement of a library lemma: a search of Mathlib finds the "
                        + "logarithm quotient and product laws, monotonicity from a nonnegative derivative, "
                        + "and the sine-hyperbolic bound, but no logarithmic mean and no assembled kernel "
                        + "sandwich. The chain is the load-bearing ordering behind the corresponding "
                        + "path-divergence comparison; only the mean-kernel sandwich itself is claimed here, "
                        + "not the integral path-divergence ordering it implies.")))
            )),
        []));
}
