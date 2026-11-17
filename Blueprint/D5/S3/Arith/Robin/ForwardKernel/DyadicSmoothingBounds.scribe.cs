using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class DyadicSmoothingBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/DyadicSmoothingBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform smoothing estimates.",
        H("Bounds for dyadic smoothing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("increment-locally-bounded-measurable"),
                DeclarationHandle.Create(Prefix + "increment_lbm"),
                H("Local bounds for increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every fixed forward increment of a locally bounded Borel measurable real function is again locally bounded and Borel measurable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("locally-bounded-measurable-mem-lp"),
                DeclarationHandle.Create(Prefix + "lbm_memLp"),
                H("Square integrability on bounded intervals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every locally bounded Borel measurable real function belongs to L2 for Lebesgue measure restricted to any bounded interval (a,b]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continuous-locally-bounded-measurable"),
                DeclarationHandle.Create(Prefix + "continuous_lbm"),
                H("Compact bounds for a continuous function"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every continuous real function is Borel measurable and bounded in absolute value on every compact real interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-smoothing-bounds"),
                DeclarationHandle.Create(Prefix + "dyadic_smoothing_bounds"),
                H("Uniform smoothing estimates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be locally bounded and measurable, h>0, A>=0, a<=b, L<=a, and b+4k<=U. Suppose the L2 norm of D_u E on [L,U] is at most A*sqrt(u) for every h<=u<=8k. Simultaneously for every h<=R<=2k, the L2 norms on [a,b] of B_R, its derivative, and the derivative of Z_R are at most 2A*sqrt(R), 4A/sqrt(R), and 2A/sqrt(R), respectively. Pointwise on [a,b], the absolute values of B_R and the derivative of Z_R are at most 2A and 2A/R. All translations are bounded using the larger interval [L,U]. Taking A to be a fixed multiple of sqrt(X*log(X)) gives the five estimates in (491.5)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smoothing-residual-interval-l2-le"),
                DeclarationHandle.Create(Prefix + "smoothing_residual_intervalL2_le"),
                H("Small-scale residual bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be locally bounded and measurable, h>0, A>=0, a<=b, L<=a, and b+2h<=U. If every increment of length between zero and 2h has L2 norm on [L,U] at most A*sqrt(h), then E-Z_h has L2 norm on [a,b] at most 2A*sqrt(h). Decompose the residual into E-A_h E and its forward average, and apply Cauchy-Schwarz and Fubini to the first residual."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-smoothing-bounds-with-residual"),
                DeclarationHandle.Create(Prefix + "dyadic_smoothing_bounds_with_residual"),
                H("Residual and block smoothing estimates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With explicit inner and working intervals, a uniform square-root increment bound on the working interval gives both the double-average residual estimate and the five simultaneous smoothing block and derivative estimates on the inner interval."))),
                DescribeRole.Theorem))));
}
