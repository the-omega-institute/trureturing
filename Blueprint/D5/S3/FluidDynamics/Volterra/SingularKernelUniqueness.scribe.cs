using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Volterra;

internal sealed class SingularKernelUniquenessDocument : IScribeDocumentDefinition
{
    private const string P = "D5/S3/FluidDynamics/Volterra/SingularKernelUniqueness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous nonnegative function bounded by its inverse-square-root Volterra integral vanishes on every compact time interval.",
        H("Singular Volterra uniqueness"), Blocks(
            Describe.Lean(DescribeId.Create("singular-volterra-uniqueness"),
                DeclarationHandle.Create(P + "eq_zero_of_le_sqrt_kernel_integral"),
                H("Vanishing under the singular integral comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let T and C be arbitrary nonnegative real numbers, and let d be a real-valued function on the real line that is continuous and nonnegative on the closed interval from zero to T. For every t in this interval, suppose that d at t is at most C times the Lebesgue interval integral, from zero to t, of d at s multiplied by the reciprocal of the square root of t minus s. Then d vanishes at every point of the closed interval, including both endpoints. The statement includes T equal to zero and C equal to zero. The reciprocal uses the total real inverse, whose value at zero is zero.")),
                    Paragraph(Text("The inverse-square-root kernel is integrable because its power exponent is greater than minus one. Reflection and continuity on the compact interval give integrability of each comparison integrand. Multiplying the kernel by an exponentially decreasing weight gives integral masses tending to zero by dominated convergence. Choose the weight so that C times its mass is less than one. The corresponding weighted function attains a nonnegative maximum on the compact interval; the integral comparison bounds this maximum by that same strict factor times itself. The maximum is therefore zero, and positivity of the exponential weight gives pointwise vanishing."))),
                DescribeRole.Theorem))));
}
