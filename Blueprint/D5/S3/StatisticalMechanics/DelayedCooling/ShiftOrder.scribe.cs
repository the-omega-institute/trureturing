using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.DelayedCooling;

internal sealed class ShiftOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete delayed cooling response has an increasing hazard, strictly decreasing "
            + "positive-shift ratios, and a weak real-shift kernel order.",
        H("Real-shift order of the delayed cooling kernel"),
        Blocks(
            Paragraph(Text(
                "Fix a positive real delay at most exp(-1). The function E is the finite-sum "
                    + "relaxation with constant equilibrium history. Its positivity makes every "
                    + "ratio below well defined. All times, ages and shifts are real.")),
            Node("hazard", "The logarithmic cooling rate",
                "The hazard is E evaluated one delay earlier divided by E at the current time. "
                    + "At positive times it is minus the logarithmic derivative of E. On the "
                    + "initial interval it equals the reciprocal of one minus time.", DescribeRole.Definition),
            Node("strictMonoOn_hazard", "Strictly increasing hazard",
                "Before one delay, the hazard derivative is its square. After one delay, its "
                    + "derivative is the hazard times the difference from its value one delay "
                    + "earlier. These two derivative formulas need not agree at one delay. "
                    + "The initial segment is strictly increasing. A first nonpositive late "
                    + "rate would contradict strict increase up to that time, since the "
                    + "delayed value is strictly smaller. Continuity joins the two intervals.",
                DescribeRole.Theorem),
            Node("strictAntiOn_relaxation_ratio", "Strict order for positive shifts",
                "For every positive shift w, the ratio E(t+w) divided by E(t) decreases "
                    + "strictly on nonnegative time. Its derivative is the positive ratio "
                    + "times hazard(t) minus hazard(t+w), which is strictly negative.",
                DescribeRole.Theorem),
            Node("responseKernel", "The source history kernel",
                "The kernel at age s is E(s-tau). In the bath-history integral the age is "
                    + "nonnegative; the same expression also defines its equilibrium extension. "
                    + "On ages from zero through one delay the kernel equals one.",
                DescribeRole.Definition),
            Node("kernel_shift_order", "Weak comparison for arbitrary real ages",
                "For a at most b and a nonnegative time shift t, the shifted value at b times "
                    + "the unshifted value at a is at most the shifted value at a times the "
                    + "unshifted value at b. The assertion holds even for the real equilibrium "
                    + "extension of the ages. On nonnegative base time the ratio order follows "
                    + "from the increasing hazard. On nonpositive base time its denominator is "
                    + "one and its numerator is nonincreasing. Continuity joins the two parts. "
                    + "The comparison is weak because the kernel has an initial plateau. "
                    + "It supplies a kernel inequality for history comparisons, without "
                    + "asserting a history convolution, an attained extremum, or an optimal "
                    + "two-reservoir preparation.", DescribeRole.Theorem),
            Node("kernel_tail_mass", "Exact mass of every translated tail",
                "For any real lower age L with t plus L nonnegative, the kernel at t plus age "
                    + "is integrable over ages greater than L, and its integral is E(t+L). "
                    + "Apply the fundamental theorem of calculus to E(t+age), whose derivative "
                    + "is the negative kernel. Positivity gives the derivative sign and hence "
                    + "its integrability; the exponential bound gives the zero endpoint at "
                    + "infinity. The case t and L both zero normalizes the source history "
                    + "kernel to unit mass.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("delay-shift-" + declaration.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
