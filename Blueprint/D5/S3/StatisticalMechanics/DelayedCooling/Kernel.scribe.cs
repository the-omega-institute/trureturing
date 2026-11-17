using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.DelayedCooling;

internal sealed class KernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/DelayedCooling/Kernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite-sum quasi-exponential relaxation has a constant equilibrium past, "
            + "is continuous, satisfies its delay equation, and is positive with exponential decay "
            + "throughout the nonoscillatory delay range.",
        H("The concrete delayed relaxation"),
        Blocks(
            Paragraph(Text(
                "Fix a positive real delay tau. Time and temperature are real. The relaxation E is "
                    + "the normalized response to a single quench from an equilibrated state. "
                    + "The finite-sum construction is the quasi-exponential in Eq. (6) of Santos, "
                    + "The role of preparation protocols in the Mpemba effect under time-delayed "
                    + "Newton cooling, arXiv:2611.12328v1. These statements concern the scalar "
                    + "delay equation; they do not assert optimality of any preparation protocol.")),
            Node("relaxation", "The cutoff-power construction",
                "In the definition, each summand uses the minimum of n times tau minus t and zero, "
                    + "raised to the power n plus one and divided by its factorial. Only the first "
                    + "floor(t/tau) plus one summands are needed. Terms beyond the active interval "
                    + "vanish, so a single finite sum represents the function in a neighborhood "
                    + "of each time, even when the floor changes.", DescribeRole.Definition),
            Node("relaxation_eq_source_sum", "Agreement with the source finite sum",
                "At every nonnegative time, every included index n satisfies n times tau at most t. "
                    + "The cutoff therefore leaves each summand unchanged. The last term at an "
                    + "integer multiple of tau is zero, so the source endpoint convention agrees "
                    + "with either adjoining polynomial.", DescribeRole.Theorem),
            Node("relaxation_of_nonpos", "The equilibrated past",
                "For every time at most zero all cutoff terms vanish, and E equals one. "
                    + "This fixes the complete past history rather than only an initial value.",
                DescribeRole.Theorem),
            Node("relaxation_initial_segment", "The first polynomial segment",
                "From zero through one delay, including both endpoints, E is one minus time. "
                    + "At one delay the newly included quadratic term is zero.", DescribeRole.Theorem),
            Node("continuous_relaxation", "Continuity at every real time",
                "Each cutoff power is continuous. Local stabilization of the finite sum gives "
                    + "continuity on the whole real line, including zero and all step boundaries.",
                DescribeRole.Theorem),
            Node("hasDerivAt_relaxation", "The positive-time delay equation",
                "The derivative is minus E evaluated one delay earlier, at every strictly positive "
                    + "real time. The terms added at positive step boundaries have power at least "
                    + "two; their derivatives vanish at those boundaries. Reindexing the remaining "
                    + "derivative sum gives exactly the delayed relaxation. The constant past "
                    + "has left derivative zero at the initial quench, whereas the first polynomial "
                    + "segment has right derivative minus one. These two segment formulas show "
                    + "that the two-sided derivative does not exist at zero.", DescribeRole.Theorem),
            Node("relaxation_pos", "Positivity in the nonoscillatory delay range",
                "For every positive delay at most exp(-1), E is strictly positive at every real "
                    + "time. Multiply E by exp(kappa times t), choosing kappa equal to exp(1). "
                    + "Its rate at zero is positive. If a first nonpositive rate existed, the "
                    + "weighted response would increase strictly up to that time, including its "
                    + "negative-time exponential history. The delayed differential equation and "
                    + "exp(kappa times tau) at most kappa would make the rate strictly positive "
                    + "there as well, a contradiction.", DescribeRole.Theorem),
            Node("strictAntiOn_relaxation", "Strict cooling after the quench",
                "Positivity of the delayed value makes the derivative strictly negative at all "
                    + "positive times. Continuity joins this strict decrease to the value at zero.",
                DescribeRole.Theorem),
            Node("antitone_relaxation", "Monotonicity with the equilibrium extension",
                "The constant past and the decreasing nonnegative-time response together give "
                    + "a nonincreasing function on the whole real line.", DescribeRole.Theorem),
            Node("relaxation_le_exp_neg", "A uniform exponential bound",
                "At nonnegative times, E is at most exp(-t). The derivative of exp(t) times E "
                    + "is nonpositive because E evaluated one delay earlier is at least its "
                    + "current value. At zero the product equals one.", DescribeRole.Theorem),
            Node("tendsto_relaxation_atTop", "Decay to equilibrium",
                "The positive response is bounded above by exp(-t), so it tends to zero as "
                    + "time tends to positive infinity. These conclusions include the critical "
                    + "endpoint tau equal to exp(-1); no asymptotic expansion is used.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("delay-kernel-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
