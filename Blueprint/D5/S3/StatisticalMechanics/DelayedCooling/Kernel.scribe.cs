using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.DelayedCooling;

internal sealed class KernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/DelayedCooling/Kernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite-sum quasi-exponential relaxation has a constant equilibrium past, "
            + "is continuous, and satisfies the delayed differential equation at every positive time.",
        H("The concrete delayed relaxation"),
        Blocks(
            Paragraph(Text(
                "Fix a positive real delay tau. Time and temperature are real. The relaxation E is "
                    + "the normalized response to a single quench from an equilibrated state. "
                    + "The finite sum below is the quasi-exponential in Eq. (6) of Santos, "
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
            Node("continuous_relaxation", "Continuity at every real time",
                "Each cutoff power is continuous. Local stabilization of the finite sum gives "
                    + "continuity on the whole real line, including zero and all step boundaries.",
                DescribeRole.Theorem),
            Node("hasDerivAt_relaxation", "The positive-time delay equation",
                "The derivative is minus E evaluated one delay earlier, at every strictly positive "
                    + "real time. The terms added at positive step boundaries have power at least "
                    + "two; their derivatives vanish at those boundaries. Reindexing the remaining "
                    + "derivative sum gives exactly the delayed relaxation. The extension is not "
                    + "assumed differentiable at zero. Positivity, decay, and comparison of real "
                    + "shifts require additional arguments.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("delay-kernel-" + declaration.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
