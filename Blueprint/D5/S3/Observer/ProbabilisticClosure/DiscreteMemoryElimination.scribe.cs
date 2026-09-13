using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class DiscreteMemoryEliminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separate an actual hidden initial condition from feedback through hidden dynamics.",
        H("Discrete Memory and Future-Silent Directions"),
        Blocks(
            Paragraph(Text(
                "The source evolves an actual pair (y,h) by (Ay+Bh, Cy+Dh). "
                + "It does not reset h, choose a representative on each step, or assume "
                + "that an alternative unrealized state is exerting a physical force.")),
            Describe.Lean(
                DescribeId.Create("exact-discrete-memory-elimination"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/DiscreteMemoryElimination.exact_memory_equation"),
                H("Eliminating the hidden recurrence gives an exact all-time memory equation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction solves the hidden recurrence as D^n h0 plus the convolution "
                    + "of past visible states with D^k C. Substitution into the visible update "
                    + "gives Ay_n, the initial-hidden term B D^n h0, and the history sum with "
                    + "kernel B D^k C. Empty sums and time zero are included. No finite-dimensional, "
                    + "stochastic, or reversibility hypothesis is needed for this algebraic identity. "
                    + "Continuous-time Mori-Zwanzig identities are context, not claimed as this theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-coupled-silence-eventual-kernel"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/DiscreteMemoryElimination.zero_visible_iff_eventual_kernel"),
                H("The coupled system ignores exactly the existing eventual kernel"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With zero initial visible perturbation, all future visible components vanish "
                    + "exactly when every B D^n h vanishes. The denominator is the repository's "
                    + "existing eventualKernel, not a second memory definition. Each direction "
                    + "of the equivalence uses the actual coupled recurrence: a silent visible "
                    + "trajectory leaves pure D evolution, and an eventual-kernel hidden input "
                    + "never excites the visible component. Initial-state uncertainty is not "
                    + "identified with the history-feedback kernel, which also depends on C."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Observer/LinearMemory/ZeroMemoryCriterion"))]));
}
