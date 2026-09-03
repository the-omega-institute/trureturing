using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class CrossWorldIndependenceSharpBoundsDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A polynomial cross-world independence restriction collapses a Boolean joint query to a sharp singleton and exposes a genuine nonconvex boundary.",
        H("Cross-World Independence Sharp Bounds"),
        Blocks(
            Paragraph(Text(
                "For a normalized two-by-two event coupling, independence is encoded by vanishing of the determinant. This is a polynomial equality in the four cell masses.")),
            Paragraph(Text(
                "Combining the determinant equation with normalization and the two marginal rows forces the true-true joint mass to equal the product of the marginals. The explicit product coupling proves attainment, so the identified range is a singleton.")),
            Paragraph(Text(
                "The unrestricted family of independent couplings is not closed under mixtures. Two degenerate independent laws have a normalized midpoint with nonzero determinant. This formally marks the point at which convex interpolation cannot be used without checking the actual feasible family.")),
            Describe.Lean(
                DescribeId.Create("independent-joint-event-eq-product"),
                DeclarationHandle.Create(Prefix + "independent_joint_event_eq_product"),
                H("The determinant restriction identifies the joint mass as the marginal product"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof eliminates the other three cells using the linear marginal equations and then verifies the remaining polynomial identity exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-joint-event-sharp-singleton-iff"),
                DeclarationHandle.Create(
                    Prefix + "independent_joint_event_sharp_singleton_iff"),
                H("The cross-world joint query has an exact singleton identified set"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Necessity follows from polynomial elimination. Sufficiency is witnessed by the explicit product coupling for probability-valued marginals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "independent-event-couplings-not-closed-under-midpoint"),
                DeclarationHandle.Create(
                    Prefix
                        + "independent_event_couplings_not_closed_under_midpoint"),
                H("Independent event couplings are globally nonconvex"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two normalized independent endpoint laws are constructed. Their normalized midpoint violates the determinant equation, providing a replayable obstruction to unqualified convex mixing."))),
                DescribeRole.Theorem))));
}
