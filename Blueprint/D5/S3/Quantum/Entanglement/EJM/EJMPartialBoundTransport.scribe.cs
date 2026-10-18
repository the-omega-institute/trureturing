using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMPartialBoundTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMPartialBoundTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Faithful transport of actual partial EJM block events.",
        H("Local symmetry edges in the finite bound DAG"),
        Blocks(
            Paragraph(Text("Each symmetry is a pair consisting of one of the 12 recorded local coordinate actions and one of the producer's 24 lexicographic four-outcome permutations. The action first reads the old event at the permuted coordinate and then maps its outcome. Partial events use the same action, with unknown coordinates retained as unknown.")),
            Describe.Lean(DescribeId.Create("compatibility"),
                DeclarationHandle.Create(Prefix + "compatible_act"),
                H("Compatibility follows the exact event action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A full event agreeing with every known coordinate of a partial event still agrees after both receive the same coordinate and outcome action. This fact does not require a trusted canonicalization procedure."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-compatibility"),
                DeclarationHandle.Create(Prefix + "triangle_compatible"),
                H("The actual ten-coordinate transport"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every recorded local triangle symmetry transports compatibility between the actual ten-coordinate partial assignment and its full event."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-compatibility"),
                DeclarationHandle.Create(Prefix + "singleton_compatible"),
                H("The actual nine-coordinate transport"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every recorded local singleton symmetry transports compatibility between the actual nine-coordinate partial assignment and its full event."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-score"),
                DeclarationHandle.Create(Prefix + "triangle_score_invariant"),
                H("The actual centered triangle score is preserved"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact F1 centered score is unchanged by every recorded coordinate and outcome action. This uses the actual coefficient lookup and the head-contraction symmetry proved by EJMScoreSymmetry."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-score"),
                DeclarationHandle.Create(Prefix + "singleton_score_invariant"),
                H("The actual centered singleton score is preserved"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact F2 centered score is unchanged by every recorded local action. Compatibility and score invariance are the two earned premises consumed by the partial-bound DAG soundness theorem; they do not establish any numerical bound until the concrete rows and terminal scores are checked."))), DescribeRole.Theorem))));
}
