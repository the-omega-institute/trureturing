using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Quandles;

internal sealed class PresentedColoringSpaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generator colorings satisfying a presentation are exactly homomorphisms from its presented quandle.",
        H("Presented Coloring Space"),
        Blocks(
            Describe.Lean(DescribeId.Create("presented-coloring-space-rel-coloring"),
                DeclarationHandle.Create("D5/S0/Certificates/Quandles/PresentedColoringSpace.RelColoring"),
                H("Presented coloring assignments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A coloring assignment is a generator map whose evaluations agree on every presented relation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("presented-coloring-space-equivalence"),
                DeclarationHandle.Create("D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv"),
                H("Colorings and homomorphisms are equivalent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The universal property extends every satisfying generator assignment uniquely to a quandle homomorphism, and restriction to generators is its inverse."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("presented-coloring-space-equivalence-apply"),
                DeclarationHandle.Create("D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv_apply"),
                H("Coloring equivalence evaluation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluating the equivalence sends a satisfying assignment to the homomorphism supplied by the presentation lift."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("presented-coloring-space-equivalence-symm-apply"),
                DeclarationHandle.Create("D5/S0/Certificates/Quandles/PresentedColoringSpace.satisfyingAssignmentsEquiv_symm_apply_of"),
                H("Restriction recovers a coloring assignment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Restricting a homomorphism to the presented generators recovers its generator assignment."))),
                DescribeRole.Theorem))));
}
