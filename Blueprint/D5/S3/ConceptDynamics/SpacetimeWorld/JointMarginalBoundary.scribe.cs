using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeWorld;

internal sealed class JointMarginalBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact dependent diagonal refutes the universal full-marginal claim.",
        H("Full Marginals Do Not Determine a Joint Domain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-diagonal"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/JointMarginalBoundary.diagonal_exact"),
                H("The joint domain contains exactly two diagonal worlds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Values are the integer subtype containing exactly one and two. Pair notation is connected by an explicit equivalence to dependent valuations on the union of two singleton name sets. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dependent-marginals"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/JointMarginalBoundary.diagonal_local_marginals"),
                H("Both dependent marginal images are full"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The diagonal has full coordinate images and full images in the actual local valuation types. Both crossed worlds are excluded, and the diagonal is a strict subset of the natural join. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-marginal-refutation"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/JointMarginalBoundary.diagonal_joint_refutation"),
                H("Distinct names and full marginals do not force the natural join"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed universal claim quantifies over disjoint name sets and nonempty domains with full local marginal images. The exact diagonal refutes that claim. The finite facts support this refutation; they are not separate positive instance deposits. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem))));
}
