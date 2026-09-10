using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeWorld;

internal sealed class NaturalJoinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural join is the largest compatible domain and retains extra constraints.",
        H("Natural Join of Dependent Domains"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("join-maximality"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.naturalJoin_greatest"),
                H("Both local restrictions determine the largest domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Valuations live on the union of the name sets. Both restrictions use Mathlib dependent restriction maps into the two local valuation types. Every domain satisfying both membership conditions is a subset of the join. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("extra-constraints"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.constrainedJoin_greatest"),
                H("Additional constraints remain part of the joint model"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Intersecting the natural join with an extra set is the largest domain satisfying all three conditions. Disjoint name sets supply no theorem that would remove the extra set. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realize-subdomain"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/NaturalJoin.constrainedJoin_realizes"),
                H("Any admissible subdomain is retained exactly"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choosing an admissible subdomain as the extra constraint returns precisely that subdomain. The diagonal witness uses this representation. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem))));
}
