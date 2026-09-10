using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeWorld;

internal sealed class WorldProbabilityBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A probability measure on the full Cartesian domain has dependent coordinates.",
        H("Cartesian Domains Do Not Imply Independence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("measurable-coordinates"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.coordinates_measurable"),
                H("The coordinates are actual random variables"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The domain is the world subtype of the full Cartesian valuation set, equivalent to the product of the two value types. Both crossed worlds remain in the underlying domain. The value and world measurable spaces contain all subsets. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rectangle-masses"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.rectangle_masses"),
                H("A measurable rectangle violates factorization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual Mathlib measure is the sum of two Dirac measures with weight one half each, with its probability property proved. Both marginal values have mass one half. The rectangle where both coordinates equal one has mass one half, while the product of its marginal masses is one quarter. The second diagonal atom is also checked as measure-construction evidence. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("probability-refutation"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/SpacetimeWorld/WorldProbabilityBoundary.cartesian_probability_refutation"),
                H("Cartesian domain alone does not imply probabilistic independence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The refuted closed claim quantifies over every probability measure on this full Cartesian world domain. Its conclusion is the actual Mathlib IndepFun for the coordinate random variables. The proof uses the upstream measurable-rectangle identity, with no invented independence predicate. Formula projection is omitted; the resolving Lean declaration is the mathematical statement."))),
                DescribeRole.Theorem))));
}
