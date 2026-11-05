using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class PeriodicSkeletonRescalingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonRescaling.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual periodic-skeleton density under rescaling.",
        H("Actual periodic-skeleton density under rescaling"),
        Blocks(
            Describe.Lean(DescribeId.Create("density-rescaling"), DeclarationHandle.Create(Owner + "density_eq_of_dvd_of_periodic_coordinates_eq"),
                H("Compatible rescaling preserves actual density"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let q and h be positive natural periods of a binary two-sided point, with q dividing h. If the actual q-periodic-coordinate condition agrees with the actual h-periodic-coordinate condition at every signed site, their normalized periodic-skeleton densities are equal. The proof splits a complete h-interval into equally many q-intervals by finProdFinEquiv and counts the same actual periodic coordinates. It retains the universal quantifier over signed integer multiples, and neither assumes nor asserts essentiality of either period. Public escape registrations remain unfinished under https://github.com/the-omega-institute/trureturing/issues/24726; compiled density rescaling is not declared_validated registration evidence."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity")) ]));
}
