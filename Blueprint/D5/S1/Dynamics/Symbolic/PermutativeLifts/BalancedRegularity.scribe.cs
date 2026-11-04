using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class BalancedRegularityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual regular balanced Toeplitz generator.",
        H("Actual regular balanced Toeplitz generator"),
        Blocks(
            Describe.Lean(DescribeId.Create("height-divisibility"), DeclarationHandle.Create(Owner + "height_dvd_succ"),
                H("Balanced heights form a divisibility scale"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each balanced height divides its successor, by the literal multiplier 3 times the next factorial. This supplies the original skeleton scale for essential-period extraction; the heights themselves are not asserted essential."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonempty-shifted-skeletons"), DeclarationHandle.Create(Owner + "aligned_shifted_sites_nonempty"),
                H("Shifted actual skeletons are nonempty"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every height h(n+1), the same actual aligned point has a nonempty periodic-coordinate skeleton. Its actual density is bounded below by 1-(1/3)^(n+1), which is strictly positive. This explicitly avoids the empty initial h(0)-skeleton of the nonconstant point."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-coordinate-coverage"), DeclarationHandle.Create(Owner + "aligned_shifted_sites_cover"),
                H("Actual shifted heights cover every signed coordinate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each coordinate period p supplied by the actual compact-limit Toeplitz construction divides (p+1) factorial and hence the later balanced height h(p+1). Therefore the concrete shifted height scale covers every signed coordinate, without assuming the scale coverage needed by the generic extraction theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regular-essential-structure"), DeclarationHandle.Create(Owner + "aligned_has_regular_period_structure"),
                H("A genuine essential period structure has density one"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same actual aligned compact-limit point there exists a source period structure with strictly increasing positive essential periods, divisibility into each successor and coverage of every signed coordinate, whose actual normalized skeleton densities converge to one. Every extracted essential skeleton preserves its actual letters and holes. Compatible density rescaling transfers the balanced-height limit to the cofinal strict subsequence. Nonemptiness, coverage and aperiodicity needed by extraction are all discharged for this concrete point."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regular-toeplitz-generator"), DeclarationHandle.Create(Owner + "exists_balanced_regular_toeplitz_generator"),
                H("One actual regular Toeplitz point generates the subshift"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One binary point in the actual balanced subshift has periodic coordinates for all signed multiples, has no positive global shift period, has orbit closure exactly the compact minimal balanced subshift, and admits an actual source essential period structure along which actual normalized skeleton densities converge to one. All clauses concern the same point. This supplies regular Toeplitzness in the source period-structure sense; strict ergodicity and lift splitting remain separate statements. Public escape registrations remain unfinished under https://github.com/the-omega-institute/trureturing/issues/24726, so the mathematical proof and scoped report do not constitute declared_validated registration evidence."))), DescribeRole.Theorem)),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/EssentialPeriodStructure")),
              DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonRescaling")) ]));
}
