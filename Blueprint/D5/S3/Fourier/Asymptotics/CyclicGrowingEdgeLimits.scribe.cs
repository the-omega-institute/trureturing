using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicGrowingEdgeLimitsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical-scale coefficients and signed boundary values for growing cyclic windows.",
        H("Boundary limits in the growing cyclic moment fit"),
        Blocks(
            Paragraph(Text(
                "Fix a nonempty finite set S of real rear offsets and let n tend to infinity. " +
                "Assume n⁵h(n)² tends to a finite real K. Put m=n(n+1)/5 and prescribe the " +
                "three scaled moments (1−mh²,m/n²,3n³mh²/4). The coefficient vector a(n) is the " +
                "inverse of the coupled moment matrix applied to this target.")),
            Describe.Lean(DescribeId.Create("critical-coefficient-limit"),
                DeclarationHandle.Create(Owner + ".coefficient_tendsto"),
                H("The three fitted coefficients converge"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The moment target converges to (1,1/5,3K/20). Inverting the limiting " +
                    "coupled matrix gives (3/4,−3/4,B), where " +
                    "B=(3K/20+(3/4)∑_{r∈S}r²)/|S|."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("refined-front-coefficients"),
                DeclarationHandle.Create(Owner + ".refined_coefficients"),
                H("The front coefficient error vanishes after multiplication by n"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact lattice reference has radius parameter t=n(n+1)−1/2 and " +
                    "normalizer Z. Its first two coefficients are nt/Z and −n³/Z. " +
                    "After multiplying by n, the top two rows of the coupled matrix minus " +
                    "the lattice Gram rows with a zero third column converge to zero. " +
                    "The target mass perturbation also vanishes under this scaling. " +
                    "Holding the rear coefficient fixed, inversion of the first two rows " +
                    "transfers the scaled residual bound to the two coefficient errors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("front-edge-limit"),
                DeclarationHandle.Create(Owner + ".scaled_boundary_value"),
                H("Signed value at the growing front boundary"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At x=(n+δ)/n the finite signed weight is the dot product of the coefficient " +
                    "row with a(n). Multiplying by n² gives the limit (3/4)(1−2δ). " +
                    "This gives strictly positive and strictly negative limiting values at δ=0 " +
                    "and δ=1 respectively. The scaled site-feature remainders vanish, including " +
                    "at a fixed offset beyond the fitted window."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rear-edge-limit"),
                DeclarationHandle.Create(Owner + ".scaled_rear_value"),
                H("Signed value at a fixed rear offset"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every fixed real rear offset r the signed value multiplied by n³ " +
                    "converges to B−3r²/4. Strict limiting inequalities settle the eventual sign. " +
                    "Zero limiting values require finer estimates. These readouts concern a signed " +
                    "moment fit on the stated windows. Certification of the full cyclic optimizer " +
                    "also requires the cyclic grid correspondence and complement signs."))),
                DescribeRole.Theorem))));
}
