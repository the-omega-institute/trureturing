using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Variational;

internal sealed class JointReciprocalScalarCoordinateDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/trureturing2026pricegapconvexity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar integral coordinates, their smooth positive derivative and endpoint surjectivity support the exact joint reciprocal variational construction.",
        H("Joint Reciprocal Scalar Coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-polynomial"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.polynomial"),
                H("The scalar denominator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For real b and v, polynomial(b,v) is 2*b+3*(1-b)*v-6*v^2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-upperroot"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.upperRoot"),
                H("The positive denominator root"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For real b, upperRoot(b) is [3(1-b)+sqrt(9(1-b) squared+48b)]/12."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-lowerroot"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.lowerRoot"),
                H("The negative root magnitude"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For real b, lowerRoot(b) is [sqrt(9(1-b) squared+48b)-3(1-b)]/12."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate"),
                H("The original integral coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For real b and v, coordinate(b,v) is the oriented Lebesgue integral from 0 to v of (2b+6s)/polynomial(b,s)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate-radius"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.radius"),
                H("The left coordinate radius"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b, radius(b) is min(lowerRoot(b)/2,b/6). This is a neighborhood size for the scalar coordinate, not a hypothesis on a competitor."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate-coordinatedomain"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinateDomain"),
                H("The open coordinate domain"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b, coordinateDomain(b) is the open real interval (-radius(b),upperRoot(b))."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate-roots"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.roots"),
                H("The two denominator roots"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b with 0<b<=1, upperRoot(b)>0 and lowerRoot(b)>0, their difference is (1-b)/2 and their product is b/3. The explicit quadratic formulas prove these identities and positivity. The constructed profile consumes these facts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate-radius-pos"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.radius_pos"),
                H("A positive neighborhood radius"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b with 0<b<=1, radius(b)>0. The inverse construction and root uniqueness consume this neighborhood estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate-domain-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.domain_zero"),
                H("Zero lies inside the domain"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b with 0<b<=1, zero lies in coordinateDomain(b). This anchors the integral and the chosen inverse."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate-domain-positive"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.domain_positive"),
                H("Positive denominator and coordinate derivative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b with 0<b<=1 and every real v in coordinateDomain(b), polynomial(b,v)>0, 2*b+6*v>0 and v+lowerRoot(b)>0. Factoring the quadratic and using the left radius proves these inequalities. The coordinate derivative and the explicit profile consume them."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate-coordinate-hasderivat"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_hasDerivAt"),
                H("The coordinate derivative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b with 0<b<=1 and every real v in coordinateDomain(b), coordinate(b) has derivative (2*b+6*v)/polynomial(b,v) at v. Continuity on the oriented integration interval supplies the fundamental theorem of calculus. The smooth inverse construction consumes this exact derivative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate-coordinate-contdiff"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_contDiff"),
                H("Smoothness of the coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b with 0<b<=1 and every real v in coordinateDomain(b), coordinate(b) is infinitely continuously differentiable at v. The rational integrand is smooth on this open domain and is the coordinate derivative. Smooth local inversion consumes this result."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate-coordinate-strictmono"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_strictMono"),
                H("Strict monotonicity on the open domain"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b with 0<b<=1, coordinate(b) is strictly increasing on coordinateDomain(b), since its derivative is positive there. Root uniqueness and inverse uniqueness consume this result."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate-coordinate-surj-from"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalScalarCoordinate.coordinate_surj_from"),
                H("Every value above an attained coordinate is attained"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b with 0<b<=1, all real a and t with a in coordinateDomain(b) and coordinate(b,a)<=t admit a real v in coordinateDomain(b) with coordinate(b,v)=t. A logarithmic antiderivative diverges to positive infinity at upperRoot(b); the intermediate value theorem on the connected domain gives the result. The unique scalar root and actual inverse curve consume this endpoint surjectivity."))),
                DescribeRole.Theorem))));
}
