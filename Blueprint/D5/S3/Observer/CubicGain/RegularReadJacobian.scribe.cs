using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class RegularReadJacobianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The derivative of the actual fifth and eighth reads",
        H("RegularReadJacobian"),
        Blocks(
        Paragraph(Text("Let x=(t,b), r=tb. The regular circuit gives the actual fifth and clock-eight M reads as P/D and M/D. Here M denotes the clock-eight numerator, rather than the seventh-M response used in the critical-locus construction. All derivatives below are derivatives in the independent source coordinates t,b of these same actual functions.")),
        Paragraph(Text("Differentiate the circuit polynomials and apply the quotient rule. The determinant numerator is (D Pt-P Dt)(D Mb-M Db)-(D Pb-P Db)(D Mt-M Dt), and the derivative determinant divides this by D^4. Multiplying its numerator by b^7 gives 45 D times a polynomial in r,b. This identity is an equality of polynomials, verified before using source inequalities.")),
        Paragraph(Text("On 9005/10000 <= r <= 9006/10000 and 12758/100000 <= b <= 12759/100000, write u=10000r-9005 and v=100000b-12758. Both variables lie in [0,1]. Express the remaining polynomial in these translated variables. Every nonconstant monomial lies in [0,1], so the constant coefficient plus the sum of positive remaining coefficients bounds it above. That exact rational upper bound is negative. The denominator D is nonzero on the same complete closed source strip. The actual derivative therefore has nonzero determinant.")),
        Paragraph(Text("This calculation uses neither a derivative of the degree-67 root polynomial nor an assumed determinant inequality. Equality of the circuit reads with chartRead holds in a neighborhood of every strict regular source, so the computed derivative is the Frechet derivative of chartRead itself. No gain-degree or nonzero-sample restriction is imposed.")),
        Describe.Lean(DescribeId.Create("cubic-gain-actual-jacobian-nonsingular"),
            DeclarationHandle.Create("D5/S3/Observer/CubicGain/RegularReadJacobian.actual_jacobian_nonsingular"),
            H("Actual read derivative is invertible"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real pair x=(t,b) satisfying all four displayed closed strip bounds, the determinant of fderiv R chartRead x is nonzero. There also exists a continuous linear equivalence e from R times R to itself whose underlying continuous linear map is a derivative of chartRead at x."))), DescribeRole.Theorem))));
}
