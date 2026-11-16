using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingEndpointVarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cumulative and local variance bounds control increments between two increasing endpoints.",
        H("Two moving endpoints"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-endpoint-integral-average-pow-le"),
                DeclarationHandle.Create(Prefix + "two_endpoint_integral_average_pow_le"),
                H("Shared even-power endpoint average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let e be a positive even integer and E be locally bounded and Borel measurable. Suppose p and q are continuous on [l,r], their derivatives within the interval are at least m>0, and their images lie in [A,B]. Choose a<=b and c<=d so that [a-delta(x),b-delta(x)] lies in [c,d], where delta=q-p. If the integral of D_v(y)^e over [A,B] is at most an integrable F(v) on each averaging interval, then (b-a) times the integral of (E(q)-E(p))^e is at most 2^(e-1)/m times the sum of the integrals of F over [a,b] and [c,d]. The common-endpoint identity, the even-power sum inequality, translation, Fubini, and change of variables give this bound. Exponents two and four yield the square and fourth-moment endpoint estimates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-endpoint-increment-square-le"),
                DeclarationHandle.Create(Prefix + "two_endpoint_increment_square_le"),
                H("The two-endpoint square estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be Borel measurable and locally bounded. Let p and q be continuous on [l,r], l<=r, with derivatives within that interval bounded below by m>0. Assume their images lie in [1,Y], 0<=q(x)-p(x)<=C0*R, R>0, C0>=0, and K>=0. If V(Y,u)<=K for every R<=u<=(C0+2)*R, then the integral of (E(q(x))-E(p(x)))^2 over [l,r] is at most 2*(C0+2)*K/m.")),
                    Paragraph(Text(
                        "Put delta=q(x)-p(x). Average the identity E(q(x))-E(p(x))=D_v(p(x))-D_(v-delta)(q(x)) over (C0+1)*R<=v<=(C0+2)*R, and use (A-B)^2<=2*A^2+2*B^2. Translation enlarges the second length interval to [R,(C0+2)*R]. Fubini and change of variables through p and q bound the two averaged terms by R*K/m and (C0+1)*R*K/m. Division by R gives the claim. Only differentiability and a positive lower derivative bound are needed; derivative continuity is unnecessary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-two-endpoint-increment-square-le"),
                DeclarationHandle.Create(Prefix + "local_two_endpoint_increment_square_le"),
                H("The local signed-endpoint estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be Borel measurable and locally bounded. Let l<=r, A<=B, R>0, C>=0, and m>0. Suppose p and q are continuous on [l,r], have derivatives within that interval bounded below by m, take values in [A,B], and satisfy |q(x)-p(x)|<=R. If the integral of D_v(y)^2 over [A,B] is at most C*v for every R<=v<=4*R, then the integral of (E(q(x))-E(p(x)))^2 over [l,r] is at most 20*C*R/m.")),
                    Paragraph(Text(
                        "For the signed difference delta=q(x)-p(x), the increments D_v(p(x)) and D_(v-delta)(q(x)) have the same endpoint. Average their difference over [2*R,3*R], square with (A-B)^2<=2*A^2+2*B^2, and translate the second length interval into [R,4*R]. The shared averaging and change-of-variables estimate integrates the length-dependent bound C*v: the two contributions are (5/2)*C*R^2/m and (15/2)*C*R^2/m. Multiplication by two and division by R give the result. The image interval [A,B] is retained throughout; the ordering of p and q may change, and derivative continuity is unnecessary."))),
                DescribeRole.Theorem))));
}
