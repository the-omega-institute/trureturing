using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingEndpointVarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingEndpointVariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Comparable cumulative variances control increments between two increasing endpoints.",
        H("Two moving endpoints"),
        Blocks(
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
                DescribeRole.Theorem))));
}
