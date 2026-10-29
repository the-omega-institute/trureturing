using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class RemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/Remainder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse coordinates preserve the original forward window and its quantitative derivative scale.",
        H("Inverse coordinates for the forward Robin kernel"),
        Blocks(
            Paragraph(Text(
                "Write H(x)=x^(4/5). For t>0 and z>=0, x(t,z) is the unique "
                + "positive solution of t=x+z*H(x). A globally increasing extension "
                + "x+z*H(max(x,0)) defines the inverse without changing this positive solution.")),
            Describe.Lean(
                DescribeId.Create("forward-coordinate-scale"),
                DeclarationHandle.Create(Prefix + "coordinate_scale_bounds"),
                H("The inverse coordinate stays within the original scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For t>=1 and 0<=z<=1, 0<x(t,z)<=t and "
                    + "0<=1-x(t,z)/t<=t^(-1/5). For t>=2 the additional "
                    + "bound x(t,z)>=t/2 holds."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-coordinate-fraction-derivative"),
                DeclarationHandle.Create(Prefix + "coordinate_fraction_derivative_bound"),
                H("Differentiating the relative coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Put D=1+(4/5)*z*x(t,z)^(-1/5). The exact time derivative "
                    + "is x_t=1/D. After dividing by t, the constant main term "
                    + "cancels: (x/t)_t=z*H(x)/(5*t^2*D). Thus "
                    + "0<=(x/t)_t<=t^(-6/5)/5 for t>=1 and 0<=z<=1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-normalized-power"),
                DeclarationHandle.Create(Prefix + "normalizedPower_bounds"),
                H("The relative complex Mellin power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For p=-s-1/2 define P(t,z,s)=exp(p*log(x(t,z)/t)). "
                    + "For t>=2 and 0<=z<=1, its norm is at most exp(2*|p|), "
                    + "and |P-1|<=2*|p|*exp(2*|p|)*t^(-1/5). "
                    + "The logarithmic estimate |log(x/t)|<=2*t^(-1/5) "
                    + "retains the exact moving coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-normalized-power-derivative"),
                DeclarationHandle.Create(Prefix + "normalizedPower_derivative_bound"),
                H("The time derivative of the relative power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The time derivative satisfies "
                    + "|P_t|<=2*|p|*exp(2*|p|)*t^(-6/5). "
                    + "This differentiates the relative coordinate after "
                    + "extracting the principal power t^p."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-jacobian-scale"),
                DeclarationHandle.Create(Prefix + "jacobianFactor_bounds"),
                H("The inverse Jacobian"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For J=1/D, 0<J<=1 and |J-1|<=2*t^(-1/5) "
                    + "throughout t>=2 and 0<=z<=1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-jacobian-derivative"),
                DeclarationHandle.Create(Prefix + "jacobianFactor_derivative_bound"),
                H("The Jacobian derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact derivative is J_t=(4/25)*z*x^(-6/5)*J^3. "
                    + "The bound x>=t/2 gives |J_t|<=t^(-6/5)."))),
                DescribeRole.Theorem))));
}
