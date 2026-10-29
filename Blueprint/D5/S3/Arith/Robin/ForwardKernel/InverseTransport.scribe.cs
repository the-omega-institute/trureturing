using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class InverseTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/InverseTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original forward Mellin adjoint admits an exact inverse-coordinate representation.",
        H("Inverse coordinates for the original Mellin adjoint"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adjoint-kernel-inverse-coordinates"),
                DeclarationHandle.Create(Prefix + "adjointKernel_inverse_coordinates"),
                H("Exact change of variables in the Mellin adjoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For x0>=4 and t>=max(8,B(x0)), let x(t,z) be the positive "
                        + "solution of t=x+z*x^(4/5), and let "
                        + "D=1+(4/5)*z*x^(-1/5). Then the actual adjoint q_s(t), "
                        + "defined by integrating x^(-s-1)*k(x,t) over x>=x0, "
                        + "equals the integral over z in [0,1] of "
                        + "x(t,z)^(-s-1/2)*integral(w(x+u*x^(4/5))/w(x),u=z..1)/D.")),
                    Paragraph(Text(
                        "The original support reduces the center integral to "
                        + "[x(t,1),t]. The exact derivative x_z=-x^(4/5)/D "
                        + "gives the change of variables. Integrating the price "
                        + "derivative w=-lambda' on the same window produces "
                        + "the inner weight ratio; x^(8/5)/x^(11/10)=sqrt(x) "
                        + "then gives the principal Mellin exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjoint-kernel-eq-inverse-adjoint"),
                DeclarationHandle.Create(Prefix + "adjointKernel_eq_inverseAdjoint"),
                H("Identification with the normalized triangular adjoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For x0>=4 and t>=max(8,B(x0)), the actual Mellin adjoint "
                    + "equals the normalized triangular adjoint used for the uniform "
                    + "remainder estimates. The equality follows from the exact "
                    + "inverse-coordinate integral and Fubini on the fixed triangle."))),
                DescribeRole.Theorem))));
}
