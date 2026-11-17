using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class StripAsymptoticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/StripAsymptotic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial bounds for the forward adjoint on a vertical strip.",
        H("Strip estimates for the forward adjoint"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-coordinate-one-fifth-power"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/Asymptotic.coordinate_power_one"),
                H("The inverse coordinate scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For t>=2 and z in [0,1], the inverse coordinate satisfies "
                    + "x(t,z)^(-1/5)<=2*t^(-1/5)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-unit-square-volume"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/Asymptotic.unitSquare_volume"),
                H("The unit square has area one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real Lebesgue measure of [0,1] times [0,1] is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-triangle-integral"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/Asymptotic.triangle_integral"),
                H("The triangular principal coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral over the unit square of the indicator of z<=u, "
                    + "with constant complex value one, is one half."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-normalized-power-strip"),
                DeclarationHandle.Create(Prefix + "normalizedPower_strip_bounds"),
                H("Uniform relative powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is a positive absolute constant C such that, for "
                    + "-1/5<=Re(s)<=1, t>=2 and 0<=z<=1, the relative power "
                    + "P=exp((-s-1/2)*log(x(t,z)/t)) has norm at most C, "
                    + "its difference from one has norm at most "
                    + "C*(1+|s|)*t^(-1/5), and its time derivative has norm "
                    + "at most C*(1+|s|)*t^(-6/5). The logarithm is real, "
                    + "so the exponential norm depends only on Re(s). "
                    + "The mean value inequality along the exponential segment "
                    + "bounds its difference from one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-adjoint-remainder-strip-c1"),
                DeclarationHandle.Create(Prefix + "adjointRemainder_strip_C1_bounds"),
                H("Polynomial remainder bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is a positive absolute constant C such that, for "
                    + "-1/5<=Re(s)<=1 and t>8, the exact adjoint remainder "
                    + "r_s(t) satisfies |r_s(t)|<=C*(1+|s|)*t^(-Re(s)-7/10) "
                    + "and |r_s'(t)|<=C*(1+|s|)^2*t^(-Re(s)-17/10). "
                    + "The relative power estimates combine with the weight "
                    + "ratio and inverse Jacobian bounds on the fixed triangle "
                    + "0<=z<=u<=1. Its area is one half. Differentiating the "
                    + "principal Mellin power supplies the second parameter factor."))),
                DescribeRole.Theorem))));
}
