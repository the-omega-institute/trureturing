using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class AveragedBoxEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite separated family of complex jumps has uniform energy in every dyadic band of box widths.",
        H("Averaged box energy of separated jumps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("separated-closed-box-sum"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/AveragedBoxEnergy.boxSum"),
                H("The exact box sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite index type, real nodes x_i, complex coefficients c_i and real s,u, boxSum is the finite sum of c_i times the indicator of [x_i,x_i+s]. No ordering or nonzero-total-mass condition is imposed. The internal half-open boxes [x_i,x_i+s) give exactly F(u)-F(u-s) for s>=0, where F(u)=sum_{x_i<=u} c_i. The full finite-family almost-everywhere comparison proves that the closed and half-open energies have the same integral: their difference is supported on finitely many upper endpoints."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-averaged-separated-box-energy"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/AveragedBoxEnergy.averaged_box_energy_lower_bound"),
                H("Every separated jump contributes at every band"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every finite index type, every real node family with |x_i-x_j|>=g for i!=j, every complex coefficient family, and every g>0 and a>=g, the integral over s in [a,2a] of the whole-line squared modulus of boxSum is at least (a*g/16)*sum_i |c_i|^2. Empty and singleton families are included. There is no restriction on total span, equal spacing, or cancellation among coefficients.")),
                    Paragraph(Text("Write v=u-s. Lebesgue measure is preserved by the change from (u,v) to (s,u)=(u-v,u). Keep |F(u)-F(v)|^2 intact on the strip a<=u-v<=2a. The prefix itself is not asserted integrable: when sum c_i is nonzero it approaches that nonzero constant at plus infinity. The strip-restricted difference is measurable, uniformly bounded and supported in a bounded rectangle; this supplies the actual Bochner integrability needed for Fubini and monotonicity.")),
                    Paragraph(Text("At node i take U_i=[x_i-g/4,x_i+g/4) and V_i=[x_i-7a/4,x_i-5a/4]. Since a>=g, every U_i times V_i lies in the strip. Separation makes the U_i, and hence these rectangles, pairwise disjoint. The two halves of U_i each have length g/4 and have prefix values differing by exactly c_i; all other nodes stay on the same side. For fixed v the two squared values are |A|^2 and |A+c_i|^2. Their sum is at least |c_i|^2/2. Thus the U_i integral is at least (g/8)|c_i|^2; multiplying by |V_i|=a/2 and summing disjoint rectangles yields the stated constant.")),
                    Paragraph(Text("The estimate captures all separated jumps uniformly despite arbitrary other prefix values. It uses the same nodes and coefficient family throughout the strip, without a cancellation restriction. No academic priority or optimality of the constant is claimed.")),
                    Paragraph(Text("The direct arithmetic application is ActualKernelDyadicCoercivity. The positive density lower bound D2(s)>=1/(8a) on each contained dyadic band turns this average into g/128 times the coefficient square sum. Summing J bands preserves the same nodes and complex coefficient family and gives a logarithmically increasing local conditioning margin. This statement supplies neither global far-block control nor the Riemann hypothesis."))),
                DescribeRole.Theorem))));
}
