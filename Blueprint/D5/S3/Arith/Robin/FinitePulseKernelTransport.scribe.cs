using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class FinitePulseKernelTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/FinitePulseKernelTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed bounds from exclusion and a local envelope",
        H("FinitePulseKernelTransport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kernel-atom-accounting"),
                DeclarationHandle.Create(Prefix + "kernel_atom_accounting"),
                H("Exact accounting before exclusion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a price curve, a<y, 1<t<=B and any D, actualKernel(y)-referenceKernel(a) equals the closed-pulse indicator at t times (price(t)-price(B))/D, minus D inverse times the interval integral of the closed-pulse weight over [t,B].")),
                    Paragraph(Text("The equality includes a=t, y=t, the terminal endpoint B, and atoms beyond B. The difference between open and closed integration cutoffs is a single null point, whereas the initial correction retains the literal closed endpoints. No initial actual atom is silently removed."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-pulse-accounting"),
                DeclarationHandle.Create(Prefix + "finite_pulse_accounting"),
                H("Finite closed-pulse transport identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For an arbitrary finite index set I with a(i)<y(i), sum h(i)*(actualKernel(y(i))-referenceKernel(a(i))) equals delta(t)*(price(t)-price(B))/D minus the integral of delta(x)*weight(x) over [t,B], divided by D. Here delta(x)=sum h(i)*1_[a(i),y(i)](x).")),
                    Paragraph(Text("Finite summation and integrability of the cutoff weight prove the identity. The weights h need not be nonnegative for this identity. It is consumed by the signed bounds."))
                ), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-pulse-bounds"),
                DeclarationHandle.Create(Prefix + "finite_pulse_bounds"),
                H("Signed bounds from exclusion and a local envelope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume additionally h(i)>=0, D>0, t outside every closed pulse, and delta(x)<=L on [t,B]. Then the finite response lies between -(price(t)-price(B))*L/D and zero.")),
                    Paragraph(Text("Exclusion removes the initial correction only after the exact accounting identity. The nonnegative weighted integral supplies the sign and the local envelope supplies the lower bound. There is no assumption that an integrated selected kernel is globally nonincreasing. The original specialization supplies its envelope, denominator and every prime exclusion."))
                ), DescribeRole.Theorem))));
}
