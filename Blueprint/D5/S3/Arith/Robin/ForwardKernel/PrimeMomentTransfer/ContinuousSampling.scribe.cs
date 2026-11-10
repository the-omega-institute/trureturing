using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class ContinuousSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous sampling transfers short interval moments from integer cells to real points.",
        H("Continuous sampling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("floor-shift-cases-add-nat"),
                DeclarationHandle.Create(Prefix + "floor_shift_cases_add_nat"),
                H("Floor shift cases add nat"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural n, 0<=x<1 and A>=0, floor(n+x+A) is either n+floor A or n+floor A+1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psi-endpoint-discrepancy"),
                DeclarationHandle.Create(Prefix + "psi_endpoint_discrepancy"),
                H("Psi endpoint discrepancy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If two ordered positive integer endpoints are each shifted by zero or one and the shifted endpoints are at most 4L with L>=1, the change in their Chebyshev psi difference is at most 2 log(4L) in absolute value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("s-eq-psi-shift"),
                DeclarationHandle.Create(Prefix + "S_eq_psi_shift"),
                H("S eq psi shift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For H>=0 and 0<=a<=b, the centered interval sum S(H,a,b,n) equals the difference of psi at n+floor(bH) and n+floor(aH), minus floor(bH)-floor(aH)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sampling-pointwise"),
                DeclarationHandle.Create(Prefix + "sampling_pointwise"),
                H("Pointwise cell discrepancy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an admissible interval inside a fixed window, with integer scale H and M H at most N, the centered Chebyshev increment at x differs from the centered integer-cell sum at floor x by at most 2 log(4N)+2. The two logarithmic terms account for the possible crossings at the left and right endpoints, while the additive constant accounts for the lattice centering count."))),
                DescribeRole.Theorem))));
}
