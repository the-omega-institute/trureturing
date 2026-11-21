using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMPeriodSourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Periods and covariance of the original four-point kernel",
        H("Euler periods in the physical charts"),
        Blocks(
            Paragraph(Text("Write P for the original Euler slit period and τ(r) for i P(1−r)/P(r). "
                + "At the real cross-ratio z the native arguments are rA = 1−1/z, rB = z and rD = 1/z.")),
            Describe.Lean(DescribeId.Create("original-fourm-period-correction"),
                DeclarationHandle.Create(Prefix + "periodCorrection"),
                H("Period correction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a complex function F and complex r, "
                    + "the correction C_F(r) is r(1−r) deriv(F)(r)/F(r)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-period-pfaff-correction"),
                DeclarationHandle.Create(Prefix + "pfaff_correction"),
                H("Pfaff transport of the correction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For r in the Euler slit domain, differentiating the principal Pfaff identity gives "
                    + "C_P(r/(r−1)) = C_P(r)/(1−r) − r/[2(1−r)]."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-period-b-correction"),
                DeclarationHandle.Create(Prefix + "chartB_pfaff_correction"),
                H("Correction at the Pfaff image of A"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real z > 0, the Pfaff image of rA is 1−z. "
                    + "The transported correction is C_P(1−z) = z C_P(rA) + (1−z)/2."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-period-d-lip"),
                DeclarationHandle.Create(Prefix + "dLip"),
                H("The D lip paired with A"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the Boolean upperA, the D lip is the open half-plane Im t < 0 "
                    + "when upperA is true and Im t > 0 when upperA is false."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-period-d-germ"),
                DeclarationHandle.Create(Prefix + "dPeriod"),
                H("The D period germ"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Boolean upperA and complex t, set s = 1 when upperA is true "
                    + "and s = −1 when it is false. Then dPeriod(upperA,t) = (τ(1−1/t)+s) P(1−t)/i."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-period-d-agreement"),
                DeclarationHandle.Create(Prefix + "dPeriod_eq_slit"),
                H("Agreement with the Euler period on the open lip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every complex point of the selected D lip, dPeriod(upperA,t) = P(t). "
                    + "The complementary ratio at 1−t differs from the ratio at its Pfaff image 1−1/t by s."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-period-d-boundary"),
                DeclarationHandle.Create(Prefix + "dPeriod_boundary"),
                H("One-sided period and derivative limits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either choice of upperA and every real t > 1, as u tends to t within "
                    + "the selected D lip, P(u) tends to dPeriod(upperA,t) and deriv(P)(u) tends to "
                    + "the complex derivative of dPeriod(upperA,·) at t."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-period-chart-correction"),
                DeclarationHandle.Create(Prefix + "chartCorrection"),
                H("Corrections in native chart arguments"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Boolean upperA, a chart c and complex z, chartCorrection applies "
                    + "the period correction at parameter(c,z). It uses P in A and B and dPeriod(upperA,·) in D."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-period-b-pfaff"),
                DeclarationHandle.Create(Prefix + "chartB_pfaff_period"),
                H("Pfaff period with the chosen A root"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real z > 0, P(1−z) = periodRoot(A,z) P(rA), "
                    + "where periodRoot(A,z) = 1/√z."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-period-covariance"),
                DeclarationHandle.Create(Prefix + "covariance_discrepancies"),
                H("The two corrected spatial covariance differences"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let upperA select a lip, let z be real with 0 < z < 1, and take complex "
                        + "x and X with zx−1, zX−1 and x−X nonzero. For each chart, subtract its chartCorrection "
                        + "from spatialKernel at first argument 1−r, using the native argument r of that chart. "
                        + "Evaluate the resulting kernels K_A, K_B and K_D at (x,X), at the two pullB images "
                        + "and at the two pullD images, respectively.")),
                    Paragraph(Text("Then (−i√z)² K_A − K_B = 1/[π P(1−z) P(z)] and "
                        + "i² K_A − K_D = 1/[π P(rA) dPeriod(upperA,rD)]."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-period-d-root"),
                DeclarationHandle.Create(Prefix + "chartD_root_boundary"),
                H("The principal root on the D boundary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real 0 < z < 1, let u tend to rD within the selected D lip. "
                    + "The principal complex power (1−u)^(1/2) tends to i√(1−z)/√z on the lower lip "
                    + "(upperA true) and to −i√(1−z)/√z on the upper lip (upperA false). "
                    + "The lower limit is periodRoot(D,z)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-period-source-exponents"),
                DeclarationHandle.Create(Prefix + "chart_source_exponents"),
                H("The shifted theta exponents"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For either lip and real 0 < z < 1, take any lattice data D and complex "
                        + "source vectors M_B and M_D indexed by its rank. Write Q(M) = Mᵀ G M for the "
                        + "Gram quadratic form with the integer matrix G cast to the complex numbers.")),
                    Paragraph(Text("Use (p_B,q_B) = (P(1−z),P(z)) and "
                        + "(p_D,q_D) = (P(rA),dPeriod(upperA,rD)). The source lifts are "
                        + "a_B = periodRoot(A,z)(−i√z) and a_D = i. In each chart j = B,D put "
                        + "ζ_j = [i a_j/(2π p_j)] M_j and τ_j = i q_j/p_j. Both identities "
                        + "2πi Q(ζ_j)/τ_j = Q(M_j)/(2π p_j q_j) hold."))),
                DescribeRole.Theorem))));
}
