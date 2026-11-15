using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class PsiLaplaceContinuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Measurability of the actual psi source",
        H("PsiLaplaceContinuation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qpsi-measurable"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/PsiLaplaceContinuation.qpsi_measurable"),
                H("Measurability of the actual psi source"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("qpsi(u)=exp(-u)*(psi(exp u)-exp u), with the actual Chebyshev psi function."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qpsi-integrable"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/PsiLaplaceContinuation.qpsi_integrable"),
                H("Unconditional source integrability"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing WeightedPrimeLimit.chebyshev_error_kernel_integrable is transported by x=exp u, including the Jacobian. Boundedness alone is not an L1 argument."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("apsi-entire"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/PsiLaplaceContinuation.Apsi_entire"),
                H("Entire oriented finite correction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite correction Apsi(U,s)=integral_(0..U) exp(-su)*qpsi(u) is entire for every real U, in both orientations, by the existing finiteHead_entire theorem."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qpsi-eq-mpsi"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/PsiLaplaceContinuation.Qpsi_eq_Mpsi"),
                H("Actual positive-half-plane continuation identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real cutoff U and Re s>0, the actual integral Qpsi(U,s) equals -(1+logDeriv(zeta1,1+s))/(1+s)-Apsi(U,s). The Mellin identity uses actual von Mangoldt coefficients, Mathlib SumCoeff and the existing Mangoldt prefix estimate. There is no prime-power correction."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mpsi-real-analytic"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/PsiLaplaceContinuation.Mpsi_real_analytic"),
                H("Regularity of the full real corridor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized-zeta expression Mpsi is analytic at every real x>-1, including zero. It uses the existing normalized zeta nonvanishing result on the positive real axis; it makes no assertion of integral convergence there."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-source-poles"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/PsiLaplaceContinuation.actual_source_poles"),
                H("Complete local source pole"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every nontrivial zeta zero rho in the open critical strip, a=rho-1 lies in Re s>-1, is nonzero and nonreal. With m the full positive analytic multiplicity and Lambda=-m/rho, Mpsi=Lambda/(s-a)+H on a full punctured complex neighborhood, where H is analytic. The source order is -1 and the order of -Mpsi prime+Mpsi is -2. Real analyticity excludes real source poles. No condition at 2*rho or simple-zero assumption is used."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-normalized-limit"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/PsiLaplaceContinuation.source_normalized_limit"),
                H("Full complex source coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication by s-a in the source pole expansion tends to Lambda=-m/rho in the full complex punctured neighborhood. This supplier is consumed by the forcing coefficient theorem."))), DescribeRole.Theorem))));
}
