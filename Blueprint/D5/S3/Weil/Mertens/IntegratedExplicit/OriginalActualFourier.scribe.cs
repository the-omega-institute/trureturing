using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class OriginalActualFourierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual finite-atom Fourier density is finite", H("The actual finite-atom Fourier density is finite"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-actual-fourier-prefix-eq-zero-extension"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.prefix_eq_zero_extension"),
                H("The original prefix and its zero extension"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite atom type, complex coefficients with zero total mass, and nodes in the closed window [0,D], the original prefix equals its closed-window zero extension pointwise. The finite closed-step expansion retains the endpoint nodes; the common tail cancels by zero mass."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-actual-fourier-prefix-l1-l2"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.prefix_L1_L2"),
                H("Integrable prefix and square energy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original prefix is Lebesgue integrable and its squared norm is integrable. L1 follows from the finite closed-step expansion. L2 reuses AtomicPrefixEnergy.shifted_hinge_prefix_energy. Empty atom types, repeated nodes and cancelling coefficients remain allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-actual-fourier-frequency-mul-ahat"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.frequency_mul_Ahat"),
                H("Every frequency, including zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Ahat(A,w) is literally the Lebesgue integral of A(u)*exp(-I*w*u). For the original prefix, (I*w)*Ahat(A,w)=sum_i a_i*exp(-I*w*x_i) at every real w. The nonzero-frequency proof integrates each finite closed step; zero mass proves the frequency-zero case."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-actual-fourier-normsq-ahat-bound"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.normSq_Ahat_bound"),
                H("An integrable square envelope"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Put C0=integral norm(A) and M=sum_i norm(a_i). The triangle inequality gives norm(Ahat)<=C0, while the finite Fourier identity gives abs(w)*norm(Ahat)<=M. Adding their squared bounds yields norm(Ahat)^2<=(C0^2+M^2)/(1+w^2) for every real frequency."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-actual-fourier-actual-rho-finite"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier.actual_rho_finite"),
                H("Finiteness of the literal spectral measure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The density is literally norm(Ahat(A,w))^2/(2*pi), and rho is volume.withDensity(ofReal(density)). Continuity of the L1 Fourier integral gives measurable density. The square envelope is integrable, so the withDensity measure is finite without a finite-measure premise."))),
                DescribeRole.Theorem))));
}
