using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class FrequencyDomainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a>0 and only original Ioc MemLp 2, finite zero-extension actual-Gamma energy is equivalent to finiteness of the full integer coefficient sum with the actual digamma-increment weights. This consumes the boundary-domain equivalence and periodic spectral identity, not a new Fourier-L2 premise. The compact-core conclusions keep their original finite-energy hypotheses.",
        H("Actual Gamma form core: FrequencyDomain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-frequencydomain-actual-gamma-zero-domain-iff-digamma-weighted-sum-finite"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actual_gamma_zero_domain_iff_digamma_weighted_sum_finite"),
                H("actual gamma zero domain iff digamma weighted sum finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>0 and only original Ioc MemLp 2, finite zero-extension actual-Gamma energy is equivalent to finiteness of the full integer coefficient sum with the actual digamma-increment weights. This consumes the boundary-domain equivalence and periodic spectral identity, not a new Fourier-L2 premise. The compact-core conclusions keep their original finite-energy hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualfouriertruncation"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actualFourierTruncation"),
                H("Literal finite Fourier sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For period d>0, base t, and a finite integer set S, the truncation is the sum of fourierCoeff(liftIoc(d,t,u),n)*exp(2*pi*i*n*x/d) over n in S. The coefficients use probability Haar measure. Equivalently each term is the physical coefficient sqrt(d)*fourierCoeff multiplied by the Lebesgue-normalized basis vector exp(2*pi*i*n*x/d)/sqrt(d)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-fourier-truncation-form-core"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/FrequencyDomain.actual_fourier_truncation_form_core"),
                H("Fourier convergence in the actual Gamma form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a>0 and let u be any complex L2 profile on (-a,a] with finite actual zero-extension Gamma energy. Every finite Fourier truncation and every residual belongs to that same zero-extension domain. As the finite integer set increases, the sum of the residual squared L2 mass and its actual zero-extension Gamma energy tends to zero. Parseval gives the physical mass tail, nonnegative digamma weights give the periodic energy tail, and E0<=EP+C(a)*mass gives the zero-extension energy limit. The residual domain hypotheses are proved before real integrals are used. No endpoint matching, parity or smoothness is imposed."))),
                DescribeRole.Theorem))));
}
