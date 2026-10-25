using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class SourceQuarterSpectralClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite resolvents and the complete Hankel square series pay both graph directions.",
        H("The original quarter-digamma graph closes from finite energies"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("source-quarter-spectral-closure-actual-bare-quarter-even-zero-domain-and-identity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SourceQuarterSpectralClosure.actual_bare_quarter_even_zero_domain_and_identity"),
                H("The original even and zero extensions have equivalent graphs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same arbitrary complex half-line L1 and L2 input, the actual bare-quarter weight W(xi)=Re(psi(1/4+i*xi))-Re(psi(1/4)) has equivalent weighted Fourier graph domains for the zero extension and its even extension. The domain equivalence is derived before the infinite energy identity. Finite energy identities E_N=2*U_N-S_N, nonnegative monotone convergence and the complete Hankel Laplace-square series supply the two uniform bounds. On the proved zero-extension graph, E=2*U-Re(Hankel(1/4,u)). No infinite identity or extra trace premise is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-quarter-spectral-closure-actual-bare-quarter-reflected-cross"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SourceQuarterSpectralClosure.actual_bare_quarter_reflected_cross"),
                H("The actual infinite reflected cross has a domain and value"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same L1 and L2 input on its original zero-extension quarter graph gives an integrable literal W-weighted Fourier cross, whose real integral is minus Re(Hankel(1/4,u))/2. Weighted AM-GM pays its complex domain. Polarization and the already derived graph identity pay its value. Equality with the literal even function u(abs(t)) is through an almost-everywhere identity at the origin; no value-u(0) restriction is introduced."))),
                DescribeRole.Theorem))));
}
