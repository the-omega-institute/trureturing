using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilPrimeThresholdParityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilPrimeThresholdParity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original arithmetic parity columns and actual odd edge integrals preserve the cancellation needed for a uniform Weil Schur certificate across prime activation.",
        H("Prime Threshold Parity"),
        Blocks(
            Describe.Lean(DescribeId.Create("arithmetic-parity-pair-columns"),
                DeclarationHandle.Create(Owner + "arithmetic_parity_pair_columns"),
                H("Both original parity columns before rounding"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expand the existing couplingColumn on {n,-n}, with coefficients (1,1) and (1,-1). For n>0 and |m|>n the two numerators are respectively 2(n*s_n-m*s_m) and 2(m*s_n-n*s_m), over pi*(m^2-n^2). The original complete arithmetic symbol and its proved oddness are retained. The numerical consumer applies the unitary parity normalization before enclosing and quantizing every high-mode column."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-prime-activation"),
                DeclarationHandle.Create(Owner + "oddPrimeActivation"),
                H("The complete complex pairing of both activation edges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For F(t)=sum v_n*sin(pi*n*t), the expression is w times the integral from zero to h of conjugate(F(t))*F(h-t)+conjugate(F(h-t))*F(t). For a shift 2-h in (1,2), odd Fourier basis values on the two edges have opposite signs. This integral is consequently the actual negative symmetric prime contribution after dilation. All cross terms and complex coefficients remain present."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("odd-prime-activation-cubic-bound"),
                DeclarationHandle.Create(Owner + "odd_prime_activation_cubic_bound"),
                H("Cubic activation energy on the finite odd block"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For w,h nonnegative, bound the norm of the complete edge pairing by w*pi^2*h^3/3 times sum n^2 times sum norm(v_n)^2. The proof derives the pointwise profile bound from the actual sine functions, integrates t*(h-t) exactly, and applies finite Cauchy-Schwarz. Continuity supplies integrability. No approximate zero boundary condition or assembled energy bound is assumed.")),
                    Paragraph(Text("The accompanying interval certificate independently recomputes the full low matrices and all high-mode Schur corrections for every a in log(3)/2 plus or minus 2e-8, including the entering prime 3. The cubic estimate explains the odd-block cancellation; the certificate uses the exact matrix entries rather than replacing them by this coarser bound. Fourier/domain identification and the infinite Neumann/logarithmic comparison remain paper bridges. Lean elaboration, Scribe emission and transitive axiom checking have not been executed. No unbounded-scale gap or Xi limit is asserted."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaBridge/WeilEvenDualStencil"))]));
}
