using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualSuzukiDomainCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiDomainCounterexample.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exactly K>1 admits one real original physical H6 source with positive physical "
            + "mass, strict sixth-moment ratio below K, and simultaneous escape from every "
            + "Gamma form domain whose constant-shifted weight is at least one. The same "
            + "source retains full theta, actual profile L1 and L2, and all exponential "
            + "position moments.",
        H("Sharp Sixth-Moment Threshold for Simultaneous Gamma-Domain Escape"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-physical-h6"),
                DeclarationHandle.Create(Owner + "originalPhysicalH6"),
                H("Original physical sixth-moment domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The original half-line is x>pi. The predicate requires physical "
                        + "MemLp 2 and genuine integrability of (x/pi)^6 times norm(F(x))^2 "
                        + "on that half-line. It is not a coefficient-space condition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("complete-physical-theta"),
                DeclarationHandle.Create(Owner + "fullTheta"),
                H("Complete physical theta transform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sum includes every integer n>=1 with term n^4 F(n^2 x), using "
                        + "n=k+1. For the constructed source every n>=2 term is proved zero "
                        + "on x>=pi by exact support, and a full HasSum proof gives TF=F. "
                        + "No theta cutoff is imposed as a definition or premise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-gamma-profile"),
                DeclarationHandle.Create(Owner + "actualGammaProfile"),
                H("Actual zero-extended theta profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For t>=0 the profile is (pi exp(t))^(9/4) times TF(pi exp(t)); "
                        + "for t<0 it is zero. There is no B operator. The same actual "
                        + "profile is identified pointwise with a time compression of "
                        + "the centered tent times the real lacunary cosine series used "
                        + "in the Fourier proof: u(t)=counterProfile(t/kappa)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("literal-reference-gamma-weight"),
                DeclarationHandle.Create(Owner + "gammaWeight"),
                H("Literal reference Gamma weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write p0(xi)=gammaWeight(xi). Its literal value is "
                        + "(2/sqrt(pi))*((xi^2+1/16)/(xi^2+25/16)) "
                        + "*(Re digamma(1/4+i*xi)-log(pi))+1+4*sqrt(pi). "
                        + "The construction proves p0(xi)>1 and "
                        + "max(log(abs(xi)),0)<=C0*p0(xi) with a fixed finite "
                        + "nonnegative C0. Thus the relative shift c=0 is admissible."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("literal-shifted-gamma-domain"),
                DeclarationHandle.Create(Owner + "originalGammaFormDomain"),
                H("Literal constant-shifted Gamma form domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a real relative shift c and source F, "
                            + "originalGammaFormDomain(c,F) means genuine integrability "
                            + "of (p0(xi)+c) times the squared norm of the actual profile's "
                            + "unitary positive angular Fourier transform. The theorem "
                            + "calls c admissible precisely when p0(xi)+c>=1 for every xi. "
                            + "This permits negative c whenever the same bound holds.")),
                    Paragraph(Text(
                        "For every admissible c, p0<=p0+c+abs(c) "
                            + "<=(1+abs(c))*(p0+c). Consequently max(log(abs(xi)),0) "
                            + "<=C0*(1+abs(c))*(p0(xi)+c). Finiteness of the shifted "
                            + "Gamma density alone would imply finiteness of the "
                            + "nonnegative positive-log density. This uses the literal "
                            + "weight; no identification with a separate formal V "
                            + "structure is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-h6-gamma-domain-counterexample"),
                DeclarationHandle.Create(Owner + "actual_h6_gamma_domain_escape_iff"),
                H("The exact cap range is K>1"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real K, the following complete source existence "
                            + "statement is equivalent to 1<K. The real original physical "
                            + "H6 source F has H=integral over x>pi of norm(F(x))^2 strictly "
                            + "positive and M=integral over x>pi of (x/pi)^6*norm(F(x))^2 "
                            + "strictly below K*H. No normalization H=1 is asserted.")),
                    Paragraph(Text(
                        "The same witness has complete theta HasSum equal to F(x) for "
                            + "every x>=pi. Its actual profile belongs to L1 and L2, has "
                            + "every real exponential position moment finite, has strictly "
                            + "positive squared mass, and has a finite strictly positive "
                            + "first position moment. Its actual extended positive-log "
                            + "Fourier integral equals infinity. This one F fails "
                            + "originalGammaFormDomain(c,F) simultaneously for every "
                            + "real c whose shifted weight is at least one everywhere. "
                            + "The witness F is chosen before c and does not vary "
                            + "with the shift.")),
                    Paragraph(Text(
                        "For K>1, compress the explicit centered-tent lacunary cosine "
                            + "profile into a sufficiently short positive logarithmic "
                            + "window. The physical source remains x^(-9/4) times the "
                            + "compressed profile at log(x/pi) for x>=pi, zero otherwise. "
                            + "The physical support directly bounds the literal sixth "
                            + "moment by a factor strictly smaller than K times H. "
                            + "The Fourier scaling argument retains log-plus divergence.")),
                    Paragraph(Text(
                        "Conversely, the pointwise weight (x/pi)^6 is at least one on "
                            + "x>pi. Genuine integrability gives H<=M. Together with H>0 "
                            + "and M<K*H this forces 1<K, excluding every K<=1 including "
                            + "the boundary. No extra positivity assumption on K is used.")),
                    Paragraph(Text(
                        "The uncompressed seed Fourier transform has common phase exp(i*xi/2). "
                            + "Both cosine channels remain in the nonnegative amplitude, "
                            + "each using the concrete tent transform "
                            + "sinc(xi/8)^2/(4*sqrt(2*pi)). An integrable coefficient-times-tent "
                            + "majorant justifies the infinite series interchange.")),
                    Paragraph(Text(
                        "For the seed, the bands of radius one around exp(4^(n+1)) are pairwise "
                            + "disjoint. On every band the positive-log Fourier density "
                            + "is at least 1/(4096*pi); each band has measure two. "
                            + "The genuinely extended nonnegative integral is therefore "
                            + "infinite. Fourier compression preserves this divergence, "
                            + "and each admissible shifted Gamma comparison transfers "
                            + "it to nonintegrability on the same compressed actual source.")),
                    Paragraph(Text(
                        "This theorem is an infinite analytic source-domain obstruction. "
                            + "It asserts neither a negative complete Weil energy nor RH "
                            + "or a Robin conclusion. The conclusion concerns the literal "
                            + "simultaneous Gamma-domain obstruction on the original "
                            + "physical source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-gamma-weight-continuity"),
                DeclarationHandle.Create(Owner + "finiteGammaWeight_continuous"),
                H("Continuity of the actual reference Gamma weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The literal gammaWeight is continuous on the real frequency line. "
                        + "The proof rewrites its density through the existing smooth mu "
                        + "function and uses the nonsingular rational factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-gamma-weight-quadratic-upper"),
                DeclarationHandle.Create(Owner + "finiteGammaWeight_quadratic_upper"),
                H("A global quadratic upper bound for the actual Gamma weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is a real G>0 such that gammaWeight(xi)<=G*(1+xi^2) "
                        + "for every real xi. The proof consumes the existing digamma "
                        + "strip estimate and the actual rational factor bounds. "
                        + "The finite cosine construction consumes this estimate with "
                        + "its proved Fourier decay to obtain a genuinely integrable "
                        + "Cauchy-kernel majorant; the growth bound alone asserts no "
                        + "energy finiteness for arbitrary H6 sources."))),
                DescribeRole.Theorem))));
}
