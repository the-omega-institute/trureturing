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
                DescribeId.Create("actual-plus-unitary-fourier"),
                DeclarationHandle.Create(Owner + "unitarySourceFourier"),
                H("Actual positive angular Fourier convention"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The actual transform is (sqrt(2*pi))^(-1) times the mathlib Fourier "
                        + "transform at -xi/(2*pi). Equivalently its genuine L1 integral "
                        + "has kernel exp(i*xi*t) and unitary angular normalization."))),
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
                DescribeId.Create("finite-actual-gamma-energy-unbounded"),
                DeclarationHandle.Create(Owner + "actual_h6_finite_gamma_energy_unbounded"),
                H("Unbounded finite Gamma energy under every strict physical cap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real K>1 and every real B, there is a real physical "
                            + "H6 source F whose complete physical theta has HasSum equal "
                            + "to F(x) for every x>=pi. It belongs to every constant-shift "
                            + "Gamma form domain, has physical mass H(F)>0, and satisfies "
                            + "the same strict sixth-moment cap M(F)<K*H(F). Its genuinely "
                            + "finite reference Gamma energy P0(F) exceeds B*H(F). Here "
                            + "P0(F) is the actual integral of gammaWeight(xi) times the "
                            + "squared norm of the actual profile's unitary Fourier transform.")),
                    Paragraph(Text(
                        "The witnesses also include a physical H6 limit F_infinity and "
                            + "a sequence G. The limit escapes every relative constant "
                            + "shift whose weight is at least one everywhere. Each G(n) "
                            + "is real, belongs to physical H6, retains the complete theta "
                            + "HasSum identity, belongs to every real constant-shift Gamma "
                            + "domain, and has positive physical mass and the same strict "
                            + "K-cap. The selected high-energy F equals G(n) for some n. "
                            + "The actual weighted squared error integral "
                            + "integral_{x>pi}(x/pi)^6*norm(F_infinity(x)-G(n)(x))^2 "
                            + "tends to zero. These witnesses are quantified inside the "
                            + "given K and B; the statement does not put a single G "
                            + "outside the quantifier over B.")),
                    Paragraph(Text(
                        "The construction uses the genuine finite cosine sums u_N "
                            + "of the original centered tent profile. One compression "
                            + "kappa is fixed within the sequence, and the physical source "
                            + "is x^(-9/4)*u_N(log(x/pi)/kappa) for x>=pi, zero otherwise. "
                            + "Exact support makes every n>=2 physical theta term zero; "
                            + "the whole HasSum is proved, and the actual profile is "
                            + "identified with u_N(t/kappa). No theta truncation or "
                            + "independent spectral premise is used.")),
                    Paragraph(Text(
                        "True integrability is established before the real integral "
                            + "is used as energy. The actual finite-sum Fourier formula "
                            + "and sinc-square decay give "
                            + "(1+xi^2)*norm(hat(u_N(t/kappa))(xi))<=E_N. "
                            + "A reused digamma strip estimate gives "
                            + "0<=gammaWeight(xi)<=G0*(1+xi^2), hence the actual Gamma "
                            + "density is bounded by G0*E_N^2/(1+xi^2), an integrable "
                            + "majorant. The constants are finite for each N and need "
                            + "not be uniform in N. From gammaWeight>=1, the unweighted "
                            + "Fourier square is also integrable; adding its constant "
                            + "multiple proves domain membership for every real shift, "
                            + "including shifts whose weights change sign.")),
                    Paragraph(Text(
                        "The finite-frequency bands are "
                            + "J_n=[(exp(4^(n+1))-1)/kappa,(exp(4^(n+1))+1)/kappa]. "
                            + "They are pairwise disjoint and have length 2/kappa. "
                            + "For each retained n<=N, the actual positive-log density "
                            + "is at least kappa^2/(4096*pi) on J_n. Finite disjoint-band "
                            + "integration and logplus<=C_p*gammaWeight give "
                            + "P_N>=(N+1)*kappa/(2048*pi*C_p). No infinite "
                            + "sum/integral interchange is used for this lower bound. "
                            + "The common support gives H_N<=3*pi, so choosing N "
                            + "large enough yields P_N>B*H_N for any real B.")),
                    Paragraph(Text(
                        "The fixed support also gives M_N<=exp(9*kappa/2)*H_N; "
                            + "choose exp(9*kappa/2)<K to keep one strict cap for every "
                            + "sequence member. The geometric spatial tail is at most "
                            + "2^(-(N+1)). After proving the error density genuinely "
                            + "integrable on the common physical support [pi,4*pi], "
                            + "the actual H6 squared error is bounded by "
                            + "12288*pi*(1/4)^(N+1), which tends to zero.")),
                    Paragraph(Text(
                        "This is convergence in the displayed physical H6 metric. "
                            + "The construction has unbounded reference Gamma energies; "
                            + "it provides no Gamma form-norm convergence and does not "
                            + "contradict closedness of a Gamma form. The result concerns "
                            + "an explicit Fourier form-domain obstruction and finite "
                            + "energy growth. It asserts no sign for the complete Weil "
                            + "energy and proves no RH or Robin conclusion."))),
                DescribeRole.Theorem))));
}
