using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualSuzukiFiniteGammaEnergyDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFiniteGammaEnergy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite actual Gamma energies are unbounded relative to physical mass "
            + "under every strict physical sixth-moment cap, with actual H6 convergence.",
        H("Finite Gamma Energy and H6 Approximation"),
        Blocks(
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
