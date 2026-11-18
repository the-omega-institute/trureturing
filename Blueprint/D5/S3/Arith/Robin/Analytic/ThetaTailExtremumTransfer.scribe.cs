using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class ThetaTailExtremumTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional transfer from both signs of the actual theta tail to arithmetic B.",
        H("Same-exponent theta-tail extremum transfer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-theta-tail-omega-pm-to-b"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ThetaTailExtremumTransfer.actual_theta_tail_omega_pm_to_B"),
                H("Both signed power bounds at the original exponent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix real b,cplus,cminus with 0<b<1, 0<cplus and 0<cminus. Write "
                        + "K(x)=-ActualThetaTailLaplace.F(x). Assume explicitly that for every real T "
                        + "there is a real x>max(T,2) with cplus*x^(-b)<=K(x), and that for every "
                        + "real T there is a real x>max(T,2) with K(x)<=-cminus*x^(-b). Then for "
                        + "every real T there is a real x>max(T,2) with (cplus/4)*x^(-b)<=B(x), "
                        + "and for every real T there is a real x>max(T,2) with "
                        + "B(x)<=-(cminus/2)*x^(-b). Both signs and all real thresholds are retained.")),
                    Paragraph(Text(
                        "Here B(x)=Mertens.E₃(x)+log(log(Chebyshev.theta(x)))-log(log(x)) is "
                        + "RHSharpArithmeticEnvelope.B, E(x)=Chebyshev.theta(x)-x and "
                        + "w(x)=(log(x)+1)/(x²*log(x)²). The actual definitions give "
                        + "K(x)=integral_(t>x) E(t)*w(t) and B(x)=K(x)+H(x)+N(x), where "
                        + "H(x)=Mertens.E₃(x)+Mertens.E₂p(x), abs(H(x))<=4/x for x>=2, and "
                        + "N(x)=log(log(theta(x)))-log(log(x))-E(x)/(x*log(x)). "
                        + "N(x)<=0 when x>1 and theta(x)>1. Unconditional prime_number_limits "
                        + "supplies theta(x)>1 eventually; no quantitative global theta rate is assumed.")),
                    Paragraph(Text(
                        "Put delta=cplus/2 and consider K(x)-delta*x^(-b). Choose a negative K point L "
                        + "beyond the requested threshold, a later positive point z, and a later negative "
                        + "point R. Continuity of the actual integral tail gives a compact maximum on [L,R]. "
                        + "Its positive value and the negative endpoint values place the maximum in (L,R), "
                        + "where K(x)>delta*x^(-b). These maxima occur beyond every real threshold.")),
                    Paragraph(Text(
                        "The right theta germ includes x; the left germ excludes x. The jump j(x) is "
                        + "log(x) when x is a natural prime and zero otherwise. One-sided integral calculus "
                        + "gives K'_+(x)=-E(x)*w(x) and K'_-(x)=-(E(x)-j(x))*w(x). At the selected "
                        + "maximum the right derivative of K-delta*x^(-b) is nonpositive and its left "
                        + "derivative is nonnegative. With "
                        + "r(x)=delta*b*x^(1-b)*log(x)²/(log(x)+1), these inequalities give "
                        + "r(x)<=E(x)<=r(x)+j(x), hence 0<=E(x)<=(delta*b+1)*x^(1-b)*log(x). "
                        + "The proof uses the prime jump and both germs at the same maximum; it does not "
                        + "specialize an almost-everywhere derivative at that chosen point.")),
                    Paragraph(Text(
                        "The original ZeroFreeStripMertensEnvelope.nonlinear_quadratic gives "
                        + "abs(N(x))<=8*(E(x)/x)²/log(x) for x>=exp(2) and theta(x)>=x/2. "
                        + "The same-point maximum estimate supplies that hypothesis and yields "
                        + "abs(N(x))<=8*(delta*b+1)²*log(x)/x^(2*b). Since b>0 this is "
                        + "o(x^(-b)); since b<1, 4/x is also o(x^(-b)). Pay cplus/8 for each error "
                        + "to retain cplus/4 on the positive side. On the negative side N<=0 and "
                        + "the finite error costs only cminus/2. No smaller exponent is introduced.")),
                    Paragraph(Text(
                        "The extrema and prime-jump method is related to J.-L. Nicolas, Petites valeurs "
                        + "de la fonction d'Euler, Journal of Number Theory 17 (1983), 375-388, "
                        + "Theorem 3(c), printed p.376, and Section 4, printed pp.386-387, "
                        + "DOI 10.1016/0022-314X(83)90055-0. The two-sign compact bracketing is a "
                        + "conditional proof arrangement, with no novelty claim. The public "
                        + "critical_theta_tail_peak supplies only the negative K sign; the two signed "
                        + "hypotheses of this bridge remain explicit. Neither RH nor a signed spectral "
                        + "construction is concluded."))),
                DescribeRole.Theorem))));
}
