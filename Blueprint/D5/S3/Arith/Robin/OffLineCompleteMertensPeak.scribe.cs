using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OffLineCompleteMertensPeakDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OffLineCompleteMertensPeak.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An off-line zero forces a finite complete Mertens peak and an actual lcm Robin violator.",
        H("Off-line zeros and finite complete Mertens peaks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("off-line-complete-mertens-peak"),
                DeclarationHandle.Create(Prefix + "off_line_complete_mertens_peak"),
                H("A positive arithmetic peak and an explicit integer interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Analytic/polak2026finiterobinca"),
                    LibraryNoteRef.Create("D5/L/Zeros/revesz1988oscillation"),
                    LibraryNoteRef.Create("D5/L/Weil/johnstonyang2022pnt"),
                    LibraryNoteRef.Create("D5/L/Analytic/lay2015mertenssignchanges")),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a countable zero family in the open critical strip, with "
                        + "multiplicities retained, a conjugation-preserving index equivalence, "
                        + "|Im(rho_i)|>10, and HasSum of 1/(rho_i*(1-rho_i)) equal to "
                        + "2+EulerGamma-log(4*pi). Assume the integrated explicit formula "
                        + "Hc(y)=U(exp(y))-log(2*pi)+R(y) for y>0, where "
                        + "R(y)=sum exp(-2*(k+1)*y)/(2*(k+1)*(2*(k+1)+1)), k>=0. "
                        + "The low-height and explicit-formula inputs remain hypotheses; "
                        + "they are respectively the cited Revesz fact and Polak's Proposition 14, "
                        + "equation (8.6), with the trivial-zero correction (8.18).")),
                    Paragraph(Text(
                        "Fix rho_0=beta+i*gamma with beta>1/2 and gamma>0. Set delta=beta-1/2, "
                        + "D=gamma+10, m0=100*D^2/delta^2, m1=500*D^4/delta^2, and "
                        + "B0=exp(4*(28*m1+20)^2). There is A in [exp(4*m0),exp(28*m1)] "
                        + "such that U(A)>sqrt(A)*(4*log(A)+9). Assuming in addition the "
                        + "Johnston-Yang and Lay inputs of complete_mertens_peak, there is a real "
                        + "t in [A,exp(4*(log(A)+20)^2)], that entire interval lies in [A,B0], "
                        + "and N=lcm(1,...,floor(t)) satisfies 5040<N<=exp(B0*log(B0)) and "
                        + "sigma(N)/N>exp(EulerGamma)*log(log(N)).")),
                    Paragraph(Text(
                        "The full Gaussian response supplies m in [m0,m1] and a signed integral "
                        + "at least exp((beta^2+16*beta)*m)/2. If H has no peak above "
                        + "(4*y+11)*exp(y/2) on [4*m,28*m], signed localization bounds that "
                        + "same integral by 2000*m*D^2*exp(33*m/4), retaining the complete "
                        + "envelope integral and both exterior contributions.")),
                    Paragraph(Text(
                        "The exponent difference is beta^2+16*beta-33/4=17*delta+delta^2. "
                        + "The scale bounds give log(4000*m*D^2)<20+6*D+2/delta<D^2/delta "
                        + "<17*delta*m. Here 20*delta+6*D*delta+2<3*D+12<D^2 follows from "
                        + "D>20 and 0<delta<1/2. This contradicts the two integral estimates "
                        + "and produces the positive H peak.")),
                    Paragraph(Text(
                        "Each correction term is strictly below "
                        + "(1/2)*(1/(k+1)-1/(k+2)); telescoping bounds R(y)<1/2. "
                        + "Since log(2*pi)>1, the explicit formula gives H(y)<=U(exp(y)). "
                        + "Also m0>160000, so A>10000. The elementary strict comparison "
                        + "4*log(A)>4*log(A)^2/(1+log(A)) supplies the complete Mertens "
                        + "peak threshold. Finally log(A)<=28*m1 bounds the truncation "
                        + "endpoint by B0 and transfers the integer bound through monotonicity "
                        + "of x*log(x). The conclusion is conditional on an off-line zero; "
                        + "it supplies no instance of that condition."))),
                DescribeRole.Theorem))));
}
