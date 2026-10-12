using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualVonMangoldtBandCompensationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ActualVonMangoldtBandCompensation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite prime-power compensation pays the local volume in the same finite centered max-kernel response.",
        H("Actual finite von Mangoldt band compensation"),
        Blocks(
            Paragraph(Text(
                "Use the literal max kernel h_A(t)=1/(max(A,t)*log(max(A,t))), "
                + "w_c(t)=h_A(t/c)/c, and the tangent a_A(t)=-1/(A*log(A)) at t<=A, "
                + "1/(t*log(t)^2) above A. B_c=w_c-h_A-(c-1)*a_A. "
                + "The regular kernel b_c equals q=(c-1)^2/(c*A*log(A)) at t<=A "
                + "and the literal smooth formula bar_b_c(t) above A. The residual is kappa=b_c-B_c.")),
            Paragraph(Text(
                "Pi is the actual right-closed finite sum of Lambda(n)*kappa(n) through max(A,c*A), "
                + "using the original arithmeticPrefix supplier. V is the Lebesgue integral of kappa "
                + "from 0 to max(A,c*A). For c>1 the A atom is excluded; for c<1 the A atom "
                + "is included. The c*A residual has zero weight in either direction. Full B_c(c*A) "
                + "need not vanish. The definitions include c=1 and bands with no prime-power atoms.")),
            Describe.Lean(
                DescribeId.Create("primitive-theta-actual-band-payment"),
                DeclarationHandle.Create(Prefix + "actual_vonMangoldt_band_compensation_of_theta_increment_lower"),
                H("Primitive real theta increments pay the actual finite band"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume A>=exp(78), 99/100<=c<=101/100, H>0 and 0<=epsilon<1. "
                        + "For every real X<=u<v<=2*X with v-u>=H, assume "
                        + "theta(v)-theta(u)>=(1-epsilon)*(v-u), where X=99*A/100. Then "
                        + "Pi>=(1-epsilon)*max(0,V-(517/1000)*min(H^2,A^2*(c-1)^2)/(A^2*log(A))).")),
                    Paragraph(Text(
                        "The proof compares psi and theta by the actual nonprime Lambda increment. "
                        + "Finite Abel and FTC transport the literal atom sum to the directed psi increment "
                        + "integral. Long distances use the primitive theta premise; short distances use "
                        + "only nonnegative actual mass. The logarithmic derivative cap is 517/500 "
                        + "divided by A^2*log(A). No clock displacement is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("endpoint-safe-finite-response"),
                DeclarationHandle.Create(Prefix + "finite_signed_response_identity"),
                H("The finite response retains the cutoff and terminal atoms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume A>=exp(78), 99/100<=c<=101/100, R>A and R>=c*A. The literal finite response "
                        + "T_R=sum(n<=R,Lambda(n)*B_c(n))-integral(0,R,B_c) equals "
                        + "(q-bar_b_c(A))*D(A)+bar_b_c(R)*D(R) "
                        + "-integral(A,R,D(t)*bar_b_c'(t))+V-Pi, with D=psi-id.")),
                    Paragraph(Text(
                        "The A boundary uses the smooth formula's trace, while b_c(A)=q. "
                        + "The right-closed R atom remains in psi(R). Only the smooth bar_b is "
                        + "differentiated; the Chebyshev staircase D is never differentiated."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-finite-directed-consumer"),
                DeclarationHandle.Create(Prefix + "finite_signed_response_upper_of_theta_increment_lower"),
                H("The same finite response consumes the actual compensation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the primitive theta premise and the same local scale and finite R "
                        + "conditions, T_R is at most its complete smooth boundary plus epsilon*V "
                        + "+(1-epsilon)*(517/1000)*min(H^2,A^2*(c-1)^2)/(A^2*log(A)). "
                        + "The compensation theorem is used on the actual V-Pi term in this identity.")),
                    Paragraph(Text(
                        "The primitive uniform real theta premise remains an assumption. "
                        + "A fixed Guth-Maynard specialization needs its separately quantified constants "
                        + "and eventual scale conditions; A>=exp(78) does not provide them. "
                        + "This finite arithmetic result does not establish infinite Gamma exchange, "
                        + "a signed spectral anchor against Res+d, the all-integer Robin inequality, "
                        + "RH, or official acceptance."))),
                DescribeRole.Theorem))));
}
