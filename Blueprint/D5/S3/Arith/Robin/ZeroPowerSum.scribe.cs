using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ZeroPowerSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ZeroPowerSum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite complex family containing one has a bounded power sum with real part at least one.",
        H("Finite Cassel power-sum selection"),
        Blocks(
            Paragraph(Text("Quantitative actual-zero application. Suppose IsNontrivialZero(rho0), beta=Re(rho0)>1/2 and gamma=Im(rho0)>0. The actual height theorem implies gamma>10. Set delta=beta-1/2 in (0,1/2), D=gamma+10>20, m0=100*D^2/delta^2, m1=500*D^4/delta^2, and a=beta^2+16*beta. Use the multiplicity-exact closed set S={k:|Im(actualZero(k))-gamma|<=6} from ActualReciprocalSquareBounds. Exhaustivity and positivity of each analytic multiplicity supply an occurrence k0 with actualZero(k0)=rho0; it lies in S and q_k0=a for q_k=(actualZero(k)-i*gamma)^2+16*(actualZero(k)-i*gamma). Thus z_k=exp(m0*(q_k-a)) has z_k0=1. Apply exists_pow_sum_re_ge_one after the finite equivalence Fin(card S) to S, keeping repeated values. It gives 1<=nu<=2*card(S)+1<=5*D^2 and Re(sum_S z_k^nu)>=1. At m=nu*m0, m0<=m<=m1, and exp(m*q_k)=exp(a*m)*z_k^nu. Hence the real part of the finite local sum is at least exp(a*m). No modulus restriction is added to the finite power-sum theorem.")),
            Paragraph(Text("Paying the full omitted tail. For eta!=0 and d=|eta-gamma|>=6, |eta|<=gamma+d<=(gamma+6)*d/6. Since d^2/36<=1+m*(d^2-36)<=exp(m*(d^2-36)), exponential cancellation gives exp(-m*(eta-gamma)^2)<=D^2*exp(-36*m)*eta^(-2). Multiplying by the strip factor exp(17*m) bounds every omitted summand by D^2*exp(-19*m)*eta_k^(-2). Absolute comparison proves summability and bounds the norm of the ENTIRE strict complement by 2*D^2*exp(-19*m). The exact splitting E=sum_S exp(m*q_k)+sum_{k outside S} exp(m*q_k) retains distance six in S. The lower time bound and delta^2<1 imply D^2<=m and m>=1. The inequality exp(19*m)>=1+19*m>=4*D^2 makes that tail at most 1/2; since a>=0, exp(a*m)>=1. Therefore Re(E)>=exp(a*m)-1/2>=exp(a*m)/2. This is a composite application of the frozen power-sum and actual mass results, not a separate theorem identity.")),
            
            Describe.Lean(
                DescribeId.Create("finite-cassel-power-sum"),
                DeclarationHandle.Create(Prefix + "exists_pow_sum_re_ge_one"),
                H("A power sum with real part at least one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Zeros/revesz1988oscillation")),
                Blocks(
                    Paragraph(Text(
                        "For every n and every indexed complex family z:Fin(n)->C with an entry equal "
                        + "to one, there is an integer exponent nu with 1<=nu<=2*n+1 and "
                        + "Re(sum_i z(i)^nu)>=1. Repeated entries retain their multiplicities, and "
                        + "the other entries have unrestricted moduli.")),
                    Paragraph(Text(
                        "Delete one entry equal to one and pair each remaining entry with its complex "
                        + "conjugate. The resulting family has d=2*(n-1) entries and real power sums p(k). "
                        + "Let c(k) be the real part of its signed elementary symmetric function, so "
                        + "c(0)=1 and c(d+1)=0. Newton's identity gives "
                        + "k*c(k)=-sum_{a+b=k,a<k} c(a)*p(b). If every p(1),...,p(d+1) were negative, "
                        + "strong induction would make every c(0),...,c(d+1) positive, a contradiction. "
                        + "A nonnegative p(nu) yields a nonnegative real power sum for the remaining "
                        + "entries; restoring the designated one proves the stated bound. "
                        + "The empty remaining family includes the case n=1.")),
                    Paragraph(Text(
                        "This is the discrete Cassel step in the proof following Lemma 6 of Revesz's "
                        + "Effective oscillation theorems for a general class of real-valued remainder "
                        + "terms, printed page 488. The finite argument uses Mathlib's "
                        + "MvPolynomial.mul_esymm_eq_sum and the vanishing of elementary symmetric "
                        + "functions above the cardinality of their indexed family."))),
                DescribeRole.Theorem))));
}
