using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class PrimeOccupationDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform theta-weighted occupation estimate for arbitrary prime selections.",
        H("Prime Occupation Defect"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-theta-weighted-prime-occupation-defect"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Robin/PriceRecord/PrimeOccupationDefect.uniform_prime_occupation_defect"),
            H("Uniform occupation defect on bounded theta mass"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Put r=sqrt(2), y=r*sqrt(z), D=sqrt(z)*log(z), and "
                    + "q=1/(y^2*log(y)). For every real M>=0 and epsilon>0 there "
                    + "is one real Z>=2 such that, for every real z>=Z, every "
                    + "finite set H of primes p<=y and every finite set X of primes "
                    + "y<p<=z, B=sum_H log(p)+sum_X log(p)<=M*sqrt(z) implies "
                    + "J(B/sqrt(z))<=D*(sum_H(1/p^2-q*log(p)) "
                    + "+sum_X(q*log(p)-1/p^2))+epsilon. Here "
                    + "J(b)=sqrt((sqrt(1+b^2)+3)^3/(sqrt(1+b^2)+1))-4*sqrt(2). "
                    + "All prime weights and cutoffs in the Lean statement are literal; "
                    + "no replacement of log(p) or log(y) by log(z)/2 occurs.")),
                Paragraph(Text(
                    "Generality I records the fixed actual-prime square layer: "
                    + "the reference primes, reciprocal-square cost, r=sqrt(2), "
                    + "scale D, literal price q and profile J are fixed. The "
                    + "I-bearing inputs are OriginalEndpointFirstLayerBand's theta "
                    + "difference identity, PrimeSquareTail's uniform prime-square "
                    + "tail, and QuantitativePrimeAbel's prime intervals and square "
                    + "sums. Other reference sequences, layer powers or cutoff "
                    + "constants require their own estimates and profile derivation. "
                    + "The stated uniformity over all permitted H and X is unchanged.")),
                Paragraph(Text(
                    "For one mass b0>=0 set s=sqrt(1+b0^2), P=1+s, "
                    + "T=sqrt(b0^2+4*P), A=(T-b0)/2 and C=(T+b0)/2. "
                    + "Then AC=P, C-A=b0, A^(-2)+C^(-2)=1 and "
                    + "0<A<=r<=C. The common limiting slope is "
                    + "tau=2/A^2-1=1-2/C^2 in [0,1). The closed profile follows "
                    + "from T^2=P*(P+2) and "
                    + "A+C+2/A+2/C=T*(P+2)/P. These are scalar algebraic "
                    + "endpoints, not assumed prime minimizers or exponent optimizers.")),
                Paragraph(Text(
                    "At finite z use the actual endpoint prices "
                    + "qA=1/((A*sqrt(z))^2*log(A*sqrt(z))) and qC likewise. "
                    + "Monotonicity of t^2*log(t) makes the gain "
                    + "qA*log(p)-1/p^2 nonpositive below A*sqrt(z), and "
                    + "1/p^2-qC*log(p) nonpositive above C*sqrt(z). "
                    + "Selecting all positive gains on the two comparison intervals "
                    + "gives an exact finite dual for arbitrary H and X. Its slopes "
                    + "are sqrt(z)*D*(qA-q) and sqrt(z)*D*(q-qC); "
                    + "their common limit is tau. In particular the actual "
                    + "alpha_z=sqrt(z)*D*q=log(z)/(2*log(r*sqrt(z))) is "
                    + "retained throughout the finite calculation.")),
                Paragraph(Text(
                    "The existing theta_sqrt_scale, log_sqrt_scale and "
                    + "prime_square_tail_uniform supply all endpoint limits. "
                    + "Subtract the two tails ending at z to evaluate finite "
                    + "comparison intervals; there is no new Abel or PNT proof. "
                    + "The intercept tends to tau*b0-J(b0). The two finite slope "
                    + "errors are bounded by their absolute values times the "
                    + "total mass bound M. Thus every selected prime, including "
                    + "escaped mismatch outside both comparison intervals, remains "
                    + "charged. No tightness or compact support of H or X is assumed.")),
                Paragraph(Text(
                    "Continuity of J gives an open neighborhood of each b0 "
                    + "in [0,M] on which its fixed supporting line differs from "
                    + "J by less than epsilon/2. A finite subcover and the "
                    + "intersection of finitely many eventual thresholds complete "
                    + "the uniform estimate. The compact object here is only the "
                    + "scalar interval [0,M]. This is an analytic estimate, "
                    + "not an enumeration, checker, numerical reduction or finite "
                    + "certified instance; utility kind is none.")),
                Paragraph(Text(
                    "The estimate asserts no attainment or sharpness construction, "
                    + "no RH conclusion and no literature novelty. The bounded "
                    + "mass hypothesis controls the total selected mass, with no "
                    + "restriction to the comparison intervals."))),
            DescribeRole.Theorem))));
}
