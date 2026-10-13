using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class PositiveThreeTermRootRealityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/nist2026dlmforthogonalzeros");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite positive three-term recurrence excludes a nonreal spectral parameter at a zero.",
        H("Positive Three-Term Root Reality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-positive-three-term-root-reality"),
                DeclarationHandle.Create("D5/S3/Zeros/Jensen/PositiveThreeTermRootReality."
                    + "finite_positive_three_term_zero_has_real_parameter"),
                H("Reality from a finite positive recurrence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let q be any natural number, z any complex number, c a real sequence "
                        + "and v a complex sequence. Assume v_0 is nonzero, v_1=z v_0, and "
                        + "v_(k+2)=z v_(k+1)-c_k v_k with c_k>0 whenever k+2 is at most q. "
                        + "Then v_q=0 implies Im z=0. Both sequences beyond the finite "
                        + "endpoint are unrestricted. The q=0 premises cannot include a zero; "
                        + "at q=1 no recurrence equation or coefficient positivity is required.")),
                    Paragraph(Text(
                        "For Im z nonzero, induction proves v_k nonzero and "
                        + "Im z times Im(v_(k+1)/v_k) positive. The ratio recurrence is "
                        + "v_(k+2)/v_(k+1)=z-c_k/(v_(k+1)/v_k). Its imaginary product "
                        + "equals (Im z)^2 plus c_k times the previous positive product "
                        + "divided by the squared norm of the ratio. This excludes the "
                        + "terminal zero. With c_0=-1, z=i, v_0=1, v_1=i and v_2=0, "
                        + "the endpoint recurrence holds but the parameter is nonreal; "
                        + "coefficient positivity is essential.")),
                    Paragraph(Text(
                        "This is a finite scalar formulation of classical positive-recurrence "
                        + "zero reality, as recorded by DLMF's Favard and orthogonal-polynomial "
                        + "zero results. The direct ratio proof supplies the missing Lean "
                        + "inference without constructing a measure or Jacobi matrix. "
                        + "It carries no literature originality claim, simplicity claim "
                        + "or interlacing claim.")),
                    Paragraph(Text(
                        "For a monic degree-q polynomial satisfying s p''-X p'+q p=0 "
                        + "with real s>0, differentiate the equation at an actual root beta. "
                        + "For q>0, the reversed normalized jets "
                        + "v_k=k! p^(q-k)(beta)/q! through q satisfy this recurrence with "
                        + "z=beta and c_k=s(k+1), with v_0=1, v_1=beta and v_q=0. "
                        + "The theorem therefore supplies the Hermite root-reality endpoint. "
                        + "The degree-zero monic polynomial has no roots. This application "
                        + "does not establish real-rootedness of an original xi core, "
                        + "the signs of its convolution cofactors, or the Riemann hypothesis.")),
                    Paragraph(Text(
                        "For the same-source finite Appell application, write G(u)=chi(psi(u))-chi(t)+s u with "
                        + "psi(u)=t/(1+t u/n), s=t^2 chi'(t)/n, and M(u)=exp(-chi(t)u)(1+t u/n)^n H(psi(u))/H(t). The "
                        + "actual jets g_k=G^(k)(0) define f_(lambda,k)=lambda g_k-delta_(k,1)s. Starting from "
                        + "a_(lambda,0)=1, the full finite convolution recurrence a_(lambda,m+1)=sum_(k=0)^m binom(m,k) "
                        + "f_(lambda,k) a_(lambda,m-k) defines P_lambda(X)=sum_(k=0)^q a_(lambda,k)/k! times the k-th "
                        + "derivative of X^q. Its coefficients are continuous in real lambda, it is monic of degree q, "
                        + "and the same-source realness supplier makes every coefficient real. P_0 satisfies s P_0''-X "
                        + "P_0'+q P_0=0, whose root reality follows from the finite positive recurrence above. P_1 is "
                        + "exactly the actual raw-M-jet value kernel, rather than a replacement polynomial.")),
                    Paragraph(Text(
                        "The actual germ zero-jet supplier, using n nonzero and H(t) nonzero from the same extraction "
                        + "bounds, gives G(0)=G'(0)=0. For q>0 take b=sqrt(q/|s|) and a=8b, so q=|s|b^2. The authentic "
                        + "source disc at radius 196609a supplies the full row sum of |(g_m/m!)a^(m-1)/s| through q "
                        + "bounded by 1/65536. Multiplication by lambda in the closed interval [0,1] cannot enlarge that "
                        + "sum, so the generic scalar derivative-chain criterion receives its full required 1/16 budget "
                        + "for every P_lambda. The generic coarse-root and scalar-diagonal suppliers then pay the "
                        + "root-location and 1/64 diagonal conditions; no external root-location premise is added. At "
                        + "every actual root beta, P_lambda'(beta) is nonzero and |P_lambda^(m)(beta)/P_lambda'(beta)| is "
                        + "at most a^(m-1) for every m>=1. The corresponding public scalar induction is "
                        + "AppellRootDerivativeChain.actual_root_derivative_chain, with a square root of s as its sigma "
                        + "parameter and lambda g_m/m! as its higher symbol coefficients. Taylor expansion gives a "
                        + "uniform distance at least 1/(2a) between distinct actual roots. "
                        + "CompactSeparatedRealContinuation.compact_separated_real_family then propagates root reality "
                        + "over the entire closed interval from lambda=0 to lambda=1. The q=0 case is kept separately as "
                        + "the literal monic constant polynomial 1.")),
                    Paragraph(Text(
                        "The realness and scale premises are paid by the actual extraction coordinate supplier: "
                        + "chi(conj z)=conj chi(z) globally and, at every real t in the closed source chart, s is a "
                        + "strictly positive real number. Algebraic reflection of psi and the actual G yields G(conj "
                        + "u)=conj G(u). The total one-variable identity deriv(conj composed with f composed with "
                        + "conj)=conj composed with deriv(f) composed with conj, iterated at zero, makes every raw G jet "
                        + "real. No interchange between source-parameter and kernel derivatives is used.")),
                    Paragraph(Text(
                        "There is one fixed U>0 before all source parameters. For arbitrary actual ZeroData Z, T>=32, "
                        + "0<rho<=1/8, n>=1048576*196609^2*U*log(T+2)*T^2/rho^2, every real t with |t-T^2|<=T*rho/32 and "
                        + "every natural q with q<=512*log(T+2), all actual roots of the value kernel from "
                        + "E=exteriorSource Z(localTheoryCore Z T rho) and H=extraction n E are real. The constant U "
                        + "combines the authentic sharp majorant and positive-scale suppliers; the original source E, its "
                        + "finite extraction H, chi, s, and the lambda=1 kernel remain identical throughout the argument. "
                        + "These are exact same-source finite auxiliary kernels. This application supplies neither the "
                        + "still-open signed source/core cofactor transfer nor real-rootedness of the original xi core, "
                        + "and it does not establish the Riemann hypothesis or a strict Robin claim beyond 5040."))),
                DescribeRole.Theorem))));
}
