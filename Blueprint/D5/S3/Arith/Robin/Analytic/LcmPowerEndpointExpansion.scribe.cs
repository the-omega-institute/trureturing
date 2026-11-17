using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class LcmPowerEndpointExpansionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/fankobayashimolnar2025family");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual real-power divisor transform has an exact logarithmic decomposition on prefix least common multiples.",
        H("Exact real-power prefix-lcm expansion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sigma-transform"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.sigmaKappa"),
                H("Real-power divisor transform"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The value at a natural n is the finite sum over positive divisors d of n of mu(n/d) times sigma(d)^kappa. The real exponent is unrestricted in this definition. The divisor set is empty at zero. This is Definition 1.2 of Fan, Kobayashi and Molnar, arXiv:2511.02106v1."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-ratio"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.G"),
                H("Normalized divisor ratio"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For natural n the expression is zeta(kappa)*sigmaKappa(kappa,n)/(exp(gamma)*n*log(log(n)))^kappa. The real part of the complex Riemann zeta at a real argument is used. The positive domain used below has kappa>1 and log(n)>1. This is the normalization in equation (1.1) of Fan, Kobayashi and Molnar."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-cutoff"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.primeCutoff"),
                H("Finite prime support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite set consists of positive natural primes at most the natural floor of the real cutoff x."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-clock-error"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.B"),
                H("Prime-clock Mertens correction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("B(x) is gamma+log(log(theta(x))) plus the finite sum of log(1-1/p) over the prime cutoff. Thus it equals gamma+log(log(theta(x)))-log(P(x)), where P(x) is the finite product of inverse Euler factors."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("terminal-layer-error"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.A"),
                H("Terminal prime-power layers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A(x) is minus the finite sum of log(1-p^(-a-1)), where a is the natural base-p logarithm of the natural floor of x. These are the omitted terminal terms in the ordinary sigma ratio of the prefix least common multiple."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("clock-correction"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.J"),
                H("Prime-power clock correction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("J(x) is log(log(psi(x)))-log(log(theta(x))). It measures the change from the prime clock to the prime-power clock."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("missing-euler-factors"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.T"),
                H("Missing Euler logarithms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("T(kappa,x) is log(zeta(kappa)) plus the finite sum of log(1-p^(-kappa)) over primes not exceeding x. In the convergent domain kappa>1 this is the logarithm of the missing inverse Euler factors."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-correction"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.C"),
                H("Exact local Euler correction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("C(kappa,x) is the sum of log((1-r^kappa)/(1-p^(-kappa))), where r=sigma(p^(a-1))/sigma(p^a) at the maximal prime-power exponent a allowed by x. Its strict upper bound 1/p follows from sigma(p^a)=p*sigma(p^(a-1))+1."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nonnegative-local-correction"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.C_nonneg"),
                H("The local correction is nonnegative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive real kappa and every real x, C(kappa,x) is nonnegative. Every prime in the finite support has a positive maximal exponent. Its exact successive divisor-sum ratio is strictly between zero and 1/p, so the logarithm of the corresponding quotient of Euler factors is nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-normalized-ratio"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.G_pos"),
                H("Positivity on the logarithmic domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For kappa>1 and psi(x)>1, G(kappa,lcmUpto(floor(x))) is positive. The convolution transform is multiplicative, and at a positive prime-power exponent it is the positive difference sigma(p^a)^kappa-sigma(p^(a-1))^kappa. The real zeta factor and the logarithmic normalizing factor are positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-logarithmic-expansion"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.log_G_decomposition"),
                H("The exact logarithmic decomposition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real kappa>1 and every real x with psi(x)>1, log(G(kappa,lcmUpto(floor(x))))=-kappa*B(x)-kappa*A(x)-kappa*J(x)+T(kappa,x)+C(kappa,x). Dirichlet convolution gives the exact prime-power difference. Multiplicativity turns its logarithm into the sum of kappa times the ordinary sigma logarithm and the exact local corrections. The existing ordinary divisor-ratio factorization supplies A and the finite Euler prefix, while log(lcmUpto(floor(x)))=psi(x) supplies the change of clock. This identity is exact; the subsequent correction estimates are unconditional."))),
                DescribeRole.Theorem),
Describe.Lean(
            DescribeId.Create("prime-power-clock-limit"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.J_scaled_limit"),
            H("The unit clock correction"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Write J(x)=log(log(psi(x)))-log(log(theta(x))). As the real variable "
                    + "x tends to infinity, sqrt(x)*log(x)*J(x) tends to one. "
                    + "The assertion is unconditional.")),
                Paragraph(Text(
                    "The existing prime number theorem gives theta(x)/x and psi(x)/x "
                    + "tending to one. Continuity of the logarithm and division by log(x) "
                    + "then give log(theta(x))/log(x) and log(psi(x))/log(x) tending to one. "
                    + "Both clocks eventually exceed one.")),
                Paragraph(Text(
                    "The existing prime-power layer identity gives "
                    + "(psi(x)-theta(x))/sqrt(x) tending to one. The tangent inequality "
                    + "for log(log(t)), applied in both directions, places J(x) between "
                    + "(psi(x)-theta(x))/(psi(x)*log(psi(x))) and "
                    + "(psi(x)-theta(x))/(theta(x)*log(theta(x))). Multiplication by "
                    + "sqrt(x)*log(x) makes both bounds tend to one."))),
            DescribeRole.Theorem),
Describe.Lean(
            DescribeId.Create("terminal-layer-limit"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.A_scaled_limit"),
            H("The coefficient two"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let a_p=floor(log(x)/log(p)) for each prime p<=x, and put "
                    + "A(x)=-sum log(1-p^(-a_p-1)). As the real cutoff x tends "
                    + "to infinity, sqrt(x)*log(x)*A(x) tends to two. "
                    + "The maximal exponent a_p is represented exactly by "
                    + "p.log(floorNat(x)); the terminal exponent in A(x) is "
                    + "a_p+1, represented by p.log(floorNat(x))+1.")),
                Paragraph(Text(
                    "Write tau_p=p^(-a_p-1) and Q(x)=sum tau_p. Maximality of "
                    + "a_p gives tau_p<1/x. For p>sqrt(x), a_p=1 and tau_p=1/p^2; "
                    + "for p<=sqrt(x), a_p>=2 and tau_p<=1/p^3. Splitting the latter "
                    + "primes at u=x^(1/3), their smaller part has at most u terms "
                    + "and total at most u/x=1/u^2. The existing finite cubic-tail "
                    + "estimate bounds the larger part by 2/u^2.")),
                Paragraph(Text(
                    "Thus, with S(x)=sum over sqrt(x)<p<=x of 1/p^2, "
                    + "S(x)<=Q(x)<=S(x)+3*x^(-2/3). The logarithm inequality "
                    + "t<=-log(1-t)<=t+t^2 gives "
                    + "Q(x)<=A(x)<=(1+1/x)*Q(x) for x>=2. The existing uniform "
                    + "prime-square tail gives sqrt(x)*log(x)*S(x) tending to two, "
                    + "while sqrt(x)*log(x)*x^(-2/3) tends to zero. "
                    + "Both bounds therefore have the same limit."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("endpoint-euler-tail-lower"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion.endpoint_euler_tail_lower"),
                H("The endpoint Euler tail supplies coefficient two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every epsilon>0, eventually for all real x, sqrt(x)*log(x)*T(3/2,x)>2-epsilon. Finite Abel summation at the weight 1/(t*sqrt(t)) uses the unconditional prime number theorem for theta. Truncate at C*x for one fixed sufficiently large C, and compare log(p) with log(C*x). The positive, absolutely convergent Euler logarithm series identifies the actual log-zeta remainder and bounds it below by this finite prime interval. Only the lower direction needed by the endpoint argument is asserted."))),
                DescribeRole.Theorem))));
}
