using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class EulerLayerPhaseSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/EulerLayerPhaseSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Euler higher layers activate before the forward reference window, forcing "
            + "occupation in the same strict inventory integer while its first primes are absent.",
        H("Exact Euler Layer Phase Separation"),
        Blocks(
            Paragraph(Text(
                "For a prime q and positive exponent k, the actual marginal is the logarithm "
                + "of (1-q^(-(k+1)))/(1-q^(-k)), divided by log(q). Write n=q^k and "
                + "lambda(x)=1/(x*log(x)). A literal clock tau>1 satisfies "
                + "lambda(tau)=goldenLayerMarginal(q,k); no inverse function is assumed.")),
            Describe.Lean(
                DescribeId.Create("euler-higher-layer-price-separation"),
                DeclarationHandle.Create(Prefix + "higher_layer_price_separation"),
                H("A uniform prime and power margin"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural prime q and natural k>=2 with n=q^k>=16, "
                        + "lambda(3*n/4)<goldenLayerMarginal(q,k). For every real tau>1 "
                        + "whose price equals that marginal, tau<3*n/4.")),
                    Paragraph(Text(
                        "The logarithmic lower bound for the exact Euler ratio gives "
                        + "r>(1-1/q)/(n*log(q))=k*(1-1/q)/(n*log(n)). "
                        + "If k>=4, the coefficient is at least 2. If k=3, n>=16 forces "
                        + "q>=3; if k=2, primality and n>=16 force q>=5. Thus the "
                        + "coefficient is at least 8/5. Since (4/3)^6<16<=n, "
                        + "5*log(n)<6*log(3*n/4), and 8/(5*n*log(n))>lambda(3*n/4). "
                        + "Strict decrease of lambda gives the clock conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("euler-higher-layer-forward-window"),
                DeclarationHandle.Create(Prefix + "higher_layer_forward_window"),
                H("Both literal forward window implications"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every prime q, k>=2 and real t>=243, set B=t+t^(4/5). "
                        + "If t<n<=B then lambda(t)<goldenLayerMarginal(q,k). "
                        + "For every tau>1 with lambda(tau)=goldenLayerMarginal(q,k), "
                        + "tau<n, t<n<=B implies tau<t, and t<=tau<=B implies B<n. "
                        + "The last implication has no n>=16 hypothesis.")),
                    Paragraph(Text(
                        "The coefficient k*(1-1/q) is at least one for every higher "
                        + "layer, giving r>lambda(n) and tau<n even for small powers. "
                        + "The exact bound t^(4/5)<=t/3 gives B<=4*t/3. In the first "
                        + "implication n>t>=243 supplies n>=16. In the second, tau<n "
                        + "and tau>=t supply the same size bound before the phase "
                        + "estimate is used. All asserted endpoints remain strict."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("euler-strict-inventory-forward-window"),
                DeclarationHandle.Create(Prefix + "strict_inventory_forward_window"),
                H("Occupation and absence in the same positive integer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix one positive natural integer U and a real t>=243. Assume "
                        + "the literal strict inventory law: for every natural q, "
                        + "U.factorization(q)=optimalLayerCount(lambda(t),q), where "
                        + "optimalLayerCount is the finite number of positive k for "
                        + "which q is prime and lambda(t)<goldenLayerMarginal(q,k). "
                        + "For every prime q and k>=2 with t<q^k<=B, "
                        + "k<=U.factorization(q) and q^k divides U. For every prime q "
                        + "with t<q<=B, U.factorization(q)=0. The theorem also gives "
                        + "all the literal higher clock conclusions just stated.")),
                    Paragraph(Text(
                        "The strict price inequality puts each reference higher layer "
                        + "in the finite active exponent prefix identified by "
                        + "positive_layers_eq_count_interval. Positivity of U converts "
                        + "the resulting valuation bound into divisibility. For a first "
                        + "prime q>t, the existing upper bound r(q,1)<=lambda(q)<lambda(t) "
                        + "excludes its first exponent, hence the entire strict prefix. "
                        + "Tied prices are excluded by the original strict count law."))),
                DescribeRole.Theorem),
            Paragraph(Text("Correspondence on each unchanged original closed edge.")),
            Paragraph(Text(
                "On an original edge N_p=p*U and N_r=r*U, let A=log(p*U)<C=log(r*U). "
                + "The edge premise U=N(t) throughout the whole closed interval [A,C] "
                + "uses the same strict finite positive-layer product and supplies exactly "
                + "the valuation equality above at each t. Apply the theorem to this same "
                + "U whenever t>=243. Neither U nor the edge is reselected, and the complete "
                + "original interval union is preserved.")),
            Paragraph(Text(
                "Where this edge is used as part of the original selected source family, "
                + "retain 5040 dividing U, the least maximizing sources in the original "
                + "classes of multiples of 5040*p and 5040*r, and the labels p,r>2*R. "
                + "Those source premises do not enter the price or strict inventory "
                + "theorems. Equality with the strict core on the closed edge remains an "
                + "explicit premise; integer maximality at interpolated real centers "
                + "is not inferred from endpoint maximality.")),
            Paragraph(Text("Remaining signed comparison.")),
            Paragraph(Text(
                "This separation locates the negative higher reference phase in already "
                + "occupied layers. It does not bound the complete signed response from "
                + "below on the unchanged original selected family, does not remove the "
                + "large cancellation in the occupied subtraction, and does not prove "
                + "Robin's inequality or the Riemann hypothesis. The cofinal lower "
                + "coefficient I_X>=-kappa*M_X with kappa<(sqrt(2)-1)/4 remains unresolved.")))));
}
