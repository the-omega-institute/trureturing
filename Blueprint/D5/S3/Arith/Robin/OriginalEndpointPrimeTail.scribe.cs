using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalEndpointPrimeTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalEndpointPrimeTail.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-price prime tails for the original strict and maximal resource optimizers.",
        H("Original endpoint prime tails"),
        Blocks(
            Paragraph(Text(
                "Both original endpoints, all positive prices, all primes and layers, "
                + "and simultaneous ties are retained. "
                + "The strict EndpointRobinEstimates sign and the original global Robin goal remain open.")),
            Describe.Lean(
                DescribeId.Create("original-all-price-tail"),
                DeclarationHandle.Create(Prefix + "original_endpoint_prime_tail_supply"),
                H("Sharp local prices, the exact residual, and a uniform same-integer tail estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The r4463 source supplier is reused with attribution to its r4454 scalar sandwich. At either original endpoint the complete finite Euler tail lies between the sums of the sharp local prices L and U and is at most 7/(2*sqrt(u)), where u is this endpoint's own largest prime. The retained quantitative proof uses endpoint_small and the adaptive small/large support split, including the small-u and empty-support branches. The exact factorization keeps A=log(N). No lcm transfer, finite layer cap, arithmetic certificate or final-sign hypothesis is used.")),
                    Paragraph(Text("For each real q>0 and either original endpoint N, let S=N.primeFactors, a_p=N.factorization(p), m(p,k)=goldenLayerMarginal p k, u=largestPrime(N), A=log N, z_p=exp(q log p), t_p=-log(1-p^(-(a_p+1))), L_p=log((p z_p-1)/((p-1)z_p)) and T=sum_S t_p. All sums use this endpoint's complete support and all its layers. Let C be {p in S : m(p,2)<=q} at the strict endpoint and {p in S : m(p,2)<q} at the maximal endpoint; put H=S\\C. Among primes in S, a_p>=1. The exact k=2 classifier makes p in C equivalent to not(2<=a_p), hence to a_p=1, with the stated strict/weak tie conventions. Thus H consists exactly of the support primes with a_p>=2.")),
                    Paragraph(Text("Set c_p=-log(1-p^-2), B=sum_C c_p+sum_H L_p and J=sum_H(t_p-L_p). On C, t_p=c_p exactly and the retained local sandwich gives L_p<=c_p. On H, the retained local sandwich gives t_p-L_p>=0. Consequently sum_S L_p<=B, J>=0 and T=B+J, by adding c_p+0=t_p on C and L_p+(t_p-L_p)=t_p on H. In particular B<=T and margin(N)=E3(u)+B+log(log A)-log(log u)+J. No higher-layer term has been discarded.")),
                    Paragraph(Text("For any active strict-endpoint prime with a_p=1, strict selection gives q<m(p,1), hence 1<z_p<1+1/p. Here p>=2 and z_p>1, so 1-p^-2 and all displayed denominators are positive. Logarithmic algebra gives")),
                    Paragraph(Text("c_p-L_p = log(p^2 z_p / ((p+1)(p z_p-1))) > 0,")),
                    Paragraph(Text("because p^2 z_p-(p+1)(p z_p-1)=p+1-p z_p>0. To produce the original above-5040 family, first choose any prime p>5040, then set q_p=m(p,2) and N_p=strictInteger(q_p). Existing marginal positivity and layer strict decrease give q_p>0 and q_p<m(p,1). The k=1 classifier selects p and the k=2 classifier excludes its second layer, so a_p=1 and p divides N_p. The original strictInteger_pos also gives N_p>0; hence N_p>=p>5040. This p supplies a strictly positive summand in B-sum_S L_p, while every other summand is nonnegative. Infinitely many primes p>5040 give this family of pairs (q_p,p); no claim of infinite support at a fixed q is made. At a maximal first-layer tie, z_p=1+1/p and the displayed difference is zero, so this strict-gain assertion is not transferred to every maximal tie.")),
                    Paragraph(Text("The existing same-integer prime-prefix identity gives log(1-1/p)+c_p=-log(1+1/p) on C and log(1-1/p)+L_p=log(1-1/(p z_p)) on H. The prime-local logarithm arguments are positive. On the original Robin domain N>5040, A>1 and u>=2 also give the usual analytic domains for the iterated logarithms; outside that domain the original total Lean logarithm conventions remain. The support-prefix identity is E3(u)=gamma+log(log u)+sum_S log(1-1/p), so substituting T=B+J and cancelling log(log u) gives")),
                    Paragraph(Text("(5) margin(N) = gamma + log(log A) - sum_C log(1+1/p) + sum_H log(1-1/(p z_p)) + J, (6) log(sigma(N)/N) <= sum_C log(1+1/p) - sum_H log(1-1/(p z_p)).")),
                    Paragraph(Text("Indeed the exact Euler identity gives log(sigma(N)/N)=sum_C log(1+1/p)-sum_H log(1-1/(p z_p))-J; dropping only the nonpositive term -J proves (6). Thus (5) is an identity and (6) is its abundancy bound.")),
                    Paragraph(Text("These are the original lower-control and equivalent prime-log derivations, not new canonical theorem bindings. Their exact original statements and Lean proof bodies remain transient. The remaining original obligation is strict positivity of E3(u)+T+log(log A)-log(log u) at both endpoints for every q>0 with strictInteger(q)>5040. J>=0 or a local strict gain does not prove that sign. Positivity of E3(u)+B+log(log A)-log(log u) would be sufficient, but is neither necessary nor proved here. The sharp upper-tail estimate cannot supply a lower sign."))),
                DescribeRole.Lemma))));
}
