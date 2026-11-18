using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeProductPoissonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/TimeArrow/NativeProductPoisson.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quantitative full product Poisson comparison for the actual native signal-count vector.",
        H("Native full product Poisson comparison"), Blocks(
            Describe.Lean(DescribeId.Create("native-signal-rates"),
                DeclarationHandle.Create(Prefix + "signalRates"), H("Signal rates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural M,q and real r, signalRates(M,r) is the nonnegative rate vector indexed by Fin(q)+Fin(q). At inl(j) it is the nonnegative part of (1+r)/(4M); at inr(j) it is the nonnegative part of (1-r)/(4M). Under 1<=q<M and 0<r<1, these are the unmodified positive rates. Their total is rho=q/(2M). The final Poisson rate vector is s times this vector. With n=2M and L=s/n its positive and negative coordinates are exactly L(1+r)/2 and L(1-r)/2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("native-product-poisson"),
                DeclarationHandle.Create(Prefix + "native_product_poisson"),
                H("Every native full count event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every natural M,q,s, every real r with 1<=q<M, 0<r<1 and compensation(M,q,r)=rq/(M-q)<1, every S:Support(M,q), every injective m:Fin(q)->Fin(M) with all m(j) in S, and every subset E of ((Fin(q)+Fin(q))->Nat), the absolute difference between the sum over native path observations o of probability(r,path,S,o) when nativeCounts(m,o) belongs to E (and zero otherwise), and poissonProduct(j -> s*signalRates(M,r,j)).real(E), is at most 9*s*(q/(2M))^2. The native vector has coordinate count(path,o,m(j),1) at inl(j) and count(path,o,m(j),-1) at inr(j), on the identical original path. The target is the existing poissonProduct on the entire natural count-vector space. All natural times, including zero and one, and all support cardinalities allowed by the hypotheses are included.")),
                    Paragraph(Text("The exact bridge represents the categorical symbol law as a finite sum of weighted Dirac measures on Option(Fin(q)+Fin(q)). Mapping each symbol to its count increment gives CategoricalProductPoisson.categoricalIncrement at precisely signalRates. Mathlib's finite product pushforward identity followed by composition of measure maps identifies aggregation with NativeMarkedCountComparison.referenceCounts on the same symbol history. Expanding the finite product measure on singletons gives exactly the referenceWeight event sum used by NativeMarkedCountComparison.native_joint_count_comparison. No equality of laws is assumed.")),
                    Paragraph(Text("The quantitative proof consumes native_joint_count_comparison with its coefficient feedback invariant and categorical_product_poisson with its common submeasure and full product time aggregation. Their live estimates give 8*s*rho^2 and s*rho^2, respectively; the triangle inequality gives 9*s*rho^2. The finite measure bridge and the triangle step are applications of existing machinery; the new quantitative substance lies in the consumed kernel proofs. No additional mathematical novelty is asserted for composition.")),
                    Paragraph(Text("This establishes the finite known-forward continuous-path signal-vector comparison underlying equation (27.6) in PARITY_HIDDEN_ARROW_FLUCTUATIONS, uniformly over the actual support. It does not close the parent theorem 27.2. The independent-pair experiment, reversal and unknown-direction transfer, independent priority extension, asymptotic vanishing, mean transfer (27.7), posterior covariance and threshold comparisons (27.8)-(27.20), and the exact-risk-centered joint normal conclusion (27.3)-(27.4) remain separate obligations."))),
                DescribeRole.Theorem))));
}
