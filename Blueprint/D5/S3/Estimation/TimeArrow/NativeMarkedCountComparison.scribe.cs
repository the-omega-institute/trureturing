using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeMarkedCountComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/TimeArrow/NativeMarkedCountComparison.";

    private static DocumentBlock Definition(string selector, string title, string text) =>
        Describe.Lean(DescribeId.Create("native-marked-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform comparison of native joint marked counts with independent categorical counts.",
        H("Native joint signal-count comparison"),
        Blocks(
            Paragraph(Text("Fix natural M,q with 1<=q<M, a real 0<r<1 satisfying rq/(M-q)<1, and a deterministic support S of cardinality q. The injection m from Fin(q) into Fin(M) takes all its values in S; since the cardinalities agree, it enumerates the whole support. The native observation is the original uniform-start path in Fin(M)+Fin(M), with s consecutive transitions and its actual probability. Both destination parity counts for every support row stay in one vector indexed by Fin(q)+Fin(q).")),
            Definition("rho", "Total marked probability", "rho(M,q)=q/(2M). Write n=2M and L=s/n; the theorem uses every natural s, including zero and one, with no restriction on L."),
            Definition("ap", "Positive marked increment", "ap(M,r)=(1+r)/(4M)=(1+r)/(2n). Each positive destination mark has this one-step probability."),
            Definition("am", "Negative marked increment", "am(M,r)=(1-r)/(4M)=(1-r)/(2n). Each negative destination mark has this one-step probability."),
            Definition("nativeCounts", "The full native count vector", "At coordinate inl(j), nativeCounts(m,o) is count(path,o,m(j),1); at inr(j), it is count(path,o,m(j),-1). Both use the same actual path and its consecutive edges."),
            Definition("incrementExponent", "One categorical count increment", "The unmarked symbol none contributes the zero vector; some(i) contributes one in coordinate i and zero elsewhere."),
            Definition("referenceIncrement", "The categorical reference increment law", "The alphabet is Option(Fin(q)+Fin(q)). Its none probability is 1-rho; some(inl(j)) has probability ap, and some(inr(j)) has probability am. Under the stated domain these values are nonnegative and their sum is one."),
            Definition("referenceCounts", "Categorical count aggregation", "For a reference sequence indexed by Fin(s), referenceCounts sums the categorical increment vectors. It records every mark coordinate as a natural count."),
            Definition("referenceWeight", "Independent reference sequence mass", "The reference mass of a sequence is the product of referenceIncrement over exactly s times. This gives independent categorical increments on the full mark alphabet; it introduces no prior on S."),
            Describe.Lean(DescribeId.Create("native-joint-count-comparison"),
                DeclarationHandle.Create(Prefix + "native_joint_count_comparison"),
                H("A uniform bound on every full joint count event"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every legal M,q,r,S, every such enumeration m, every natural s and every subset E of the entire natural count-vector space, the absolute difference between the native probability of nativeCounts in E and the independent reference probability of referenceCounts in E is at most 8*s*rho(M,q)^2. Each probability is the explicit finite sum of its actual history masses over the indicated event. No truncation of E, restriction to one or two rows, averaging over S, or additional distance from r=1 is assumed.")),
                    Paragraph(Text("The proof reuses MarkedPoissonCoefficient.actual_marked_path_transfer for arbitrary many marked rows and all complex tilts. Polynomial extensionality lifts that exact native PGF identity to the complete multivariate count polynomial. Its coefficient absolute-value sum is at most one because the native history probabilities are nonnegative and normalized by FiniteSupportSelectionBayes.finite_support_bayes.")),
                    Paragraph(Text("Write P=1+A for the one-step categorical polynomial and B for the signed endpoint-parity feedback polynomial. The coefficient norms satisfy norm(P)<=1, norm(A)<=2*rho and norm(B)<=beta, where beta=(1+r)*rho<1/2 follows from the original compensation condition. For the exact native two-component recursion (X,Y), the new invariant bounds norm(Y_s) by 2*beta. Multiplication by P contracts coefficient mass, so each additional step increases norm(X_s-P^s) by at most 8*rho^2. An induction gives the stated uniform law bound. Applying the linear indicator functional of any vector event is bounded by that coefficient mass. A finite product-sum identity identifies P^s with the actual categorical sequence mass used in the conclusion.")),
                    Paragraph(Text("This is the native-to-categorical intermediary. It does not establish the full product-Poisson conclusion of the source theorem or its remaining joint inference clauses. Composition with a separately proved categorical-to-Poisson comparison, and the rest of the parent atom, remain required. The argument establishes a mathematical bound in the stated finite experiment; it asserts no physical realization or literature novelty."))),
                DescribeRole.Theorem))));
}
