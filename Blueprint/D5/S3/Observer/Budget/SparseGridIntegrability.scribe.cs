using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class SparseGridIntegrabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual sparse-grid rounding preserves finite positive-integer first moments "
            + "under every probability law exactly when its rounding ratio is bounded.",
        H("All-Law Integrability of Sparse-Grid Waiting"),
        Blocks(
            Paragraph(Text(
                "A Grid is an arbitrary strictly increasing sequence depth:N->N with depth(0)=0. "
                    + "Strict increase implies depth(j)>=j and hence unboundedness; no computability "
                    + "assumption is imposed. Write n_j=depth(j). The function m(n)=round(S,n) "
                    + "is the actual least n_j>=n, selected by the least such index. It is also "
                    + "defined at zero, where it equals zero. For positive n in (n_j,n_(j+1)], "
                    + "m(n)=n_(j+1). All ratios below have positive denominators.")),
            Paragraph(Text(
                "C=ratio(S) is the extended nonnegative supremum of m(n)/n over n>=1. "
                    + "D=segmentRatio(S) is the supremum of n_(j+1)/(n_j+1) over j>=0. "
                    + "Least(S) abbreviates: for every n, n<=m(n), and for every retained n_j>=n, "
                    + "m(n)<=n_j. Fixed(S) says m(n_j)=n_j for all j.")),
            Paragraph(Text(
                "AllLaw(S) quantifies over every probability space in an arbitrary universe and "
                    + "every measurable T with values in N and T(x)>=1 everywhere: integrability "
                    + "of the real-valued T implies integrability of the real-valued m(T). "
                    + "Because these variables are nonnegative, this is exactly finiteness of "
                    + "their extended first moments. BigO(S) means m(n)=O(n) at the natural "
                    + "atTop filter. LinearBound(S) supplies one finite nonnegative real C with "
                    + "m(n)<=C*n for every n, including zero.")),
            Describe.Lean(
                DescribeId.Create("sparse-grid-integrability"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/SparseGridIntegrability.sparse_grid_integrability"),
                H("The all-law criterion for the actual least retained depth"),
                StatementSource.FromAuthor(Criterion()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On each positive segment the numerator m(n) is constant and the "
                            + "denominator increases, so its maximal ratio is attained at n_j+1. "
                            + "This proves C=D. A finite C gives a global linear bound, which "
                            + "preserves integrability by domination on every probability space. "
                            + "Conversely an eventual BigO bound absorbs finitely many initial "
                            + "ratios; zero contributes no exception. For necessity, the common "
                            + "law in the following theorem violates all-law preservation. "
                            + "The arbitrary-universe application lifts that same natural-valued "
                            + "law and replaces the null depth-zero input by one."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For a strictly increasing sequence t(k)>=2, k>=0, put "
                    + "w(k)=1/(4*(k+1)^2*t(k)). Define atomicLaw(t) as the sum of the Dirac "
                    + "mass w(k) at each t(k), plus the residual mass 1-sum_k w(k) at one. "
                    + "DepthCubic(S,t) means t(k)>=2 and (k+1)^3*t(k)<=m(t(k)) for every k. "
                    + "AtomicMoments(S,t) means: this is a probability measure, sum_k w(k)<=1/4, "
                    + "its singleton masses at one and t(k) are exactly the specified masses, "
                    + "its original first moment is at least one, at most "
                    + "1+(1/4)*sum_k 1/(k+1)^2 and finite, and its rounded first moment is infinity.")),
            Paragraph(Text(
                "PrefixRealization(S,t) has the following full meaning. For every finite "
                    + "measurable alphabet A with measurable singletons, decidable equality, and "
                    + "distinct letters zero and one, F consists of replicate(n,one) followed by "
                    + "zero, for every n>=0. The path depthPath(zero,one,r) has one at positions "
                    + "i with i+1<r and zero thereafter. codeTime is the infimum of n+1 for "
                    + "which all earlier letters are one and letter n is zero; it is infinity "
                    + "if no such prefix exists. The theorem proves both this exact no-hit "
                    + "equivalence and its list-prefix characterization. For every r>=1, "
                    + "codeTime(depthPath(r))=r.")),
            Paragraph(Text(
                "The code has exactly one word at each positive depth, is prefix-free, excludes "
                    + "the empty word, and satisfies the existing Coding Legal(b,F) interface "
                    + "whenever b(n)>=1 for every positive n. prefixLaw is the pushforward of "
                    + "atomicLaw(t) under depthPath, so it is one probability law, with masses "
                    + "on 1^(t(k)-1)00... and residual mass on 000.... Its pushforward under "
                    + "codeTime equals the pushforward of atomicLaw(t) under the natural-number "
                    + "embedding into the extended nonnegative reals. The original first moments "
                    + "are equal; the prefix rounded moment is infinity. extendedRound fixes "
                    + "infinity and agrees with m on natural inputs; its floor convention on "
                    + "other finite real inputs is immaterial to these integer-valued times. "
                    + "With finite discrete A these measurable path laws are Borel laws. "
                    + "For alphabets containing other letters, codeTime is the actual hit of F, "
                    + "so a preceding third letter prevents a later zero from being a code hit.")),
            Describe.Lean(
                DescribeId.Create("common-law-prefix-witness"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/SparseGridIntegrability.common_law_prefix_witness"),
                H("One common separating law and its actual prefix realization"),
                StatementSource.FromAuthor(Witness()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An unbounded ratio remains unbounded beyond every finite depth. "
                            + "Recursive choice therefore gives strictly increasing t(k)>=2 "
                            + "satisfying DepthCubic. The inverse-square estimate sum_{k>=1} "
                            + "k^(-2)<=2 is reused from Mathlib's telescoping bound. Thus "
                            + "sum w(k)<=1/4, while w(k)*t(k)=1/(4*(k+1)^2) is summable. "
                            + "Each rounded contribution is at least (k+1)/4, so summability "
                            + "of the rounded moments would imply summability of the nonzero "
                            + "constant 1/4, a contradiction. Dirac integration and measurable "
                            + "pushforward transport then establish the same-law prefix moments."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The necessity quantifier ranges over all laws. In the prefix model it applies "
                    + "when the strategy class admits this first-zero code and the common laws "
                    + "above. It classifies neither a fixed iid source nor every restrictive "
                    + "budget. If stopping is permitted only at one finite depth N, finite "
                    + "original mean forces stopping there almost surely and the delayed mean "
                    + "is the finite m(N) for any grid. A zero budget admits only the empty code, "
                    + "whose infinite stopping time makes the finite-mean premise vacuous. "
                    + "The bounded-ratio sufficiency applies to every allowed strategy. If a "
                    + "strategy already stops only at retained depths, Fixed(S) gives unchanged "
                    + "waiting time even when C is infinite.")),
            Paragraph(Text(
                "For a fixed source and strategy, section 7.9's criterion remains the weighted "
                    + "tail identity: E[m(T)] equals sum_{j>=0} "
                    + "(n_(j+1)-n_j)*Pr(T>n_j), with both sides extended nonnegative and no "
                    + "finite-mean premise. Pathwise the corresponding indicator sum telescopes "
                    + "to m(T); for a no-hit infinite T, unboundedness makes the sum infinite. "
                    + "Tonelli, supplied by MeasureTheory.lintegral_tsum, exchanges this "
                    + "nonnegative sum and integral. Thus finiteness of this weighted tail "
                    + "sum is the exact fixed-law test. The unweighted sum Pr(T>n_j) measures "
                    + "observation stages instead of original waiting steps. This is reused "
                    + "exposition, not an additional Lean theorem in this module.")),
            Paragraph(Text(
                "The mathematical source is Proposition 7.7 in "
                    + "RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION, with sections "
                    + "7.1, 7.2, 7.9 and 7.15 supplying the grid, full-prefix and applicability "
                    + "conventions. Existing PrefixFreeCode and DepthBudgetIidGreedyOptimality "
                    + "own the code interfaces. Pinned Mathlib owns the asymptotic bound, "
                    + "p-series, atomic-integral, summability and pushforward facts used here. "
                    + "The construction is a formalization of that source criterion; it makes "
                    + "no literature novelty or computational complexity claim.")))));

    private static Formula All(Formula x, Formula domain, Formula body) =>
        Seq(Forall, Sp, x, Sp, Colon, Sp, domain, Comma, Sp, body);

    private static Formula Criterion()
    {
        Formula s = F.Id("S"), c = Call("ratio", s);
        return Disp(All(s, F.Id("Grid"), Seq(
            c, Sp, Eq, Sp, Call("segmentRatio", s), Sp, Land, Sp,
            Call("Least", s), Sp, Land, Sp, Call("Fixed", s), Sp, Land, Sp,
            Grp(Seq(c, Sp, Lt, Sp, Infty, Sp, Iff, Sp, Call("BigO", s))), Sp, Land, Sp,
            Grp(Seq(c, Sp, Lt, Sp, Infty, Sp, Iff, Sp, Call("AllLaw", s))))));
    }

    private static Formula Witness()
    {
        Formula s = F.Id("S"), t = F.Id("t");
        return Disp(All(s, F.Id("Grid"), Seq(Call("ratio", s), Sp, Eq, Sp, Infty,
            Sp, Implies, Sp, Exists, Sp, t, Comma, Sp,
            Call("StrictMono", t), Sp, Land, Sp, Call("DepthCubic", s, t), Sp, Land, Sp,
            Call("AtomicMoments", s, t), Sp, Land, Sp, Call("PrefixRealization", s, t))));
    }
}
