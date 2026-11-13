using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class CommonOldExclusionConfirmationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/CommonOldExclusionConfirmation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One original confirmer controls every mixed input of the entire fixed old exclusion ball.",
        H("Common confirmation on an old complete exclusion"), Blocks(
        Describe.Lean(DescribeId.Create("full-effect-norm-bound"), DeclarationHandle.Create(Owner + "effectNormBound"),
            H("The actual full-interval dual norm maximum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The bound M is the maximum of the operator norm over the entire original effect interval. It is finite and attained. The auxiliary norm supplies distances and topology; it does not supply a physical inner product.")))),
        Describe.Lean(DescribeId.Create("whole-effect-maximum"), DeclarationHandle.Create(Owner + "wholeMaximum"),
            H("One effect on the entire specified set"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("wholeMaximum(G,e) is the supremum of e on all of G. On a nonempty compact G it is an attained maximum.")))),
        Describe.Lean(DescribeId.Create("common-effect-minimum"), DeclarationHandle.Create(Owner + "kappa"),
            H("Minimum before maximum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("kappa_G(a) minimizes wholeMaximum(G,e) over the complete original confirmer fiber F_a. The same effect e is used for every point of G. Both extrema are attained. No minimax interchange is made.")))),
        Describe.Lean(DescribeId.Create("old-ball-chart"), DeclarationHandle.Create(Owner + "oldChart"),
            H("A full original chart"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("An arbitrary chart is chosen from the exact original EB3 hypothesis. No regularity of this choice is assumed.")))),
        Describe.Lean(DescribeId.Create("old-ball-center"), DeclarationHandle.Create(Owner + "oldCenter"),
            H("The old complete ball's center"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The chosen affine chart maps zero to the old center c_p. Reflection preserves the whole ball. The main theorem proves that every symmetry center equals this point, so the center is independent of the chart.")))),
        Describe.Lean(DescribeId.Create("actual-full-zero-effects"), DeclarationHandle.Create(Owner + "fullZeroEffects"),
            H("The actual full-zero confirmer family"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("A_p is exactly the continuous-dual representation of FixedZeroObstruction.fullZeroConfirmers: an original full-interval effect confirming p and vanishing at every mixed point of the complete D_p.")))),
        Describe.Lean(DescribeId.Create("actual-fiber-distance"), DeclarationHandle.Create(Owner + "zeroFiberDistance"),
            H("Distance from a complete confirmer fiber"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The distance is the minimum, over all e in the whole F_a, of the actual dual norm distance from e to the whole A_p. The outer minimum is attained. No specified effect or selector is part of this definition.")))),
        Describe.Lean(DescribeId.Create("complete-old-exclusion-confirmation"),
            DeclarationHandle.Create(Owner + "common_old_exclusion_confirmation"),
            H("Complete original X125.2 and X125.3"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("The carrier V is arbitrary finite dimensional real normed space. C is the same closed pointed generating cone, u is the same functional strictly positive on its nonzero vectors, K is all of C intersect {u=1}, P is all of ext(K), and the comparison is the minimum over all original effects confirming its first argument. Only EB3 and reciprocity on original pure pairs are assumed. In particular there is no weakPair, Inj, least-effect, noncollapse, finite extension budget, closed-pure assumption or global continuity input.")),
            Paragraph(Text("For every nonempty compact convex centrally symmetric G contained in K and every original pure a, kappa_G(a) is attained by one e in F_a at an attained maximizing point x of G, with every y in G bounded by e(x) and every competing confirmer's whole maximum bounded below by kappa. Its exact sandwich is T_a(c)<=kappa_G(a)<=2T_a(c). For every original pure a_n tending to p, with the fixed old G=D_p, kappa_G(a_n), T_a_n(c_p), and the supremum of T_a_n(x) over every mixed x in G all tend to zero.")),
            Paragraph(Text("At every index, kappa_G(a_n)<=M d_H(D_a_n,G), which in particular gives the requested quantitative bound when the actual whole balls converge to G. If the actual entire D_a_n converge to a singleton {q}, the theorem proves q belongs to P intersect G. Eventually a single e_n in F_a_n simultaneously satisfies max_G e_n<=M(norm(a_n-p)+d_H(D_a_n,{q})) and e_n(c_p)<=M/2 times the same sum. These are eventual quantifiers, the old center, both exact constants, and the same actual effect for all mixed inputs.")),
            Paragraph(Text("The single-effect estimate chooses an actual minimizer at the old pure antipode r of q. Pure PR and a fixed original confirmer at r give T_a_n(r)<=M norm(a_n-p). Once this is below one, original normalized_effect proves that every such minimizer has a zero in K: otherwise subtract its positive attained minimum times u and normalize to obtain a strictly smaller original confirmer value. The zero lies in D_a_n, so the actual Hausdorff singleton distance bounds its distance to q. The effect norm bounds e_n(q); the antipodal sum gives twice e_n(c_p)=e_n(q)+e_n(r), and reflection bounds every old mixed input by twice the same center value. The zero set of this effect is never identified with D_a_n.")),
            Paragraph(Text("Compactness of the hyperspace of nonempty compact subsets of K supplies a converging subsubsequence of the actual complete exclusions inside every subsequence. The exact PR-domain whole-ball or pure-singleton alternative exhausts those limits. The preceding same-effect estimates force kappa to zero in both branches. Positivity and the attained common effect then bound the center value and the entire mixed-input supremum by kappa. No mixed-state PR and no affine comparison function is used.")),
            Paragraph(Text("A_p is nonempty, compact, convex, exposed in F_p, and proper. It is exactly {e in F_p:e(c_p)=0}. Every member has actual zero set in K equal to the entire D_p, directly from the full original confirmer and exclusion definitions. No Inj-dependent full_zero_faces package is used. Evaluation at c_p exposes the face, and u belongs to F_p with value one there, proving properness.")),
            Paragraph(Text("For every Hausdorff limit F_a_n to A of the whole confirmer fibers, A is contained in F_p and A meets A_p. Joint evaluation preserves the confirming equation. Effects attaining kappa have every cluster point in A_p, and a prescribed whole-fiber limit contains the same cluster point. Without selecting a fiber limit, the attained minimum dual distance from F_a_n to A_p tends to zero. The conclusions supply neither A=F_p nor A contained in A_p, convergence to a prescribed confirmer, or a continuous selection.")),
            Paragraph(Text("For an application in every original carrier, fix any original pure p0 and any of its complete three-ball charts f. In the chart domain choose coordinate unit vectors v0 and v1, put t_n=1/(n+1), and normalize v0+t_n v1 to x_n. Then x_n lies on the sphere, tends to v0, and differs from v0 at every index. The original boundary theorem and chart injectivity give original pure labels a_n=f(x_n) and p=f(v0), with a_n tending to p and a_n different from p for every n. Their original self-comparisons equal one. Applying the complete theorem to this sequence gives all three old-ball limits and the whole-fiber distance limit. This application uses arbitrary ambient V and the complete original domains; it uses no constant label sequence or extra continuity premise.")),
            Paragraph(Text("This formal result keeps all clauses of X125.2 and X125.3 together with their original prerequisite interfaces. It does not prove automatic CS, UF or NC, and makes no operational, composite, dynamical, or physical realization claim. Compactness, norm bounds, normalization, affine reflection, extrema, zero-set reduction and generic ball rigidity are reused tools; they are not independent new content or originality claims."))), DescribeRole.Theorem)
        )));
}
