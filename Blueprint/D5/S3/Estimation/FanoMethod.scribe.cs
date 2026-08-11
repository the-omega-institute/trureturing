using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class FanoMethodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniformly mixed family that stays close to one common reference cannot be reliably distinguished by any estimator; the exact KL averaging identity is the substantive step behind the resulting Fano bounds.",
        H("Fano's Method for a Finite Family"),
        Blocks(
            Paragraph(Text(
                "The Estimation arc so far asked whether two laws can be told apart. Fano's " +
                "method asks the same question of a finite family. Many candidates that are " +
                "all close to one common reference cannot be told apart, regardless of which " +
                "estimator is used. The estimator is universally quantified, so the conclusion " +
                "belongs to the estimation problem rather than to a particular procedure.")),
            Paragraph(Text(
                "The genuine content is an averaging equality; everything after it is " +
                "composition. Under the uniform mixture hypothesis, the joint mass at an " +
                "observation and candidate is the inverse candidate count times that " +
                "candidate's observation mass. Divergence from an arbitrary product reference " +
                "is then exactly the average of the candidate divergences, because the common " +
                "inverse-count factors cancel inside the logarithm. The proof first derives the " +
                "hidden marginal from the mixture hypothesis and normalization of every " +
                "candidate; it does not assume that marginal separately. The cancellation also " +
                "covers vanishing candidate masses. The mixture is a hypothesis, not a new " +
                "definition, so this module adds no definitions and composes directly with the " +
                "frozen theorems stated for a bare joint law.")),
            Paragraph(Text(
                "The frozen any-reference bound turns the equality into a mutual-information " +
                "upper bound by the average candidate divergence. Bounding every summand by a " +
                "single ceiling D gives the usable information budget, and frozen counting Fano " +
                "then gives the minimax product inequality. That product form has no cardinality " +
                "or epsilon side condition. Only the solved error form assumes at least two " +
                "candidates, exactly so the logarithm of the candidate count is positive and " +
                "division preserves the inequality.")),
            Paragraph(Text(
                "The numerical specializations show both when the method bites and when it " +
                "correctly becomes vacuous. With four candidates and divergence ceiling one " +
                "tenth, the quotient is approximately 0.572135, leaving every estimator's error " +
                "strictly above 0.427865, or about 42.7865 percent. For a large ceiling such as " +
                "three halves, the same solved expression is negative and imposes no constraint, " +
                "as it should when candidates far from the reference may be distinguishable. " +
                "The compiled vacuous theorem uses the exact budget log four and obtains the " +
                "exact floor minus one half. Both regimes matter: a bound positive in no regime " +
                "would be worthless, while a bound that never became vacuous would be wrong.")),
            Describe.Lean(
                DescribeId.Create("uniform-mixture-divergence-is-the-average"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethod.kl_divergence_uniform_mixture_eq_average"),
                H("Uniform-mixture divergence is exactly the candidate average"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("D"), Open,
                    F.Id("p"), Sp, Vert, Sp,
                    F.Id("Q"), Sp, Cdot, Sp,
                    F.Id("m"), Underscore, Grp(F.Id("X")), Close,
                    Sp, Eq, Sp,
                    Frac, Grp(D(1)), Grp(Lvert, Sp, F.Id("X"), Sp, Rvert),
                    Sp, Cdot, Sp,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("X")), Sp,
                    F.Id("D"), Open,
                    F.Id("P"), Underscore, Grp(F.Id("i")), Sp, Vert, Sp,
                    F.Id("Q"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X and Y be finite. Let p be a nonnegative normalized law on Y x X; " +
                        "let each P_i be a nonnegative normalized law on Y; and let Q be strictly " +
                        "positive and normalized on Y. Assume pointwise that p(y,i) is the inverse " +
                        "cardinality of X times P_i(y). Then the KL divergence of p from the " +
                        "product of Q and p's hidden-coordinate marginal equals the inverse " +
                        "cardinality of X times the sum over i of the KL divergences from P_i to " +
                        "Q. This is an equality, not merely an upper bound, and its proof derives " +
                        "the hidden marginal before cancelling the shared mixture factor."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("mutual-information-is-bounded-by-average-reference-divergence"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethod.mutual_information_le_average_reference_divergence"),
                H("Average reference divergence bounds mutual information"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("I"), Open, F.Id("X"), Semi, Sp, F.Id("Y"), Close,
                    Sp, Le, Sp,
                    Frac, Grp(D(1)), Grp(Lvert, Sp, F.Id("X"), Sp, Rvert),
                    Sp, Cdot, Sp,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("X")), Sp,
                    F.Id("D"), Open,
                    F.Id("P"), Underscore, Grp(F.Id("i")), Sp, Vert, Sp,
                    F.Id("Q"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under exactly the same finite-space, probability-law, positive " +
                        "normalized reference, and uniform-mixture hypotheses as the averaging " +
                        "equality, the mutual information of p is at most the average divergence " +
                        "from the candidates P_i to Q. The proof composes the frozen " +
                        "any-reference mutual-information bound with the preceding equality; it " +
                        "introduces no further hypothesis."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("uniform-reference-ceiling-bounds-mutual-information"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethod.mutual_information_le_uniform_reference_divergence"),
                H("A uniform reference ceiling bounds mutual information"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("I"), Open, F.Id("X"), Semi, Sp, F.Id("Y"), Close,
                    Sp, Le, Sp, F.Id("D")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X, Y, p, the candidate family, and Q satisfy the same hypotheses as " +
                        "the averaging equality, and let D be real. Add the pointwise ceiling " +
                        "that every candidate divergence from P_i to Q is at most D. Then the " +
                        "mutual information of p is at most D. This is the average bound relaxed " +
                        "by finite summation; the theorem assumes no separate sign condition on " +
                        "D."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("fano-method-gives-the-minimax-product-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethod.fano_method_minimax_product_bound"),
                H("Fano's method gives the minimax product bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, D(1), Minus, Varepsilon, Close,
                    Sp, Cdot, Sp,
                    Log, Sp, Lvert, Sp, F.Id("X"), Sp, Rvert,
                    Sp, Le, Sp,
                    F.Id("D"), Plus, Sp, Log, Sp, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X and Y be finite; let p, the candidate family P_i, and the positive " +
                        "normalized reference Q satisfy the uniform-mixture hypotheses; and let " +
                        "g from Y to X be arbitrary. If every candidate divergence to Q is at " +
                        "most D and the p-mass of pairs on which g(y) differs from i is at most " +
                        "epsilon, then the product of one minus epsilon and log card X is at most " +
                        "D plus log two. Neither a lower bound on card X nor any range condition " +
                        "on epsilon is assumed."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("fano-method-gives-the-minimax-error-floor"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethod.fano_method_minimax_error_lower_bound"),
                H("Fano's method gives the solved minimax error floor"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(1), Minus,
                    Frac,
                    Grp(F.Id("D"), Plus, Sp, Log, Sp, D(2)),
                    Grp(Log, Sp, Lvert, Sp, F.Id("X"), Sp, Rvert),
                    Sp, Le, Sp, Varepsilon))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the finite-space, probability-law, positive normalized reference, " +
                        "uniform-mixture, candidate-divergence-ceiling, arbitrary-estimator, and " +
                        "error-at-most-epsilon hypotheses of the product theorem, add exactly " +
                        "that card X is at least two. Then epsilon is at least one minus the " +
                        "ratio of D plus log two to log card X. The added cardinality hypothesis " +
                        "makes the denominator positive; no other hypothesis is added."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("four-candidate-small-divergence-regime-is-informative"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethod.fano_method_four_candidates_informative"),
                H("Four close candidates force a positive error floor"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, D(1), Minus, Varepsilon, Close,
                    Sp, Cdot, Sp, Log, Sp, D(4),
                    Sp, Le, Sp,
                    Frac, Grp(D(1)), Grp(D(1, 0)),
                    Plus, Sp, Log, Sp, D(2),
                    Sp, Land, Sp,
                    D(0), Dot, D(4, 2, 7, 8, 6, 5),
                    Sp, Lt, Sp, Varepsilon))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X and Y be finite and satisfy the same probability-law, positive " +
                        "normalized reference, uniform-mixture, arbitrary-estimator, and " +
                        "error-at-most-epsilon hypotheses as above. Specialize card X to four " +
                        "and every candidate divergence ceiling to one tenth. The theorem proves " +
                        "both the specialized product inequality and the strict numerical " +
                        "conclusion that 0.427865 is less than epsilon."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("four-candidate-large-budget-regime-is-vacuous"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethod.fano_method_four_candidates_vacuous"),
                H("The four-candidate bound becomes vacuous at a large budget"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, D(1), Minus, Varepsilon, Close,
                    Sp, Cdot, Sp, Log, Sp, D(4),
                    Sp, Le, Sp,
                    Log, Sp, D(4), Plus, Sp, Log, Sp, D(2),
                    Sp, Land, Sp,
                    D(1), Minus,
                    Frac,
                    Grp(Log, Sp, D(4), Plus, Sp, Log, Sp, D(2)),
                    Grp(Log, Sp, D(4)),
                    Sp, Le, Sp, Varepsilon))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every nonnegative real epsilon, the budget log four satisfies both " +
                        "the four-candidate product inequality and its solved error inequality. " +
                        "Here the solved lower floor is exactly minus one half, so the second " +
                        "inequality follows from nonnegativity and imposes no positive error " +
                        "constraint. This compiled arithmetic theorem takes only epsilon and its " +
                        "nonnegativity proof as hypotheses; it does not quantify a joint law, a " +
                        "candidate family, a reference, or an estimator."))),
                DescribeRole.Theorem
            ))));
}
