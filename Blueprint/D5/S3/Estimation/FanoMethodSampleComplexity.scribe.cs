using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class FanoMethodSampleComplexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent repetition turns a common-reference divergence ceiling into a lower bound on the number of observations required by every estimator.",
        H("Finite-Family Sample Complexity"),
        Blocks(
            Paragraph(Text(
                "Two earlier results answer adjacent questions: how many observations separate " +
                "two laws, and whether a family can be separated from a single observation. " +
                "This module joins them to answer the question an experiment actually asks: " +
                "how many observations are needed before any estimator can pick the true law " +
                "out of a finite family. The estimator is universally quantified, so these " +
                "bounds constrain every possible procedure rather than one chosen method.")),
            Paragraph(Text(
                "This wave is mostly composition. The uniform-mixture averaging equality and " +
                "exact KL power additivity are already frozen. The only new general proof work " +
                "propagates positivity and normalization through the n-fold construction, " +
                "transports the per-candidate divergence ceiling pointwise to n times D, and " +
                "performs a one-step inversion by a positive divisor. This is not new theory " +
                "disguised as composition. The mixture remains a hypothesis rather than a " +
                "definition, and the module adds no definitions.")),
            Paragraph(Text(
                "The information ceiling grows linearly in n, and that is the whole mechanism. " +
                "Each candidate's n-fold divergence from the n-fold reference is exactly n " +
                "times its single-observation divergence, so n observations carry at most n " +
                "times D information. Fano then says that the label cannot be resolved until " +
                "this ceiling exceeds the label entropy, which is precisely a lower bound on n. " +
                "The product form is primary and has no sign side condition; only the solved " +
                "form assumes 0 < D. This assumption is substantive. At D = 0, equality in " +
                "Gibbs' inequality together with strict positivity forces every candidate to " +
                "equal the reference and hence every other candidate, so no finite number of " +
                "observations can discriminate them.")),
            Paragraph(Text(
                "The hypotheses have collapsed, and the numerical regimes bite. Strict " +
                "positivity of the candidates and reference absorbs pointwise nonnegativity and " +
                "the discrete absolute-continuity obligation, so neither appears separately in " +
                "the public statements. With one thousand candidates, divergence at most one " +
                "tenth from a common reference, and one percent tolerated error, the computed " +
                "lower bound is 61.4553..., hence at least 62 observations. With four candidates " +
                "and unit tolerated error, the numerator is minus log two, so zero observations " +
                "already satisfy the bound and it imposes nothing, correctly, because an " +
                "estimator allowed to be wrong needs no data. The requirement grows like the " +
                "logarithm of the family size and the reciprocal of the divergence ceiling, and " +
                "shrinks as tolerated error grows. Both regimes must be visible: a bound that " +
                "binds nowhere would be worthless, while one that never becomes vacuous would " +
                "be wrong.")),
            Describe.Lean(
                DescribeId.Create("iid-information-is-bounded-by-average-reference-divergence"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethodSampleComplexity.mutual_information_iid_le_average_reference_divergence"),
                H("Average one-sample divergence controls n-sample information"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("I"), Open, F.Id("X"), Semi, Sp,
                    F.Id("Y"), Caret, Grp(F.Id("n")), Close,
                    Sp, Le, Sp,
                    F.Id("n"), Sp, Cdot, Sp, Open,
                    Frac, Grp(D(1)), Grp(Lvert, Sp, F.Id("X"), Sp, Rvert),
                    Sp, Cdot, Sp,
                    Sum, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("X")), Sp,
                    F.Id("D"), Open,
                    F.Id("P"), Underscore, Grp(F.Id("i")), Sp, Vert, Sp,
                    F.Id("Q"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the observation alphabet and label family be finite, let n be " +
                        "natural, and let p be a nonnegative normalized law on the n-fold " +
                        "observation space paired with the label. Let every candidate P_i and " +
                        "the reference Q be strictly positive and normalized. Assume pointwise " +
                        "that p(z,i) is the inverse cardinality of the label family times the " +
                        "n-fold power of P_i at z. Then the mutual information of p is at most n " +
                        "times the inverse family cardinality times the sum of the KL " +
                        "divergences from P_i to Q."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("uniform-one-sample-ceiling-controls-iid-information"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethodSampleComplexity.mutual_information_iid_le_uniform_reference_divergence"),
                H("A uniform one-sample ceiling gives the linear information budget"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("I"), Open, F.Id("X"), Semi, Sp,
                    F.Id("Y"), Caret, Grp(F.Id("n")), Close,
                    Sp, Le, Sp,
                    F.Id("n"), Sp, Cdot, Sp, F.Id("D")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same finite-space, n-fold mixture, nonnegative normalized " +
                        "joint-law, and strictly positive normalized candidate and reference " +
                        "hypotheses, let D be real and assume every KL divergence from P_i to Q " +
                        "is at most D. Then the mutual information of p is at most n times D. " +
                        "No sign condition on D is added."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("fano-method-gives-the-iid-minimax-product-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethodSampleComplexity.fano_method_iid_minimax_product_bound"),
                H("Fano's method gives the primary n-sample product bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, D(1), Sp, Minus, Sp, Varepsilon, Close,
                    Sp, Cdot, Sp,
                    Log, Sp, Lvert, Sp, F.Id("X"), Sp, Rvert,
                    Sp, Le, Sp,
                    F.Id("n"), Sp, Cdot, Sp, F.Id("D"),
                    Sp, Plus, Sp, Log, Sp, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the observation alphabet and label family be finite; let n, p, the " +
                        "candidate family, and the reference satisfy the preceding n-fold uniform " +
                        "mixture and probability-law hypotheses; and let g be any map from n " +
                        "observations to a label. For real D and epsilon, assume each candidate " +
                        "divergence to Q is at most D and that the p-mass of pairs on which g " +
                        "returns the wrong label is at most epsilon. Then one minus epsilon times " +
                        "log card X is at most n times D plus log two. There is no sign condition " +
                        "on D and no separate range condition on epsilon."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("fano-method-gives-the-iid-sample-complexity-floor"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethodSampleComplexity.fano_method_iid_sample_complexity_lower_bound"),
                H("Positive divergence gives the solved sample-complexity floor"),
                StatementSource.FromAuthor(Disp(Seq(
                    Frac,
                    Grp(
                        Open, D(1), Sp, Minus, Sp, Varepsilon, Close,
                        Sp, Cdot, Sp,
                        Log, Sp, Lvert, Sp, F.Id("X"), Sp, Rvert,
                        Sp, Minus, Sp, Log, Sp, D(2)),
                    Grp(F.Id("D")),
                    Sp, Le, Sp, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under exactly the finite-space, n-fold uniform mixture, probability-law, " +
                        "strict positivity, normalization, arbitrary-estimator, divergence-ceiling, " +
                        "and error-at-most-epsilon hypotheses of the product theorem, add 0 < D. " +
                        "Then the quotient of one minus epsilon times log card X minus log two by " +
                        "D is at most n. Positivity of D is the sole additional hypothesis and is " +
                        "used to preserve order when dividing."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("one-thousand-candidates-require-sixty-two-observations"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethodSampleComplexity.fano_method_thousand_candidates_one_percent"),
                H("One thousand close candidates require at least 62 observations"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(6, 1), Dot, D(4, 5, 5), Sp, Lt, Sp, F.Id("n"),
                    Sp, Land, Sp,
                    D(6, 2), Sp, Le, Sp, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the observation alphabet and label family be finite; let n, p, the " +
                        "strictly positive normalized candidate family and reference, the n-fold " +
                        "uniform mixture hypothesis, and an arbitrary estimator g be as above. " +
                        "Specialize the label cardinality to 1000, every candidate divergence " +
                        "ceiling to one tenth, and the estimator's error mass ceiling to one " +
                        "hundredth. The theorem proves jointly that 61.455 is strictly less than " +
                        "the real cast of n and that 62 is at most n."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("four-candidate-unit-error-regime-is-vacuous"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoMethodSampleComplexity.fano_method_four_candidates_unit_error_vacuous"),
                H("The four-candidate unit-error regime is vacuous"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, D(1), Sp, Minus, Sp, D(1), Close, Sp, Cdot, Sp,
                    Log, Sp, D(4), Sp, Le, Sp,
                    D(0), Sp, Cdot, Sp, Frac, Grp(D(1)), Grp(D(1, 0)),
                    Sp, Plus, Sp, Log, Sp, D(2),
                    Sp, Land, Sp,
                    Frac,
                    Grp(Open, D(1), Sp, Minus, Sp, D(1), Close, Sp, Cdot, Sp,
                        Log, Sp, D(4), Sp, Minus, Sp, Log, Sp, D(2)),
                    Grp(Frac, Grp(D(1)), Grp(D(1, 0))),
                    Sp, Lt, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "With no hypotheses, the compiled arithmetic specialization proves two " +
                        "facts jointly: at four candidates, zero samples, divergence one tenth, " +
                        "and unit tolerated error, the product inequality is satisfied; and the " +
                        "corresponding solved quotient is strictly negative. Thus the lower bound " +
                        "places no positive requirement on the sample count in this regime."))),
                DescribeRole.Theorem
            ))));
}
