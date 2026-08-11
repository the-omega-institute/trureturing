using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class FanoReferenceDivergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive normalized observation reference gives computable divergence forms of finite Fano, and the observation marginal attains the resulting family of bounds.",
        H("Finite Fano with an Arbitrary Observation Reference"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mutual-information-is-bounded-by-reference-divergence"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoReferenceDivergence.mutual_information_le_product_reference_divergence"),
                H("Reference divergence upper-bounds mutual information"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This instance-level module is separate from the general counting module " +
                        "because it depends on the frozen instance-level DemonIdentity. SL-010 " +
                        "forbids the general artifact from importing that fact: generality is " +
                        "bounded above by the complete dependency closure. The general side's " +
                        "independently checked transitive closure contains fourteen modules, all " +
                        "general, and does not contain DemonIdentity. The two documents therefore " +
                        "record a dependency-layer split of material that began in one module.")),
                    Paragraph(Text(
                        "Let X and Y be finite. Let p be a nonnegative mass function on Y x X " +
                        "with total mass one, and let u on the observation coordinate Y be " +
                        "strictly positive and normalized by sum_y u(y) = 1. With m_X denoting " +
                        "the hidden-coordinate marginal of p, the theorem states")),
                    new DocumentBlock.DisplayFormula(Seq(
                        F.Id("I"), Open, F.Id("X"), Semi, Sp, F.Id("Y"), Close,
                        Sp, Le, Sp,
                        F.Id("D"), Open,
                        F.Id("p"), Sp, Vert, Sp,
                        F.Id("u"), Sp, Cdot, Sp,
                        F.Id("m"), Underscore, Grp(F.Id("X")), Close)),
                    Paragraph(Text(
                        "The frozen DemonIdentity already decomposes the reference divergence as")),
                    new DocumentBlock.DisplayFormula(Seq(
                        F.Id("D"), Open,
                        F.Id("p"), Sp, Vert, Sp,
                        F.Id("u"), Sp, Cdot, Sp,
                        F.Id("m"), Underscore, Grp(F.Id("X")), Close,
                        Eq,
                        F.Id("I"), Open, F.Id("X"), Semi, Sp, F.Id("Y"), Close,
                        Plus, Sp,
                        F.Id("D"), Open,
                        F.Id("m"), Underscore, Grp(F.Id("Y")), Sp, Vert, Sp,
                        F.Id("u"), Close)),
                    Paragraph(Text(
                        "Discarding the marginal-to-reference term by Gibbs nonnegativity is " +
                        "the entire proof. The inequality is a one-line consequence of an " +
                        "already-frozen theorem, not a new inequality. Its value is that the " +
                        "reference u is free, so the resulting Fano floor can be computed from a " +
                        "joint-to-product-reference divergence without separately evaluating " +
                        "mutual information.")),
                    Paragraph(Text(
                        "The inequality has a strictly stronger hypothesis than the identity " +
                        "from which it comes. The identity needs u only strictly positive. The " +
                        "inequality also needs u normalized, because Gibbs nonnegativity applies " +
                        "only when both arguments are genuine distributions. On a one-point " +
                        "space the unit mass compared with the positive constant reference two " +
                        "has the kernel-checked value")),
                    new DocumentBlock.DisplayFormula(Seq(
                        F.Id("D"), Open, D(1), Sp, Vert, Sp, D(2), Close,
                        Eq, Minus, Log, Sp, D(2), Lt, D(0))),
                    Paragraph(Text(
                        "Numerically this is 1 times log(1/2), or -0.693147, so discarding that " +
                        "term would reverse the intended inequality. Strict positivity serves a " +
                        "different purpose: in the finite setting it supplies discrete absolute " +
                        "continuity for free."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("observation-marginal-attains-the-reference-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoReferenceDivergence.exists_observation_marginal_reference_attaining"),
                H("The observation marginal attains the reference bound"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p again be a nonnegative normalized law on finite Y x X, and assume " +
                        "in addition that its observation marginal m_Y is strictly positive at " +
                        "every y. Then there exists a strictly positive normalized reference u " +
                        "whose product-reference divergence equals the mutual information. The " +
                        "witness is the observation marginal itself:")),
                    new DocumentBlock.DisplayFormula(Seq(
                        F.Id("u"), Eq,
                        F.Id("m"), Underscore, Grp(F.Id("Y")), Comma, Sp,
                        F.Id("D"), Open,
                        F.Id("p"), Sp, Vert, Sp,
                        F.Id("u"), Sp, Cdot, Sp,
                        F.Id("m"), Underscore, Grp(F.Id("X")), Close,
                        Eq,
                        F.Id("I"), Open, F.Id("X"), Semi, Sp, F.Id("Y"), Close)),
                    Paragraph(Text(
                        "For this choice the discarded term is the divergence of m_Y from " +
                        "itself and is zero, so the upper bound becomes equality. Exhibiting an " +
                        "attaining reference makes the arbitrary-reference family a genuine " +
                        "degree of freedom rather than an unavoidable loss. The support " +
                        "condition remains essential to the theorem as stated: if m_Y has a " +
                        "zero, the equality identity still holds, but this witness is not " +
                        "admissible in the strictly positive reference family."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("reference-divergence-gives-a-fano-error-floor"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoReferenceDivergence.fano_error_probability_lower_bound_divergence"),
                H("Reference divergence gives the finite Fano error floor"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X and Y be finite, let p be a nonnegative normalized law on Y x X, " +
                        "let g from Y to X be arbitrary, and let u on Y be strictly positive and " +
                        "normalized. Assume card X is at least two and the hidden-coordinate " +
                        "marginal is the constant law 1/card X. Then the p-mass of pairs with " +
                        "g(y) unequal to x is at least")),
                    new DocumentBlock.DisplayFormula(Seq(
                        D(1), Minus,
                        Frac,
                        Grp(
                            F.Id("D"), Open,
                            F.Id("p"), Sp, Vert, Sp,
                            F.Id("u"), Sp, Cdot, Sp,
                            F.Id("m"), Underscore, Grp(F.Id("X")), Close,
                            Plus, Sp, Log, Sp, D(2)),
                        Grp(Log, Sp, Lvert, Sp, F.Id("X"), Sp, Rvert),
                        Sp, Le, Sp,
                        F.Id("P"), Open,
                        F.Id("g"), Open, F.Id("Y"), Close,
                        Neq, Sp, F.Id("X"), Close)),
                    Paragraph(Text(
                        "This is the uniform finite Fano floor with the mutual-information budget " +
                        "enlarged by the arbitrary-reference divergence bound. It constructs no " +
                        "estimator and places no restriction on g beyond its type."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("reference-divergence-product-bounds-hypothesis-count"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoReferenceDivergence.fano_hypothesis_count_product_bound_divergence"),
                H("The reference-divergence product form bounds hypothesis count"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X and Y be finite, let p be a nonnegative normalized law on Y x X, " +
                        "let g from Y to X be arbitrary, and let u on Y be strictly positive and " +
                        "normalized. Assume the hidden-coordinate marginal is uniform and the " +
                        "error mass is at most epsilon. With no cardinality restriction and no " +
                        "condition on epsilon, the theorem gives")),
                    new DocumentBlock.DisplayFormula(Seq(
                        Open, D(1), Minus, Varepsilon, Close, Sp, Cdot, Sp,
                        Log, Sp, Lvert, Sp, F.Id("X"), Sp, Rvert,
                        Sp, Le, Sp,
                        F.Id("D"), Open,
                        F.Id("p"), Sp, Vert, Sp,
                        F.Id("u"), Sp, Cdot, Sp,
                        F.Id("m"), Underscore, Grp(F.Id("X")), Close,
                        Plus, Sp, Log, Sp, D(2))),
                    Paragraph(Text(
                        "Like its mutual-information counterpart, this product form is primary " +
                        "because it remains valid when epsilon reaches or exceeds one and does " +
                        "not divide by 1 - epsilon."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("reference-divergence-quotient-bounds-hypothesis-count"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoReferenceDivergence.fano_hypothesis_count_bound_divergence"),
                H("The reference-divergence quotient isolates the candidate budget"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same finite-space, probability-law, positive normalized " +
                        "reference, uniform hidden-marginal, arbitrary-estimator, and " +
                        "error-at-most-epsilon hypotheses as the divergence product theorem, " +
                        "add exactly epsilon < 1. Then")),
                    new DocumentBlock.DisplayFormula(Seq(
                        Log, Sp, Lvert, Sp, F.Id("X"), Sp, Rvert,
                        Sp, Le, Sp,
                        Frac,
                        Grp(
                            F.Id("D"), Open,
                            F.Id("p"), Sp, Vert, Sp,
                            F.Id("u"), Sp, Cdot, Sp,
                            F.Id("m"), Underscore, Grp(F.Id("X")), Close,
                            Plus, Sp, Log, Sp, D(2)),
                        Grp(Open, D(1), Minus, Varepsilon, Close))),
                    Paragraph(Text(
                        "The sole additional condition makes 1 - epsilon positive, so dividing " +
                        "the side-condition-free product statement preserves the inequality. " +
                        "The normalization and strict-positivity assumptions on u remain in " +
                        "force; the quotient operation does not weaken either one."))),
                DescribeRole.Theorem
            ))));
}
