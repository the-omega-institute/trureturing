using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class FanoDivergenceFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Estimation/FanoDivergenceForm",
            "Positive normalized observation references bound finite mutual information by product-reference divergence; a positive observation marginal attains the family, and Fano yields hypothesis-counting forms."),
        H("Reference-Divergence and Hypothesis-Counting Forms of Finite Fano"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("every-positive-normalized-observation-reference-upper-bounds-mutual-information"),
                H("Every positive normalized observation reference upper-bounds mutual information"),
                LeanTheorem(
                    "D5/S3/Estimation/FanoDivergenceForm.mutual_information_le_product_reference_divergence"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("Y"), Comma, Sp, F.Id("X"), Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Colon, Sp,
                    F.Id("Y"), Times, Sp, F.Id("X"), To, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("u"), Colon, Sp, F.Id("Y"), To, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open,
                    Forall, Sp, F.Id("z"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("z"), Close,
                    Close, Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("z")), Sp,
                    F.Id("p"), Open, F.Id("z"), Close, Eq, D(1), Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("y"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("u"), Open, F.Id("y"), Close, Close, Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("y")), Sp,
                    F.Id("u"), Open, F.Id("y"), Close, Eq, D(1), Close, Sp,
                    Rightarrow, Sp, RowBreak,
                    Operatorname, Grp(F.Id("mutualInformation")), Open, F.Id("p"), Close,
                    Le, Sp,
                    Operatorname, Grp(F.Id("klDivergence")), Open,
                    F.Id("p"), Comma, Sp,
                    Open, Open, F.Id("y"), Comma, Sp, F.Id("x"), Close, Mapsto, Sp,
                    F.Id("u"), Open, F.Id("y"), Close, Sp, Cdot, Sp,
                    Operatorname, Grp(F.Id("marginal")), Open,
                    Open, F.Id("x"), Comma, Sp, F.Id("y"), Close, Mapsto, Sp,
                    F.Id("p"), Open, F.Id("y"), Comma, Sp, F.Id("x"), Close,
                    Close, Open, F.Id("x"), Close, Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The preceding Fano error floor is stated in terms of mutual " +
                        "information, which may be awkward to evaluate directly. The already " +
                        "frozen theorem demon_average_divergence_eq writes the displayed " +
                        "joint-to-product-reference divergence as mutualInformation p plus " +
                        "klDivergence (marginal p) u. Discarding the latter term gives the " +
                        "displayed upper bound while leaving the observation reference u free. " +
                        "This step is a one-line consequence of that frozen identity and Gibbs " +
                        "nonnegativity; it is not presented as a new information inequality.")),
                    Paragraph(Text(
                        "The inequality has a strictly stronger hypothesis than the identity " +
                        "from which it is derived. The identity requires u only to be strictly " +
                        "positive. Discarding klDivergence (marginal p) u additionally requires " +
                        "that term to be nonnegative, and Gibbs nonnegativity applies only when " +
                        "both arguments are distributions. Consequently u must also have total " +
                        "mass one. Strict positivity supplies discrete absolute continuity for " +
                        "free, but it does not supply normalization.")),
                    Paragraph(Text(
                        "Normalization is necessary rather than cosmetic. On the one-point " +
                        "space, the divergence of the unit mass from the constant reference 2 " +
                        "is -log 2, which is negative. Thus a merely positive, nonnormalized " +
                        "reference can make the remainder in the frozen decomposition negative; " +
                        "discarding it would reverse the intended comparison. The compiled " +
                        "counterexample records exactly D(1 || 2) = -log 2.")),
                    Paragraph(Text(
                        "The companion exists_observation_marginal_reference_attaining shows " +
                        "that this family of upper bounds is attained. If the observation " +
                        "marginal of p is strictly positive at every point, take u to be " +
                        "that marginal. Its total mass is one because p is a joint distribution, " +
                        "and the discarded divergence is then the divergence of a distribution " +
                        "from itself, hence zero. The resulting product-reference divergence " +
                        "equals mutualInformation p. The positivity assumption is genuine: if " +
                        "the marginal has zeros, the equality still holds, but this witness does " +
                        "not belong to the admissible strictly-positive reference family.")),
                    Paragraph(Text(
                        "The theorem fano_error_probability_lower_bound_divergence makes the " +
                        "corresponding short monotone substitution in the previous uniform-prior " +
                        "Fano floor. It assumes that p is a nonnegative law of total mass one, " +
                        "that u is strictly positive and normalized, that 2 <= card X, and that " +
                        "the hidden-coordinate marginal is the constant law 1/card X. For every " +
                        "estimator g, its error mass is at least 1 minus the sum of the displayed " +
                        "product-reference divergence and log 2, divided by log(card X). The " +
                        "passage from mutual information to divergence is a short corollary, not " +
                        "an independently weighted result.")),
                    Paragraph(Text(
                        "The change of direction is expressed first by " +
                        "fano_hypothesis_count_product_bound_uniform. Under the same law and " +
                        "uniform-hidden-marginal assumptions, if the error mass of an arbitrary " +
                        "estimator is at most epsilon, then (1-epsilon) log(card X) is at most " +
                        "mutualInformation p + log 2. This product form is primary and has no " +
                        "epsilon < 1 hypothesis. Its companion fano_hypothesis_count_bound_uniform " +
                        "adds exactly epsilon < 1 and divides to obtain log(card X) at most " +
                        "(mutualInformation p + log 2)/(1-epsilon).")),
                    Paragraph(Text(
                        "The declarations fano_hypothesis_count_product_bound_divergence and " +
                        "fano_hypothesis_count_bound_divergence enlarge the same two information " +
                        "budgets to the product-reference divergence. Both retain the law, " +
                        "uniform-hidden-marginal, error, strict-positivity, and normalization " +
                        "hypotheses. The divergence product form again has no epsilon < 1 side " +
                        "condition; only its quotient companion assumes epsilon < 1, because " +
                        "only that statement divides by 1-epsilon.")),
                    Paragraph(Text(
                        "This orientation counts resolvable hypotheses rather than bounding " +
                        "error: for epsilon < 1, an observation carrying I nats cannot reliably " +
                        "distinguish more " +
                        "than approximately exp((I + log 2)/(1-epsilon)) candidates at target " +
                        "error epsilon. In the compiled informative regime I = 0 and epsilon = " +
                        "1/2, so the logarithmic budget is log 2 divided by 1/2, namely log 4. " +
                        "For M >= 1, the exact implication log M <= log 4 therefore gives M <= " +
                        "4. The ceiling binds and permits at most four candidates.")),
                    Paragraph(Text(
                        "At the opposite endpoint, I = 0 and epsilon = 1 make the product form " +
                        "read 0 <= log 2 for every M, so it imposes no cardinality ceiling. This " +
                        "is the correct vacuous regime: an estimator permitted always to be " +
                        "wrong constrains nothing. Exhibiting both regimes is necessary. A " +
                        "ceiling that binds nowhere would be worthless, while one that remained " +
                        "binding at error one would be false to the estimation problem.")),
                    Paragraph(Text(
                        "The first inequality is a one-line corollary of a frozen decomposition, " +
                        "and the divergence-form error floor is a short monotone substitution. " +
                        "The content of this module is instead the normalization hypothesis and " +
                        "its concrete negative-divergence counterexample, the admissible " +
                        "attainment witness, and the hypothesis-counting orientation with its " +
                        "side-condition-free product forms. All seven declarations are finite " +
                        "and nats-valued. The module introduces no definition and claims no new " +
                        "information identity, estimator construction, minimax theorem, " +
                        "sample-complexity theorem, or measure-theoretic analogue.")))))));
}
