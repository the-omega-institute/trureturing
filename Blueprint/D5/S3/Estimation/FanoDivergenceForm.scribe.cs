using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class FanoDivergenceFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform finite Fano bounds hypothesis count in a side-condition-free product form and a quotient form valid below unit error.",
        H("Counting Hypotheses with Uniform Finite Fano"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-fano-product-bounds-hypothesis-count"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoDivergenceForm.fano_hypothesis_count_product_bound_uniform"),
                H("The product form bounds the resolvable hypothesis count"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, D(1), Minus, Varepsilon, Close, Sp, Cdot, Sp,
                    Log, Sp, Lvert, Sp, F.Id("X"), Sp, Rvert,
                    Sp, Le, Sp,
                    F.Id("I"), Open, F.Id("X"), Semi, Sp, F.Id("Y"), Close,
                    Plus, Sp, Log, Sp, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This general module was split from the arbitrary-reference material " +
                        "because an artifact's generality is bounded above by its dependency " +
                        "closure. The instance-level frozen DemonIdentity cannot be imported by " +
                        "a general artifact under SL-010. An independent walk of this module's " +
                        "transitive import closure found fourteen modules, all general, with " +
                        "DemonIdentity absent. The split therefore follows the dependency layer " +
                        "rather than merely dividing the exposition.")),
                    Paragraph(Text(
                        "Let X and Y be finite, let p be a nonnegative mass function on Y x X " +
                        "with total mass one, and let g from Y to X be arbitrary. Assume that " +
                        "the X-marginal obtained from the swapped law is the constant mass " +
                        "1/card X and that the p-mass on pairs with g(y) unequal to x is at " +
                        "most epsilon. With no cardinality restriction and no condition on " +
                        "epsilon, the theorem gives")),
                    new DocumentBlock.DisplayFormula(Seq(
                        Open, D(1), Minus, Varepsilon, Close, Sp, Cdot, Sp,
                        Log, Sp, Lvert, Sp, F.Id("X"), Sp, Rvert,
                        Sp, Le, Sp,
                        F.Id("I"), Open, F.Id("X"), Semi, Sp, F.Id("Y"), Close,
                        Plus, Sp, Log, Sp, D(2))),
                    Paragraph(Text(
                        "The previous wave used the already-frozen Fano relation to lower-bound " +
                        "error. This theorem changes the direction of use and solves the same " +
                        "relation for the number of candidates. It is not a new information " +
                        "inequality. In operational terms, at error below one an observation " +
                        "carrying I nats cannot reliably resolve substantially more than " +
                        "exp((I + log 2)/(1 - epsilon)) candidates.")),
                    Paragraph(Text(
                        "The product form is primary because it has no epsilon < 1 side " +
                        "condition. At epsilon equal to one and zero mutual information, its " +
                        "left side vanishes for every finite X and the statement reduces to")),
                    new DocumentBlock.DisplayFormula(Seq(
                        D(0), Le, Sp, Log, Sp, D(2))),
                    Paragraph(Text(
                        "This is true for every candidate count and therefore imposes no " +
                        "ceiling. That vacuity is required: an estimator permitted to be wrong " +
                        "with probability one constrains nothing."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("uniform-fano-quotient-bounds-hypothesis-count"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/FanoDivergenceForm.fano_hypothesis_count_bound_uniform"),
                H("The quotient form isolates the logarithmic candidate budget"),
                StatementSource.FromAuthor(Disp(Seq(
                    Log, Sp, Lvert, Sp, F.Id("X"), Sp, Rvert,
                    Sp, Le, Sp,
                    Frac,
                    Grp(
                        F.Id("I"), Open, F.Id("X"), Semi, Sp, F.Id("Y"), Close,
                        Plus, Sp, Log, Sp, D(2)),
                    Grp(Open, D(1), Minus, Varepsilon, Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same finite-space, probability-law, uniform hidden-marginal, " +
                        "arbitrary-estimator, and error-at-most-epsilon hypotheses as the " +
                        "product theorem, add exactly the condition epsilon < 1. The conclusion " +
                        "is")),
                    new DocumentBlock.DisplayFormula(Seq(
                        Log, Sp, Lvert, Sp, F.Id("X"), Sp, Rvert,
                        Sp, Le, Sp,
                        Frac,
                        Grp(
                            F.Id("I"), Open, F.Id("X"), Semi, Sp, F.Id("Y"), Close,
                            Plus, Sp, Log, Sp, D(2)),
                        Grp(Open, D(1), Minus, Varepsilon, Close))),
                    Paragraph(Text(
                        "The extra hypothesis appears only because the proof divides by " +
                        "1 - epsilon and needs that quantity positive to preserve the order. " +
                        "It is absent from the product theorem rather than silently inherited " +
                        "by it.")),
                    Paragraph(Text(
                        "The informative compiled illustration takes zero mutual information " +
                        "and epsilon equal to one half. The budget is log 2 divided by one half, " +
                        "which equals log 4. For a natural candidate count M, the source checks " +
                        "that M at least one together with log M at most log 4 forces M at most " +
                        "four:")),
                    new DocumentBlock.DisplayFormula(Seq(
                        F.Id("I"), Eq, D(0), Comma, Sp,
                        Varepsilon, Eq, Frac, Grp(D(1)), Grp(D(2)), Comma, Sp,
                        F.Id("M"), Ge, Sp, D(1), Comma, Sp,
                        Log, Sp, F.Id("M"), Le, Sp, Log, Sp, D(4),
                        Sp, Rightarrow, Sp, F.Id("M"), Le, Sp, D(4))),
                    Paragraph(Text(
                        "Exhibiting both the four-candidate ceiling and the epsilon-equals-one " +
                        "vacuous regime is substantive. A ceiling that binds in no regime would " +
                        "be worthless, while a ceiling that never becomes vacuous would be " +
                        "wrong. Together the two examples show that the rearranged bound both " +
                        "constrains and releases the hypothesis count in the regimes where it " +
                        "should."))),
                DescribeRole.Theorem
            ))));
}
