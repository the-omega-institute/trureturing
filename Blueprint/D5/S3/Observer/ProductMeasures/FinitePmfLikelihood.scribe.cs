using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProductMeasures;

internal sealed class FinitePmfLikelihoodDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProductMeasures/FinitePmfLikelihood.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-coordinate likelihoods construct an absolutely continuous product law.",
        H("Finite PMF Likelihood Construction"),
        Blocks(
            Definition(
                "pmf-real-mass",
                "pmfRealMass",
                "Real mass of a finite PMF",
                RealMassFormula(),
                "Finite PMF masses are converted from extended nonnegative reals to reals."),
            Definition(
                "root-likelihood",
                "rootLikelihood",
                "Square-root likelihood ratio",
                RootLikelihoodFormula(),
                "The ratio is totalized at zero denominators by real division."),
            Definition(
                "finite-pmf-affinity",
                "affinity",
                "Finite PMF affinity",
                AffinityFormula(),
                "The Bhattacharyya affinity sums products of square roots of masses."),
            Definition(
                "finite-pmf-energy",
                "energy",
                "Finite PMF Hellinger energy",
                EnergyFormula(),
                "The repository convention is H squared equals twice one minus affinity."),
            Definition(
                "prefix-root-likelihood",
                "prefixRootLikelihood",
                "Finite-prefix root likelihood",
                PrefixLikelihoodFormula(),
                "The first n coordinate likelihood ratios are multiplied."),
            Definition(
                "tail-affinity",
                "tailAffinity",
                "Finite tail affinity",
                TailAffinityFormula(),
                "Coordinate affinities are multiplied on the half-open interval."),
            Definition(
                "product-law",
                "productLaw",
                "Countable product law",
                ProductLawFormula(),
                "The infinite product measure is built from the coordinate PMF measures."),
            Lemma(
                "pmf-real-mass-nonnegative",
                "pmfRealMass_nonneg",
                "Real PMF masses are nonnegative",
                RealMassNonnegativeFormula(),
                "Conversion from extended nonnegative reals preserves nonnegativity."),
            Lemma(
                "mass-zero-iff-of-ac",
                "mass_zero_iff_of_ac",
                "Equivalent local laws share zero atoms",
                SameZerosFormula(),
                "Mutual absolute continuity transfers null singleton events both ways."),
            Lemma(
                "energy-affinity-identity",
                "energy_eq_two_mul_one_sub_affinity",
                "Energy is twice one minus affinity",
                EnergyAffinityFormula(),
                "Normalization of both finite PMFs yields the standard identity."),
            Lemma(
                "affinity-nonnegative",
                "affinity_nonneg",
                "Affinity is nonnegative",
                AffinityNonnegativeFormula(),
                "Every summand is a product of nonnegative square roots."),
            Lemma(
                "prefix-root-likelihood-in-l2",
                "prefixRootLikelihood_memLp_two",
                "Prefix likelihoods belong to L2",
                PrefixMemLpFormula(),
                "A finite-coordinate function on a probability space is bounded."),
            Lemma(
                "prefix-root-likelihood-integral",
                "integral_prefixRootLikelihood",
                "Prefix expectation factors into affinities",
                PrefixIntegralFormula(),
                "Independence of product coordinates factors the finite expectation."),
            Theorem(
                "product-law-ac-of-summable",
                "productLaw_ac_of_summable",
                "Summable energy gives product absolute continuity",
                ProductAbsoluteContinuityFormula(),
                "L2 likelihood limits provide a density for the first product law."))));

    private static DocumentBlock Definition(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation) =>
        Describe(id, declaration, title, statement, explanation, DescribeRole.Definition);

    private static DocumentBlock Lemma(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation) =>
        Describe(id, declaration, title, statement, explanation, DescribeRole.Lemma);

    private static DocumentBlock Theorem(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation) =>
        Describe(id, declaration, title, statement, explanation, DescribeRole.Theorem);

    private static DocumentBlock Describe(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation,
        DescribeRole role) =>
        StrataLint.Scribe.Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            role);

    private static Formula RealMassFormula() =>
        Disp(Equal(
            Call("pmfRealMass", F.Id("p"), F.Id("o")),
            Call("toReal", Call("mass", F.Id("p"), F.Id("o")))));

    private static Formula RootLikelihoodFormula() =>
        Disp(Equal(
            Call("rootLikelihood", F.Id("p"), F.Id("q"), F.Id("o")),
            Call("sqrtRatio", Call("pmfRealMass", F.Id("p"), F.Id("o")),
                Call("pmfRealMass", F.Id("q"), F.Id("o")))));

    private static Formula AffinityFormula() =>
        Disp(Equal(
            Call("affinity", F.Id("p"), F.Id("q")),
            Call("finiteBhattacharyyaSum", F.Id("p"), F.Id("q"))));

    private static Formula EnergyFormula() =>
        Disp(Equal(
            Call("energy", F.Id("p"), F.Id("q")),
            Call("hellingerSquared", F.Id("p"), F.Id("q"))));

    private static Formula PrefixLikelihoodFormula() =>
        Disp(Equal(
            Call("prefixRootLikelihood", F.Id("p"), F.Id("q"), F.Id("n"),
                F.Id("x")),
            Call("productBefore", F.Id("n"), Call("rootLikelihoodAt", F.Id("x")))));

    private static Formula TailAffinityFormula() =>
        Disp(Equal(
            Call("tailAffinity", F.Id("p"), F.Id("q"), F.Id("m"), F.Id("n")),
            Call("productOnHalfOpenInterval", F.Id("m"), F.Id("n"),
                F.Id("affinity"))));

    private static Formula ProductLawFormula() =>
        Disp(Equal(
            Call("productLaw", F.Id("p")),
            Call("infiniteProductMeasure", F.Id("p"))));

    private static Formula RealMassNonnegativeFormula() =>
        Disp(new Formula.Relation(
            D(0),
            FormulaRelationOperator.LessThanOrEqual,
            Call("pmfRealMass", F.Id("p"), F.Id("o"))));

    private static Formula SameZerosFormula() =>
        Disp(new Formula.Logic(
            Equal(Call("pmfRealMass", F.Id("p"), F.Id("o")), D(0)),
            FormulaLogicOperator.Iff,
            Equal(Call("pmfRealMass", F.Id("q"), F.Id("o")), D(0))));

    private static Formula EnergyAffinityFormula() =>
        Disp(Equal(
            Call("energy", F.Id("p"), F.Id("q")),
            Multiply(D(2), Subtract(D(1), Call("affinity", F.Id("p"), F.Id("q"))))));

    private static Formula AffinityNonnegativeFormula() =>
        Disp(new Formula.Relation(
            D(0),
            FormulaRelationOperator.LessThanOrEqual,
            Call("affinity", F.Id("p"), F.Id("q"))));

    private static Formula PrefixMemLpFormula() =>
        Disp(Call("MemLp", Call("prefixRootLikelihood", F.Id("p"), F.Id("q"),
            F.Id("n")), D(2), Call("productLaw", F.Id("q"))));

    private static Formula PrefixIntegralFormula() =>
        Disp(Equal(
            Call("integral", Call("prefixRootLikelihood", F.Id("p"), F.Id("q"),
                F.Id("n")), Call("productLaw", F.Id("q"))),
            Call("productBefore", F.Id("n"), F.Id("affinity"))));

    private static Formula ProductAbsoluteContinuityFormula() =>
        Disp(new Formula.Logic(
            Call("summable", Call("energySequence", F.Id("p"), F.Id("q"))),
            FormulaLogicOperator.Implies,
            Call("AbsolutelyContinuous", Call("productLaw", F.Id("p")),
                Call("productLaw", F.Id("q")))));
}
