using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.ModelSet;

internal sealed class GoldenModelSetDensityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S1/Deficit/ModelSet/GoldenModelSetDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden model-set prefixes are exact half-open endpoint windows, and their counts "
            + "have asymptotic density one over square root five.",
        H("Density of the Golden Model Set"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("beta-real-tracks-square-root-five"),
                DeclarationHandle.Create(DeclarationPrefix + "beta_real_error"),
                H("The expanding coordinate stays within one unit of its linear scale"),
                StatementSource.FromAuthor(BetaRealErrorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural parameter v, the real embedding of its golden beta point "
                        + "differs from v times square root five by less than one. The Beatty-floor "
                        + "closed form confines the floor error to one unit, while the golden-ratio "
                        + "bounds place the remaining offset in the same open interval."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("beta-real-is-strictly-increasing"),
                DeclarationHandle.Create(DeclarationPrefix + "beta_real_strictMono"),
                H("The expanding coordinate is strictly increasing"),
                StatementSource.FromAuthor(BetaRealStrictMonoFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Advancing the natural parameter by at least one increases the linear main "
                        + "term by at least square root five. Since square root five exceeds two, "
                        + "the two one-unit error bounds cannot erase that increase, so betaReal "
                        + "is strictly increasing."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-beta-parameterization-is-injective"),
                DeclarationHandle.Create(DeclarationPrefix + "beta_golden_injective"),
                H("The golden beta parameterization is injective"),
                StatementSource.FromAuthor(BetaGoldenInjectiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The second integer coordinate of a golden beta point records its natural "
                        + "parameter. Equal beta points therefore have equal recorded parameters, "
                        + "so two distinct natural indices cannot name the same model-set point."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("beta-real-starts-at-zero"),
                DeclarationHandle.Create(DeclarationPrefix + "beta_real_zero"),
                H("The expanding coordinate starts at zero"),
                StatementSource.FromAuthor(BetaRealZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The floor of the golden ratio is one. Substituting this initial Beatty value "
                        + "into the displacement and conjugate closed form shows that the expanding "
                        + "coordinate of the zeroth golden beta point is exactly the origin."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-prefix-has-index-cardinality"),
                DeclarationHandle.Create(DeclarationPrefix + "golden_prefix_card"),
                H("Each golden prefix has its index as cardinality"),
                StatementSource.FromAuthor(GoldenPrefixCardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prefix of length n is the image of the first n natural parameters under "
                        + "the injective golden beta map. No points collide, so taking the image "
                        + "preserves the n-element cardinality of the parameter range."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-prefix-is-exact-endpoint-window"),
                DeclarationHandle.Create(DeclarationPrefix + "mem_golden_prefix_iff"),
                H("A golden prefix is exactly its half-open endpoint window"),
                StatementSource.FromAuthor(GoldenPrefixMembershipFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A golden integer lies in the first n beta points exactly when it belongs to "
                        + "the golden model set and its expanding coordinate lies from zero inclusive "
                        + "to betaReal n exclusive. Strict monotonicity orders the model-set points "
                        + "by their canonical natural parameters, and the zeroth coordinate supplies "
                        + "the lower endpoint."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("beta-real-ratio-tends-to-square-root-five"),
                DeclarationHandle.Create(DeclarationPrefix + "beta_real_ratio_tendsto"),
                H("The endpoint scale tends to square root five"),
                StatementSource.FromAuthor(BetaRealRatioFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Dividing the uniform one-unit error estimate by a positive parameter traps "
                        + "betaReal n over n between square root five minus one over n and square "
                        + "root five plus one over n. Both bounds have the same limit, so the "
                        + "endpoint scale converges to square root five."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-model-set-has-endpoint-density"),
                DeclarationHandle.Create(DeclarationPrefix + "golden_model_set_density"),
                H("The golden model set has density one over square root five"),
                StatementSource.FromAuthor(GoldenModelSetDensityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every endpoint betaReal n, the corresponding half-open window contains "
                            + "exactly the first n golden model-set points and therefore has count n. "
                            + "This identifies the finite counting sets rather than only estimating "
                            + "their sizes.")),
                    Paragraph(Text(
                        "The count-to-endpoint ratio is n divided by betaReal n. Inverting the "
                            + "endpoint-scale limit, whose positive limit is square root five, gives "
                            + "the asymptotic density one over square root five along these exact "
                            + "model-set endpoints."))),
                DescribeRole.Theorem))));

    private static Formula BetaRealErrorFormula()
    {
        Formula v = Id("v");
        Formula error = new Formula.Absolute(Subtract(
            BetaReal(v),
            Multiply(v, SquareRootFive())));

        return F.Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("v"),
            NaturalNumbers(),
            new Formula.Relation(error, FormulaRelationOperator.LessThan, Num(1))));
    }

    private static Formula BetaRealStrictMonoFormula() =>
        F.Disp(Call("StrictMono", Id("betaReal")));

    private static Formula BetaGoldenInjectiveFormula() =>
        F.Disp(Call("Injective", Id("betaGolden")));

    private static Formula BetaRealZeroFormula() =>
        F.Disp(Equal(BetaReal(Num(0)), Num(0)));

    private static Formula GoldenPrefixCardFormula()
    {
        Formula n = Id("n");

        return F.Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            NaturalNumbers(),
            Equal(Card(GoldenPrefix(n)), n)));
    }

    private static Formula GoldenPrefixMembershipFormula()
    {
        Formula n = Id("n");
        Formula x = Id("x");

        return F.Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            NaturalNumbers(),
            GoldenPrefixMembershipAt(n, x)));
    }

    private static Formula BetaRealRatioFormula()
    {
        Formula n = Id("n");
        Formula ratio = new Formula.Fraction(BetaReal(n), n);

        return F.Disp(Call(
            "Tendsto",
            ratio,
            Id("atTop"),
            Call("nhds", SquareRootFive())));
    }

    private static Formula GoldenModelSetDensityFormula()
    {
        Formula n = Id("n");
        Formula x = Id("x");
        Formula exactEndpoints = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            NaturalNumbers(),
            new Formula.Logic(
                Equal(Card(GoldenPrefix(n)), n),
                FormulaLogicOperator.And,
                GoldenPrefixMembershipAt(n, x)));
        Formula density = Call(
            "Tendsto",
            new Formula.Fraction(Card(GoldenPrefix(n)), BetaReal(n)),
            Id("atTop"),
            Call("nhds", new Formula.Fraction(Num(1), SquareRootFive())));

        return F.Disp(new Formula.Logic(
            exactEndpoints,
            FormulaLogicOperator.And,
            density));
    }

    private static Formula GoldenPrefixMembershipAt(Formula n, Formula x)
    {
        Formula endpointConditions = new Formula.Logic(
            Member(x, Id("goldenModelSet")),
            FormulaLogicOperator.And,
            new Formula.Logic(
                new Formula.Relation(
                    Num(0),
                    FormulaRelationOperator.LessThanOrEqual,
                    Embedding(x)),
                FormulaLogicOperator.And,
                new Formula.Relation(
                    Embedding(x),
                    FormulaRelationOperator.LessThan,
                    BetaReal(n))));
        Formula membership = new Formula.Logic(
            Member(x, GoldenPrefix(n)),
            FormulaLogicOperator.Iff,
            endpointConditions);

        return new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            GoldenIntegers(),
            membership);
    }

    private static Formula BetaReal(Formula index) => Call("betaReal", index);

    private static Formula GoldenPrefix(Formula length) => Call("goldenPrefix", length);

    private static Formula Card(Formula set) => Call("card", set);

    private static Formula Embedding(Formula point) => Call("embedding", point);

    private static Formula Member(Formula point, Formula set) =>
        new Formula.Relation(point, FormulaRelationOperator.MemberOf, set);

    private static Formula NaturalNumbers() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula GoldenIntegers() =>
        F.Seq(F.Operatorname, F.Grp(F.Id("GoldenInt")));

    private static Formula SquareRootFive() => F.Seq(F.Sqrt, F.Grp(F.D(5)));
}
