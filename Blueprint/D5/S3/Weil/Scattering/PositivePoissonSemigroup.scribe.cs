using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Scattering;

internal sealed class PositivePoissonSemigroupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive completion depth propagates by further Poisson smoothing alone.",
        H("Positive Poisson Semigroup"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-poisson-semigroup"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Scattering/PositivePoissonSemigroup.positive_poisson_semigroup"),
                H("Positive completion depths form a Poisson semigroup"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public statement exposes the real-line convolution channel, the "
                            + "Poisson kernel family, the completion profiles, and their fixed "
                            + "boundary source. Associativity, kernel scale addition, and the "
                            + "profile representation are independent source laws.")),
                    Paragraph(Text(
                        "For every positive initial depth and positive increment, the deeper "
                            + "profile is obtained solely by applying the increment kernel to "
                            + "the shallower profile. No additional source term occurs.")),
                    Paragraph(Text(
                        "The proof positively rescales the depth coordinate and applies the "
                            + "frozen coarse semigroup theorem."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Weil/Scattering/PoissonSemigroup"))]));

    private static Formula TheoremFormula()
    {
        Formula star = F.Id("star");
        Formula kernel = F.Id("P");
        Formula completion = F.Id("completion");
        Formula source = F.Id("source");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula realFunction = Seq(reals, To, reals);
        Formula x = F.Id("x");
        Formula h = F.Id("h");
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        Formula k = F.Id("k");

        Formula associativity = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("f", realFunction), Bound("g", realFunction), Bound("k", realFunction)],
            Equal(
                Apply(star, f, Apply(star, g, k)),
                Apply(star, Apply(star, f, g), k)));
        Formula kernelSemigroup = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", reals), Bound("h", reals)],
            Implies(
                And(LessThan(D(0), x), LessThan(D(0), h)),
                Equal(
                    Apply(star, Apply(kernel, h), Apply(kernel, x)),
                    Apply(kernel, Add(x, h)))));
        Formula representation = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            reals,
            Equal(
                Apply(completion, x),
                Apply(star, Apply(kernel, x), source)));
        Formula conclusion = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", reals), Bound("h", reals)],
            Implies(
                And(LessThan(D(0), x), LessThan(D(0), h)),
                Equal(
                    Apply(completion, Add(x, h)),
                    Apply(star, Apply(kernel, h), Apply(completion, x)))));

        return Seq(
            Forall, Sp, star, Colon, Sp,
            Seq(realFunction, To, realFunction, To, realFunction), Comma, Sp,
            Forall, Sp, kernel, Colon, Sp, Seq(reals, To, realFunction), Comma, Sp,
            Forall, Sp, completion, Colon, Sp, Seq(reals, To, realFunction), Comma, Sp,
            Forall, Sp, source, Colon, Sp, realFunction, Comma, Sp,
            And(associativity, And(kernelSemigroup, representation)),
            Sp, Rightarrow, Sp, conclusion);
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        Formula result = function;
        foreach (Formula argument in arguments)
        {
            result = Seq(result, Open, argument, Close);
        }

        return result;
    }

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
