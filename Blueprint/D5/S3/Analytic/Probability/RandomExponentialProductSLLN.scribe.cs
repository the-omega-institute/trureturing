using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class RandomExponentialProductSLLNDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Analytic/Probability/RandomExponentialProductSLLN";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/dzhenzhersakbaev2026slln");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Products of bounded iid operator exponentials converge almost surely in the strong operator topology.",
        H("Random exponential product strong law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("random-product"),
                DeclarationHandle.Create(Module + ".randomProduct"),
                H("The random exponential product"),
                StatementSource.FromAuthor(Disp(RandomProductFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a scalar field K, a normed space e, an index space alpha, and a family "
                        + "of continuous linear endomorphisms a, randomProduct multiplies the "
                        + "exponentials of the factors t/n times a i omega in increasing Fin n order. "
                        + "The real quotient t/n is explicitly cast into K before scalar multiplication. "
                        + "This is the exponential semigroup product used in the source's semigroup "
                        + "setting (source lines 193–199 and 224–229)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Almost-sure strong-operator convergence on compact time intervals"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The proposition quantifies a scalar field K satisfying RCLike, a complete "
                        + "normed space e, a measurable index space alpha, a probability measure mu, "
                        + "and an operator-valued sequence a. Each a i is mu-almost-everywhere strongly measurable; the sequence is "
                        + "pairwise independent, identically distributed with a 0, and almost surely "
                        + "bounded by one real m. For every vector x and nonnegative time t, almost "
                        + "every omega satisfies an eventual epsilon estimate uniformly for s in "
                        + "[0,t]. The limit is the exponential of the Bochner integral of a 0, "
                        + "with the real time cast into K. This is the formal reading of the source "
                        + "conjecture (source lines 224–229)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The strong law for random exponential products"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The proof first installs the real-scalar algebra structure on the continuous "
                            + "linear endomorphisms and their Borel measurable space. In the "
                            + "subsingleton case every operator sends every vector to zero, so the "
                            + "required estimate is immediate.")),
                    Paragraph(Text(
                        "In the nontrivial case, the Bochner strong law for the bounded iid operator "
                            + "sequence gives almost-sure convergence of the normalized partial sums "
                            + "to the integral b. The centered sums therefore have a sublinear maximum "
                            + "on every sufficiently large prefix. A deterministic estimate combines "
                            + "the Euler product norm bound, the noncommutative Abel summation identity, "
                            + "and the centered maximum to compare the product of (1+(s/n)a i) with "
                            + "(1+(s/n)b)^n uniformly for s in [0,t].")),
                    Paragraph(Text(
                        "The exponential Taylor remainder bounds the difference between each exponential factor and its first-order approximation by three "
                            + "quarters of the squared scaled norm. A product perturbation estimate "
                            + "then compares the exponential product with the Euler product, and the "
                            + "same estimate compares the constant Euler product with exp(s b). The "
                            + "three errors are bounded by a term proportional to the centered maximum "
                            + "divided by n and a term proportional to 1/n, so the deterministic uniform "
                            + "estimate tends to zero.")),
                    Paragraph(Text(
                        "Finally, applying the deterministic estimate on the almost-sure strong-law "
                            + "event gives operator-norm convergence uniformly on the time interval. "
                            + "The continuous-linear-map operator bound converts this to the displayed "
                            + "vector estimate for every x, and the resulting almost-everywhere statement "
                            + "is exactly claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dzhenzher-sakbaev-2025-random-semigroup-slln"),
                    ResolutionKind.Proved)))));

    private static Formula RandomProductFormula()
    {
        Formula K = Scalar(), e = F.Id("e"), alpha = Alpha;
        Formula map = ContinuousLinearMap(K, e, e);
        Formula family = Arrow(Naturals(), Arrow(alpha, map));
        Formula product = At(Qualified("List", "prod"), At(Qualified("List", "ofFn"),
            LambdaOf("i", FinOf(F.Id("n")),
                At(Qualified("NormedSpace", "exp"),
                    Smul(
                        Typed(Typed(Div(F.Id("t"), Typed(F.Id("n"), Reals())), Reals()), K),
                        At(At(F.Id("a"), Typed(F.Id("i"), Naturals())), Omega))))));
        Formula equation = Equal(
            At(Local("randomProduct"), F.Id("a"), F.Id("n"), F.Id("t"), Omega),
            product);
        Formula binders = All("a", family,
            All("n", Naturals(),
                All("t", Reals(),
                    All(Omega, alpha, equation))));
        return All(K, Type(),
            All(e, Type(),
                All(alpha, Type(),
                    Seq(Instance("RCLike", K), Sp,
                        Instance("NormedAddCommGroup", e), Sp,
                        Instance("NormedSpace", K, e), Comma, Sp,
                        binders))));
    }

    private static Formula ClaimFormula()
    {
        Formula K = Scalar(), e = F.Id("e"), alpha = Alpha;
        Formula map = ContinuousLinearMap(K, e, e);
        Formula operatorFamily = Arrow(Naturals(), Arrow(alpha, map));
        Formula a = F.Id("a"), mu = Mu;
        Formula measurable = All("i", Naturals(),
            Call("AEStronglyMeasurable", At(a, F.Id("i")), mu));
        Formula independent = Call("Pairwise",
            LambdaOf("i", Naturals(),
                LambdaOf("j", Naturals(),
                    Call("IndepFun", At(a, F.Id("i")), At(a, F.Id("j")), mu))));
        Formula identical = All("i", Naturals(),
            Call("IdentDistrib", At(a, F.Id("i")), At(a, D(0)), mu, mu));
        Formula bounded = All("i", Naturals(),
            AlmostEverywhere(Omega, alpha, mu,
                LessOrEqual(
                    new Formula.Norm(At(At(a, F.Id("i")), Omega)),
                    F.Id("m"))));
        Formula integral = At(Qualified("MeasureTheory", "integral"), mu,
            LambdaOf("z", alpha, At(At(a, D(0)), F.Id("z"))));
        Formula limit = At(Qualified("NormedSpace", "exp"),
            Smul(Typed(Typed(F.Id("s"), Reals()), K), integral));
        Formula random = At(Local("randomProduct"), a, F.Id("n"), F.Id("s"), Omega);
        Formula estimate = LessThan(
            new Formula.Norm(At(Subtract(random, limit), F.Id("x"))),
            Varepsilon);
        Formula interval = Member(F.Id("s"),
            At(Qualified("Set", "Icc"), Typed(D(0), Reals()), F.Id("t")));
        Formula eventualN = EventuallyAtTop("n", Naturals(),
            All("s", Reals(), Arrow(interval, estimate)));
        Formula epsilon = All(Varepsilon, Reals(),
            Arrow(LessThan(Typed(D(0), Reals()), Varepsilon), eventualN));
        Formula almostEverywhere = AlmostEverywhere(Omega, alpha, mu, epsilon);
        Formula time = All("t", Reals(),
            Arrow(LessOrEqual(Typed(D(0), Reals()), F.Id("t")), almostEverywhere));
        Formula vector = All("x", e, time);
        Formula hypotheses = Arrow(measurable,
            Arrow(independent,
                Arrow(identical,
                    All("m", Reals(), Arrow(bounded, vector)))));
        Formula body = All("a", operatorFamily, hypotheses);
        Formula instances = Seq(
            Instance("RCLike", K), Sp,
            Instance("NormedAddCommGroup", e), Sp,
            Instance("NormedSpace", K, e), Sp,
            Instance("CompleteSpace", e), Sp,
            Instance("MeasurableSpace", alpha), Comma, Sp,
            All(mu, Call("Measure", alpha),
                Seq(Instance("IsProbabilityMeasure", mu), Comma, Sp,
                    LetI(RestrictScalars(K, e),
                        LetIAnnotated(Call("MeasurableSpace", map), Call("borel", map), body)))));
        return All(K, Type(), All(e, Type(), All(alpha, Type(), instances)));
    }

    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Analytic", "Probability", "RandomExponentialProductSLLN", name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Scalar() => Seq(Mathbb, Grp(F.Id("k")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Type() => Qualified("Type");
    private static Formula ContinuousLinearMap(Formula scalar, Formula domain, Formula codomain) =>
        At(Qualified("ContinuousLinearMap"), scalar, domain, codomain);
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Instance(string name, params Formula[] args) =>
        Seq(OpenBracket, At(Qualified(name), args), CloseBracket);
    private static Formula RestrictScalars(Formula scalar, Formula space) =>
        At(Qualified("NormedAlgebra", "restrictScalars"), Reals(), scalar,
            ContinuousLinearMap(scalar, space, space));
    private static Formula LetI(Formula value, Formula body) =>
        Seq(F.Id("letI"), Sp, Colon, Eq, Sp, value, Semi, Sp, body);
    private static Formula LetIAnnotated(Formula type, Formula value, Formula body) =>
        Seq(F.Id("letI"), Sp, Colon, Sp, type, Sp, Colon, Eq, Sp, value, Semi, Sp, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula At(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        At(Qualified(name), args);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula All(string name, Formula type, Formula body) => All(F.Id(name), type, body);
    private static Formula LambdaOf(Formula name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(name, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => LambdaOf(F.Id(name), type, body);
    private static Formula AlmostEverywhere(Formula name, Formula type, Formula measure, Formula body) =>
        At(Qualified("Filter", "Eventually"), LambdaOf(name, type, body),
            At(Qualified("MeasureTheory", "ae"), measure));
    private static Formula EventuallyAtTop(string name, Formula type, Formula body) =>
        At(Qualified("Filter", "Eventually"), LambdaOf(name, type, body),
            Qualified("Filter", "atTop"));
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Arrow(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula value) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
}
