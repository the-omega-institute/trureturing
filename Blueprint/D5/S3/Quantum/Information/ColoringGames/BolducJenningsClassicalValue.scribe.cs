using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ColoringGames;

internal sealed class BolducJenningsClassicalValueDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ColoringGames/BolducJenningsClassicalValue";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Convexity/bolducjennings2026coloring");

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N => F.Id("n");
    private static Formula M => F.Id("m");
    private static Formula P => F.Id("p");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula S => F.Id("s");
    private static Formula T => F.Id("t");
    private static Formula K => F.Id("k");
    private static Formula Rho => F.Rho;
    private static Formula A => F.Id("A");
    private static Formula C => F.Id("C");

    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Bind(Formula variable, Formula type) => Seq(variable, Colon, Sp, type);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Bind(variable, type)), Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Bind(variable, type)), Comma, Sp, body);
    private static Formula Equal(Formula lhs, Formula rhs) =>
        new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Conj(Formula lhs, Formula rhs) =>
        new Formula.Logic(lhs, FormulaLogicOperator.And, rhs);
    private static Formula Given(Formula lhs, Formula rhs) =>
        new Formula.Logic(Par(lhs), FormulaLogicOperator.Implies, Par(rhs));
    private static Formula Quotient(Formula top, Formula bottom) => Seq(Frac, Grp(top), Grp(bottom));
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Square(Formula value) => Seq(value, Caret, Grp(D(2)));
    private static Formula Cast(Formula value) => Par(Bind(value, Real));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Table() => new Formula.TypeArrow(Fin(N), Fin(M));
    private static Formula Strategy() => Call("Strategy", N, M);
    private static Formula Inputs() => Product(Fin(N), Fin(N));
    private static Formula Simplex() => Call("StdSimplex", Real, Strategy());
    private static Formula Pair() => Seq(Open, X, Comma, Sp, Y, Close);
    private static Formula First(Formula pair) => Seq(pair, Dot, D(1));
    private static Formula Second(Formula pair) => Seq(pair, Dot, D(2));
    private static Formula At(Formula function, Formula input) =>
        new Formula.Apply(function, [input]);
    private static Formula IndexedSum(Formula index, Formula indexType, Formula summand) =>
        Seq(Sum, Underscore, Grp(Bind(index, indexType)), Sp, summand);
    private static Formula Set(Formula binder, Formula condition) =>
        Seq(OpenBrace, binder, Sp, Mid, Sp, condition, CloseBrace);
    private static Formula Card(Formula set) => Call("card", set);
    private static Formula Weight(Formula pair) => Call("inputWeight", N, P, pair);
    private static Formula OffDenominator() => Product(Cast(N), Par(Seq(Cast(N), Minus, D(1))));
    private static Formula OffNumerator() => Seq(D(1), Minus, P);
    private static Formula OffWeight() => Quotient(OffNumerator(), OffDenominator());
    private static Formula TParam() =>
        Quotient(Product(P, Par(Seq(Cast(N), Minus, D(1)))), OffNumerator());
    private static Formula CommonSize(Formula colors, Formula t) =>
        Call("commonSize", N, colors, t);
    private static Formula BalancedSquares(Formula colors, Formula size) => Call("B", colors, size);
    private static Formula Win(Formula strategy) => Call("detWin", N, M, P, strategy);
    private static Formula Score(Formula t, Formula strategy) =>
        Call("detScore", N, M, t, strategy);
    private static Formula WinCondition(Formula strategy) =>
        new Formula.Logic(Equal(X, Y), FormulaLogicOperator.Iff,
            Equal(At(First(strategy), X), At(Second(strategy), Y)));
    private static Formula If(Formula condition, Formula positive, Formula negative) =>
        Call("ite", condition, positive, negative);
    private static Formula ForSizes(Formula body) => All(N, Nat, All(M, Nat, body));

    private static Formula BFormula()
    {
        var quotient = Par(Seq(S, Sp, Operatorname, Grp(F.Id("div")), Sp, K));
        var remainder = Par(Seq(S, Sp, Operatorname, Grp(F.Id("mod")), Sp, K));
        return All(K, Nat, All(S, Nat, Equal(BalancedSquares(K, S),
            Seq(Product(K, Square(quotient)), Plus,
                Product(Par(Seq(Product(D(2), quotient), Plus, D(1))), remainder)))));
    }

    private static Formula CommonSizeFormula()
    {
        var ceiling = Call("NatCeil", Quotient(T, D(2)));
        return All(N, Nat, All(K, Nat, All(T, Real,
            Equal(CommonSize(K, T), Call("min", N, Product(K, ceiling))))));
    }

    private static Formula InputWeightFormula() =>
        All(N, Nat, All(P, Real, All(Pair(), Inputs(),
            Equal(Weight(Pair()),
                If(Equal(X, Y), Quotient(P, Cast(N)), OffWeight())))));

    private static Formula DetWinFormula() =>
        ForSizes(All(P, Real, All(Rho, Strategy(), Equal(Win(Rho),
            IndexedSum(Pair(), Inputs(), If(WinCondition(Rho), Weight(Pair()), D(0)))))));

    private static Formula MixedWinFormula() =>
        ForSizes(All(P, Real, All(F.Mu, Simplex(),
            Equal(Call("mixedWin", N, M, P, F.Mu), IndexedSum(Rho, Strategy(),
                Product(Call("weights", F.Mu, Rho), Win(Rho)))))));

    private static Formula AffineValue(Formula score) =>
        Seq(D(1), Minus, P, Plus, Product(OffWeight(), score));

    private static Formula DetScoreFormula()
    {
        var diagonal = Card(Set(Bind(X, Fin(N)), Equal(At(First(Rho), X), At(Second(Rho), X))));
        var collisions = Card(Set(Bind(Pair(), Inputs()), Equal(At(First(Rho), X), At(Second(Rho), Y))));
        return ForSizes(All(T, Real, All(Rho, Strategy(),
            Equal(Score(T, Rho), Seq(Product(Par(Seq(D(1), Plus, T)), Cast(diagonal)), Minus, Cast(collisions))))));
    }

    private static Formula ResultFormula()
    {
        var t = Call("tParam", N, P);
        var d = Par(Seq(M, Minus, D(2)));
        var size = CommonSize(d, t);
        var lambda = Par(Seq(D(1), Plus, t));
        var sync = Seq(Product(lambda, Cast(N)), Minus, Cast(BalancedSquares(M, N)));
        var common = Seq(Product(lambda, Cast(size)), Minus, Cast(BalancedSquares(d, size)));
        var maximum = AffineValue(Call("max", sync, common));
        var greatest = Call("IsGreatest", Call("range", Call("mixedWin", N, M, P)), maximum);
        var attaining = Some(A, Strategy(), Some(C, Strategy(), Par(
            Conj(Par(Equal(Score(t, A), sync)), Par(Equal(Score(t, C), common))))));
        var normal = Equal(IndexedSum(Pair(), Inputs(), Weight(Pair())), D(1));
        var sizes = Conj(Seq(D(2), Sp, Le, Sp, M), Seq(M, Sp, Lt, Sp, N));
        var interval = Seq(D(0), Sp, Lt, Sp, P, Sp, Lt, Sp, Quotient(D(2), Seq(Cast(M), Plus, D(2))));
        return ForSizes(All(P, Real, Given(Conj(Par(sizes), Par(interval)),
            Conj(Par(greatest), Conj(Par(attaining), Par(normal))))));
    }

    private static DocumentBlock Definition(string id, string name, string title, Formula formula, string explanation,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted complete-graph coloring game has a sharp classical value from two attainable deterministic scores.",
        H("Classical value of the complete-graph coloring game"),
        Blocks(Paragraph(Text(
            "Alice and Bob each receive a vertex and answer with a color. The inputs are ordered. "
            + "They win when equal inputs have equal answers and unequal inputs have unequal answers. "
            + "Shared and private random choices independent of the input can be sampled as complete local tables "
            + "before play. Their distribution ranges over the whole real standard simplex of table pairs.")),
        Definition("balanced-squares", "B", "Balanced sum of squares", BFormula(),
            "For a positive number k of colors, Lemma 3.1.4 of Bolduc and Jennings gives the minimum as the displayed sum. "
            + "Divide s by k in the natural numbers. "
            + "Assign the quotient plus one to the remainder many colors and the quotient to all other colors. "
            + "At k=0, Lean's total natural division and remainder give B(0,s)=s. "
            + "The only feasible zero-color block is empty and has B(0,0)=0.",
            AssessedProvenance.FromLiterature(Source)),
        Definition("common-size", "commonSize", "Size of the common block", CommonSizeFormula(),
            "NatCeil is the natural ceiling. For the admissible nonnegative t it is the usual real ceiling. "
            + "The number of common inputs is capped at n.",
            AssessedProvenance.FromRepo(Source)),
        Definition("strategy", "Strategy", "Pairs of local response tables",
            ForSizes(Equal(Strategy(), Product(Par(Table()), Par(Table())))),
            "The first table belongs to Alice and the second to Bob. Both range over all functions from vertices to colors.",
            AssessedProvenance.FromLiterature(Source)),
        Definition("input-weight", "inputWeight", "Ordered referee weights", InputWeightFormula(),
            "For n>1, the diagonal receives total mass p and the off-diagonal receives total mass 1−p across both input orders.",
            AssessedProvenance.FromLiterature(Source)),
        Definition("det-win", "detWin", "Deterministic winning probability", DetWinFormula(),
            "Sum the input weight exactly when the input and output equalities have the same truth value.",
            AssessedProvenance.FromLiterature(Source)),
        Definition("mixed-win", "mixedWin", "Classical winning probability", MixedWinFormula(),
            "Section 2.2 of Bolduc and Jennings defines the value of a mixed strategy as the probability-weighted average of pure-strategy values. "
            + "The Lean formalization uses StdSimplex for the input-independent distribution over ordered table pairs, "
            + "with one nonnegative weight per pair and total weight one.",
            AssessedProvenance.FromLiterature(Source)),
        Definition("t-param", "tParam", "Ratio of diagonal to off-diagonal weights",
            All(N, Nat, All(P, Real, Equal(Call("tParam", N, P), TParam()))),
            "The ratio p(n−1)/(1−p) is the nonconstant term in the score coefficient in §2.1 of Bolduc and Jennings.",
            AssessedProvenance.FromLiterature(Source)),
        Definition("probability", "probability", "Conversion from score to probability",
            All(N, Nat, All(P, Real, All(S, Real,
                Equal(Call("probability", N, P, S), AffineValue(S))))),
            "The baseline is the total off-diagonal mass. One unit of score contributes one off-diagonal input weight.",
            AssessedProvenance.FromLiterature(Source)),
        Definition("det-score", "detScore", "Score of a deterministic table pair", DetScoreFormula(),
            "Count diagonal agreements with coefficient 1+t and subtract ordered color collisions. "
            + "For each color i, the collision contribution is the product of its two table counts.",
            AssessedProvenance.FromLiterature(Source)),
        Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
            H("Exact low-diagonal classical value"),
            StatementSource.FromAuthor(Disp(ResultFormula())),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "The two scores use t=p(n−1)/(1−p), λ=1+t, d=m−2 and s=min(n,d⌈t/2⌉). "
                    + "They are λn−B(m,n) and λs−B(d,s). IsGreatest certifies attainment and a bound "
                    + "on every classical mixture. Two deterministic pairs attain the respective scores, "
                    + "and the last equality normalizes the ordered input weights.")),
                Paragraph(Text(
                    "For arbitrary marginals, remove their pointwise minimum. The two residual supports are disjoint. "
                    + "If the residual mass vanishes, the balanced-square minimum bounds the score by the synchronous value. "
                    + "Otherwise choose a color of least common count on each residual support. With common counts a and b "
                    + "and remaining total R, parity gives R a b ≤ (a+b)⌊R/2⌋⌈R/2⌉. "
                    + "The resulting score is bounded by the greater of the two endpoint scores.")),
                Paragraph(Text(
                    "For d>0, the difference of successive common-block scores is t−2⌊s/d⌋. "
                    + "Its sign makes the stated capped ceiling a maximizing size, including zero differences at ties. "
                    + "When m=2, the common block is empty and its score is zero.")),
                Paragraph(Text(
                    "A balanced synchronous coloring attains the first score. For the second, both players use the "
                    + "same balanced coloring with colors 2 through m−1 on the first s inputs. On the remaining inputs "
                    + "Alice uses color 0 and Bob uses color 1. A point mass on the better pair attains the classical value."))),
            DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("bolduc-jennings-2026-low-diagonal-classical-coloring"), ResolutionKind.Proved)))));
}
