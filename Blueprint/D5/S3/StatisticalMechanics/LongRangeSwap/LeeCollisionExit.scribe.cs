using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.LongRangeSwap;

internal sealed class LeeCollisionExitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/StatisticalMechanics/lee2026longrangeswap");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal local matrices and adjacent-slot operators have uniformly bounded positive-weight collision exit paths.",
        H("Collision paths for the long-range swap matrices"),
        Blocks(
            Node("b", "The local matrix B", "B", SourceB(false), "Equation (7), source label 138am42, assigns the diagonal same-species weight mu and the unit weight to a swapped increasing input pair. Species are Fin N, with their natural order.", literature: true),
            Node("bprime", "The local matrix B prime", "Bprime", SourceB(true), "The second matrix in equation (7) assigns 1 - mu to an equal pair and the unit weight to a swapped decreasing input pair.", literature: true),
            Node("adjacent", "An adjacent-slot operator", "adjacent", AdjacentFormula(), "The two slots are zero-based s and s + 1. The product imposes the identity on every other slot. The value is zero when s + 1 is outside Fin n. Fin.mk displays only the value component; its bound proof is suppressed. All implicit size parameters are displayed explicitly.", literature: true),
            Node("calb", "The block coefficient", "calB", CalBFormula(false), "The source tensor product I to the power j + i - 2, then B, then I to the power n - j - i acts on the one-indexed slots j + i - 1 and j + i. Natural subtraction in the slot argument is truncated subtraction.", literature: true),
            Node("calbprime", "The second block coefficient", "calBprime", CalBFormula(true), "The same adjacent-slot construction uses B prime in place of B.", literature: true),
            Node("swapword", "Exchange the adjacent word slots", "swapWord", SwapWordFormula(), "Precomposition with Equiv.swap exchanges the two valid adjacent coordinates. The proof h guarantees both Fin constructors are valid."),
            Node("calbaction", "The row action of the block coefficient", "calB_mulVec", RowAction(false), "Every row has one possible successor word. Its coefficient is the corresponding swapped entry of B.", DescribeRole.Theorem),
            Node("calbprimeaction", "The second row action", "calBprime_mulVec", RowAction(true), "The same row rule holds for B prime.", DescribeRole.Theorem),
            Node("weights", "The two outgoing masses", "weights_nonneg_sum", WeightsFormula(), "For each pair and each parameter in the closed unit interval, the two swapped entries are nonnegative and sum to one. This includes both endpoint parameters.", DescribeRole.Theorem),
            Node("pathswap", "Exchange an integer-indexed pair", "swap", PathSwapFormula(), "Integer-indexed words use the existing coordinate transposition Equiv.swap."),
            Node("left", "Choose a collision direction", "left", LeftFormula(), "Move toward the smaller label. At an equal pair use its preferred direction."),
            Node("next", "A collision transition", "next", NextFormula(), "Swap the collision pair and move its position one step in the selected direction."),
            Node("interior", "The interior collision positions", "interior", InteriorFormula(), "Interior positions are the integers from zero through m - 1; all other positions are boundary states."),
            Node("preferred", "Select a positive equal-pair weight", "preferred", PreferredFormula(), "Choose left at a same-species pair when mu is at least one half; otherwise choose right. The displayed fraction is real division."),
            Node("leftstate", "The left successor", "leftState", StateFormula(false), "The left successor swaps the pair and decrements its position."),
            Node("rightstate", "The right successor", "rightState", StateFormula(true), "The right successor swaps the pair and increments its position."),
            Node("chosen", "The selected transition weight", "chosenWeight", ChosenFormula(), "The selected mass is the actual B or B prime matrix entry. No assumption on mu is needed for this selected mass to be positive."),
            Node("exits", "A bounded positive-weight exit path", "exits", ExitFormula(), "The minimum collision label never increases. While the minimum stays fixed, a direction change can only turn toward the preferred direction of that label, so there is at most one reversal. A decreasing integer rank combines the label, this reversal budget, and the remaining distance. Its bound is 2 N m. Following the selected transitions gives an exit of at most that length, positive product weight, interior states before the endpoint, and a path in the positive-weight transition relation. The conclusion applies to every real parameter vector; nonnegativity of both outgoing masses is a separate interval condition.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role = DescribeRole.Definition, bool literature = false) =>
        Describe.Lean(DescribeId.Create("lee-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Some(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Not(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, b));
    private static Formula ProductType(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Lam(string x, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, F.Id(x), Colon, type, Sp, Mapsto, Sp, body);
    private static Formula Ite(Formula p, Formula a, Formula b) => Call("ite", p, a, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Int() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Word(Formula N, Formula n) => Arr(Fin(n), Fin(N));
    private static Formula PairSpecies(Formula N) => ProductType(Fin(N), Fin(N));
    private static Formula State(Formula N) => ProductType(Int(), Parenthesized(Arr(Int(), Fin(N))));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Fst(Formula x) => QCall("Prod", "fst", x);
    private static Formula Snd(Formula x) => QCall("Prod", "snd", x);
    private static Formula Matrix(Formula x) => Call("Matrix", x, x, Real());
    private static Formula NatBind(Formula body, params string[] names)
    {
        for (int i = names.Length - 1; i >= 0; i--) body = All(names[i], Nat(), body);
        return body;
    }

    private static Formula SourceB(bool prime)
    {
        Formula N = F.Id("N"), mu = F.Id("mu"), pi = F.Id("pi"), nu = F.Id("nu");
        Formula same = And(Eq(pi, nu), Eq(Fst(nu), Snd(nu)));
        Formula switched = And(Eq(Fst(pi), Snd(nu)), And(Eq(Snd(pi), Fst(nu)),
            prime ? Lt(Snd(nu), Fst(nu)) : Lt(Fst(nu), Snd(nu))));
        Formula entry = Ite(same, prime ? Sub(D(1), App(mu, Fst(nu))) : App(mu, Fst(nu)), Ite(switched, D(1), D(0)));
        Formula name = prime ? Named("Bprime") : Named("B");
        return Disp(NatBind(All("mu", Arr(Fin(N), Real()), All("pi", PairSpecies(N),
            All("nu", PairSpecies(N), Eq(App(name, N, mu, pi, nu), entry)))), "N"));
    }
    private static Formula AdjacentFormula()
    {
        Formula N = F.Id("N"), n = F.Id("n"), M = F.Id("M"), s = F.Id("s"), pi = F.Id("pi"), nu = F.Id("nu"), r = F.Id("r");
        Formula i = QCall("Fin", "mk", s), j = QCall("Fin", "mk", Add(s, D(1)));
        Formula keep = Ite(Or(Eq(Val(r), s), Eq(Val(r), Add(s, D(1)))), D(1), Ite(Eq(App(pi, r), App(nu, r)), D(1), D(0)));
        Formula product = Seq(new Formula.Subscript(Prod, Seq(r, Colon, Fin(n))), Sp, Parenthesized(keep));
        Formula entry = Ite(Lt(Add(s, D(1)), n), Mul(App(M, Pair(App(pi, i), App(pi, j)), Pair(App(nu, i), App(nu, j))), product), D(0));
        return Disp(NatBind(All("M", Matrix(PairSpecies(N)), All("s", Nat(), All("pi", Word(N, n), All("nu", Word(N, n),
            Eq(Call("adjacent", N, n, M, s, pi, nu), entry))))), "N", "n"));
    }
    private static Formula CalBFormula(bool prime)
    {
        Formula N = F.Id("N"), n = F.Id("n"), mu = F.Id("mu"), j = F.Id("j"), i = F.Id("i");
        Formula name = prime ? Named("calBprime") : Named("calB");
        Formula b = prime ? Named("Bprime") : Named("B");
        return Disp(NatBind(All("mu", Arr(Fin(N), Real()), NatBind(
            Eq(App(name, N, n, mu, j, i), Call("adjacent", N, n, App(b, N, mu), Sub(Add(j, i), D(2)))), "j", "i")), "N", "n"));
    }
    private static Formula SwapWordFormula()
    {
        Formula N = F.Id("N"), n = F.Id("n"), s = F.Id("s"), h = F.Id("h"), w = F.Id("w"), r = F.Id("r");
        Formula swapped = QCall("Equiv", "swap", QCall("Fin", "mk", s), QCall("Fin", "mk", Add(s, D(1))), r);
        return Disp(NatBind(All("h", Lt(Add(s, D(1)), n), All("w", Word(N, n), All("r", Fin(n),
            Eq(App(Call("swapWord", N, n, s, h, w), r), App(w, swapped))))), "N", "n", "s"));
    }
    private static Formula RowAction(bool prime)
    {
        Formula N = F.Id("N"), n = F.Id("n"), mu = F.Id("mu"), j = F.Id("j"), i = F.Id("i"), h = F.Id("h"), f = F.Id("f"), w = F.Id("w");
        Formula s = Sub(Add(j, i), D(2));
        Formula pair = Pair(App(w, QCall("Fin", "mk", s)), App(w, QCall("Fin", "mk", Add(s, D(1)))));
        Formula b = prime ? Named("Bprime") : Named("B");
        Formula cb = prime ? Named("calBprime") : Named("calB");
        Formula lhs = App(QCall("Matrix", "mulVec", App(cb, N, n, mu, j, i), f), w);
        Formula rhs = Mul(App(b, N, mu, pair, Pair(Snd(pair), Fst(pair))), App(f, Call("swapWord", N, n, s, h, w)));
        return Disp(NatBind(All("mu", Arr(Fin(N), Real()), NatBind(All("h", Lt(Add(s, D(1)), n),
            All("f", Arr(Word(N, n), Real()), All("w", Word(N, n), Eq(lhs, rhs)))), "j", "i")), "N", "n"));
    }
    private static Formula WeightsFormula()
    {
        Formula N = F.Id("N"), mu = F.Id("mu"), a = F.Id("a"), pi = F.Id("pi");
        Formula pair = Pair(Snd(pi), Fst(pi));
        Formula b = Call("B", N, mu, pi, pair), bp = App(Named("Bprime"), N, mu, pi, pair);
        Formula range = All("a", Fin(N), And(Le(D(0), App(mu, a)), Le(App(mu, a), D(1))));
        return Disp(NatBind(All("mu", Arr(Fin(N), Real()), Imp(range, All("pi", PairSpecies(N),
            And(Le(D(0), b), And(Le(D(0), bp), Eq(Add(b, bp), D(1))))))), "N"));
    }
    private static Formula PathCall(string name, params Formula[] args) => QCall("Path", name, args);
    private static Formula At(Formula s, Formula x) => App(Snd(s), x);
    private static Formula Row(Formula N, Formula mu, Formula s, bool prime)
    {
        Formula pi = Pair(At(s, Fst(s)), At(s, Add(Fst(s), D(1))));
        Formula name = prime ? Named("Bprime") : Named("B");
        return App(name, N, mu, pi, Pair(Snd(pi), Fst(pi)));
    }
    private static Formula PathSwapFormula()
    {
        Formula N = F.Id("N"), w = F.Id("w"), i = F.Id("i"), x = F.Id("x");
        return Disp(NatBind(All("w", Arr(Int(), Fin(N)), All("i", Int(), All("x", Int(),
            Eq(App(PathCall("swap", N, w, i), x), App(w, QCall("Equiv", "swap", i, Add(i, D(1)), x)))))), "N"));
    }
    private static Formula LeftFormula()
    {
        Formula N = F.Id("N"), pref = F.Id("pref"), s = F.Id("s");
        Formula a = At(s, Fst(s)), b = At(s, Add(Fst(s), D(1)));
        return Disp(NatBind(All("pref", Arr(Fin(N), Named("Bool")), All("s", State(N),
            Eq(PathCall("left", N, pref, s), Ite(Lt(b, a), Named("true"), Ite(Lt(a, b), Named("false"), App(pref, a)))))), "N"));
    }
    private static Formula NextFormula()
    {
        Formula N = F.Id("N"), pref = F.Id("pref"), s = F.Id("s");
        Formula position = Ite(PathCall("left", N, pref, s), Sub(Fst(s), D(1)), Add(Fst(s), D(1)));
        return Disp(NatBind(All("pref", Arr(Fin(N), Named("Bool")), All("s", State(N),
            Eq(PathCall("next", N, pref, s), Pair(position, PathCall("swap", N, Snd(s), Fst(s)))))), "N"));
    }
    private static Formula InteriorFormula()
    {
        Formula N = F.Id("N"), m = F.Id("m"), s = F.Id("s");
        return Disp(NatBind(All("s", State(N), Eq(PathCall("interior", N, m, s),
            And(Le(D(0), Fst(s)), Lt(Fst(s), Parenthesized(Seq(m, Colon, Int())))))), "N", "m"));
    }
    private static Formula PreferredFormula()
    {
        Formula N = F.Id("N"), mu = F.Id("mu"), a = F.Id("a");
        return Disp(NatBind(All("mu", Arr(Fin(N), Real()), All("a", Fin(N),
            Eq(PathCall("preferred", N, mu, a), Call("decide", Le(new Formula.Fraction(D(1), D(2)), App(mu, a)))))), "N"));
    }
    private static Formula StateFormula(bool right)
    {
        Formula N = F.Id("N"), s = F.Id("s");
        Formula position = right ? Add(Fst(s), D(1)) : Sub(Fst(s), D(1));
        return Disp(NatBind(All("s", State(N), Eq(PathCall(right ? "rightState" : "leftState", N, s),
            Pair(position, PathCall("swap", N, Snd(s), Fst(s))))), "N"));
    }
    private static Formula ChosenFormula()
    {
        Formula N = F.Id("N"), mu = F.Id("mu"), s = F.Id("s");
        return Disp(NatBind(All("mu", Arr(Fin(N), Real()), All("s", State(N),
            Eq(PathCall("chosenWeight", N, mu, s), Ite(PathCall("left", N, PathCall("preferred", N, mu), s),
                Row(N, mu, s, false), Row(N, mu, s, true))))), "N"));
    }
    private static Formula ExitFormula()
    {
        Formula N = F.Id("N"), mu = F.Id("mu"), m = F.Id("m"), s = F.Id("s"), l = F.Id("l"), r = F.Id("r"), a = F.Id("a"), b = F.Id("b");
        Formula next = PathCall("next", N, PathCall("preferred", N, mu));
        Formula atL = QCall("Function", "iterate", next, l, s);
        Formula atR = QCall("Function", "iterate", next, r, s);
        Formula product = Seq(new Formula.Subscript(Prod, Seq(r, Colon, Fin(l))), Sp,
            PathCall("chosenWeight", N, mu, QCall("Function", "iterate", next, Val(r), s)));
        Formula edge = Lam("a", State(N), Lam("b", State(N), And(PathCall("interior", N, m, a),
            Or(And(Lt(D(0), Row(N, mu, a, false)), Eq(PathCall("leftState", N, a), b)),
               And(Lt(D(0), Row(N, mu, a, true)), Eq(PathCall("rightState", N, a), b))))));
        Formula conclusion = Some("l", Nat(), And(Le(l, Mul(Mul(D(2), N), m)),
            And(Not(PathCall("interior", N, m, atL)), And(Lt(D(0), product),
            And(All("r", Nat(), Imp(Lt(r, l), PathCall("interior", N, m, atR))),
            QCall("Relation", "ReflTransGen", edge, s, atL))))));
        return Disp(NatBind(All("mu", Arr(Fin(N), Real()), All("s", State(N), conclusion)), "N", "m"));
    }

}
