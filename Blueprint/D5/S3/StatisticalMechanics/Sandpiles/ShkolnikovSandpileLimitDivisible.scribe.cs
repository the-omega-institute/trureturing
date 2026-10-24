using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Sandpiles;

internal sealed class ShkolnikovSandpileLimitDivisibleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Sandpiles/ShkolnikovSandpileLimitDivisible.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/shkolnikov2025sandpilelimits");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The direct limit of the rectangular sandpile groups with Shkolnikov's signed reflected tiling maps is divisible: every element has a multiple-root at a later rectangular stage.",
        H("Divisibility of the rectangular sandpile limit"),
        Blocks(
            SourceQuotation(),
            Node("circle", "The circle-valued carrier", CircleFormula(),
                "The carrier is the additive circle ℝ/ℤ.", "T", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("rectangle", "The open rectangular domain", InRectFormula(),
                "InRect p q z means that both integer coordinates of z lie strictly between the corresponding rectangle boundaries.",
                "InRect", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("harmonic", "Rectangular sandpile functions", IsSandpileFormula(),
                "A rectangular sandpile function vanishes outside the open rectangle and satisfies the four-neighbour harmonic equation at every point inside it.",
                "IsSandpile", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("unfold", "The reflected one-dimensional coordinate", UnfoldFormula(),
                "The unfolded coordinate subtracts an even tile index and reflects an odd tile index, using integer division and remainder.",
                "unfold", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("embedding", "The signed reflected embedding", EmbedFormula(),
                "The embedding extends a function by zero and evaluates it at the reflected coordinates, multiplied by the sign determined by the two tile indices.",
                "embed", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Divisibility of the direct limit", ClaimBody(),
                "For every positive rectangle, harmonic function, and positive integer k, a later rectangle contains a harmonic function whose k-fold sum is the signed reflected image of the original function.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Divisibility theorem", ClaimBody(),
                "The reversible row recurrence closes on a finite denominator subgroup. Its period supplies a taller rectangle, and multiplying the lifted rows by k recovers the signed reflected embedding of the original harmonic function.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))
        ), []));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Mikhail Shkolnikov, Algebraic Limits of Sandpiles, arXiv:2506.09912v3 (2 September 2025), Section 3, p. 8. "
        + "The paper states verbatim: “Let Γ(p, q) be the portion of the square lattice given by the intersection with an open rectangle (0, p) × (0, q), where p and q are positive integers.” "
        + "It defines the rectangular monomorphism by the signed reflected formula and, after Proposition 5, states verbatim: “For instance, one may expect that it is a rational subtorus or a divisible group.”"));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("shkolnikov-sandpile-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula T() => F.Id("T");
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula PairType(Formula left, Formula right) => Call("Prod", left, right);
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Fst(Formula value) => Call("Prod.fst", value);
    private static Formula Snd(Formula value) => Call("Prod.snd", value);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula CastNat(Formula value) => Call("Int.ofNat", value);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        Parenthesized(new Formula.TypeArrow(domain, codomain));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula NegateFormula(Formula value) => new Formula.Negate(value);
    private static Formula Pow(Formula left, Formula right) => new Formula.Power(left, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Not(Formula value) => Seq(FormulaDsl.Neg, Parenthesized(value));
    private static Formula Smul(Formula scalar, Formula value) => Call("HSMul.hSMul", scalar, value);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, Parenthesized(body));
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, Parenthesized(body));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Call("ite", condition, yes, no);

    private static Formula CircleFormula() =>
        Eq(F.Id("T"), Call("AddCircle", Typed(D(1), Real())));

    private static Formula InRectFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q"), z = F.Id("z");
        Formula x = Fst(z), y = Snd(z);
        Formula body = And(Lt(D(0), x), And(Lt(x, CastNat(p)), And(Lt(D(0), y), Lt(y, CastNat(q)))));
        return All("p", Nat(), All("q", Nat(), All("z", PairType(Int(), Int()),
            Eq(App(F.Id("InRect"), p, q, z), body))));
    }

    private static Formula IsSandpileFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q"), f = F.Id("f"), z = F.Id("z");
        Formula point = PairType(Int(), Int());
        Formula fType = Arrow(point, T());
        Formula outside = All("z", point,
            Imp(Not(App(F.Id("InRect"), p, q, z)), Eq(App(f, z), D(0))));
        Formula centre = Smul(Typed(D(4), Int()), App(f, z));
        Formula neighbours = Add(Add(App(f, Pair(Sub(Fst(z), D(1)), Snd(z))),
            App(f, Pair(Add(Fst(z), D(1)), Snd(z)))),
            Add(App(f, Pair(Fst(z), Sub(Snd(z), D(1)))),
                App(f, Pair(Fst(z), Add(Snd(z), D(1))))));
        Formula inside = All("z", point,
            Imp(App(F.Id("InRect"), p, q, z), Eq(centre, neighbours)));
        return All("p", Nat(), All("q", Nat(), All("f", fType,
            Eq(App(F.Id("IsSandpile"), p, q, f), And(outside, inside)))));
    }

    private static Formula UnfoldFormula()
    {
        Formula p = F.Id("p"), x = F.Id("x"), div = Call("Int.ediv", x, CastNat(p));
        Formula rem = Call("Int.emod", div, D(2));
        Formula rhs = IfThenElse(Eq(rem, D(0)), Sub(x, Mul(div, CastNat(p))),
            Sub(Mul(Add(div, D(1)), CastNat(p)), x));
        return All("p", Nat(), All("x", Int(),
            Eq(App(F.Id("unfold"), p, x), rhs)));
    }

    private static Formula EmbedFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q"), m = F.Id("m"), n = F.Id("n");
        Formula phi = F.Id("phi"), z = F.Id("z");
        Formula point = PairType(Int(), Int());
        Formula phiType = Arrow(point, T());
        Formula x = Fst(z), y = Snd(z);
        Formula tileX = Call("Int.ediv", x, CastNat(p));
        Formula tileY = Call("Int.ediv", y, CastNat(q));
        Formula sign = Pow(Typed(NegateFormula(D(1)), Int()), Call("Int.toNat", Add(tileX, tileY)));
        Formula value = Smul(sign, App(phi,
            Pair(App(F.Id("unfold"), p, x), App(F.Id("unfold"), q, y))));
        Formula body = IfThenElse(App(F.Id("InRect"), Mul(m, p), Mul(n, q), z), value, D(0));
        return All("p", Nat(), All("q", Nat(), All("m", Nat(), All("n", Nat(),
            All("phi", phiType, All("z", point,
                Eq(App(F.Id("embed"), p, q, m, n, phi, z), body)))))));
    }

    private static Formula ClaimBody()
    {
        Formula p = F.Id("p"), q = F.Id("q"), f = F.Id("f"), k = F.Id("k");
        Formula point = PairType(Int(), Int());
        Formula fType = Arrow(point, T());
        Formula gType = fType;
        Formula roots = Ex("m", Nat(), Ex("n", Nat(),
            And(Le(D(1), F.Id("m")), And(Le(D(1), F.Id("n")),
                Ex("g", gType, And(
                    App(F.Id("IsSandpile"), Mul(F.Id("m"), p), Mul(F.Id("n"), q), F.Id("g")),
                    Eq(Smul(k, F.Id("g")), App(F.Id("embed"), p, q, F.Id("m"), F.Id("n"), f))))))));
        return All("p", Nat(), All("q", Nat(),
            Imp(Le(D(1), p), Imp(Le(D(1), q), All("f", fType,
                Imp(App(F.Id("IsSandpile"), p, q, f), All("k", Nat(),
                    Imp(Le(D(1), k), roots))))))));
    }
}
