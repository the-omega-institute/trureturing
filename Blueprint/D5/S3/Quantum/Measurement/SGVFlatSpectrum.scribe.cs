using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class SGVFlatSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/SGVFlatSpectrum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/schoutegrinkosubasivolkoff2024reflections");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit positive probabilities solve the flat-spectrum system for every copy number.",
        H("Flat-spectrum probe probabilities"),
        Blocks(
            Node("S", "The coherent Clebsch–Gordan sum", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source), SumDefinition(),
                "Equation (183), Section 4.2.1, p. 36, uses the coherent sum of the real Condon–Shortley coefficients. Here tj = 2j and i enumerates m = j − i. The displayed function clebschGordan is Racah's source expression; the Lean owner is D5.S3.Quantum.Decoherence.DampedSpinKernelPositivityRefutation.CG. Equality on J ≤ tj and i ≤ tj is established inside equal_spin_coefficient, including the square-root product and the zero terms outside the owner's shorter sum. In the displayed expression, a = 2j₁, b = 2j₂, c = 2J, x = 2m₁, y = 2m₂ and z = 2M. Its first three arguments are natural numbers; every factorial argument and each division inside fz is an integer. Int.ediv denotes Euclidean integer division; Nat.div denotes natural division. The two square roots and all selection rules are retained. The displayed function fz uses Int.toNat before Nat.factorial, so negative integer arguments map to zero before taking the factorial."),
            Node("claim", "Conjecture 4.6 as its linear system", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                Equal(Typed(X("claim"), X("Prop")), ClaimBody()),
                "Section 4.2.1, p. 36: “Conjecture 4.6. The probabilities q_j for j ∈ {(n mod 2)/2, …, n/2} in Eq. (181), which define the probe state Φ_n, could be chosen such that ‖|v_J⟩‖² = 1/binom(n+2, 2) (182) for every J ∈ {(n mod 2), …, n − 2, n}.” The displayed predicate is equation (183). Its k corresponds to j = n/2 − k, and the finite range has Nat.div n 2 + 1 elements. Probabilities are nonnegative and sum to one. Nat.mod selects the allowed parity. Nat subtraction is truncated at zero; the conditional excludes terms with 2j < J. The real coefficient is squared. Equation (181) identifies this system with equation (182) after division by 2J + 1."),
            Node("explicitQ", "The explicit probabilities", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source), ExplicitDefinition(),
                "For k ≤ Nat.div n 2 this expression is strictly positive. Every subtraction in a Nat.choose argument and in the first squared factor is natural subtraction. The quotient and the square are real operations. These probabilities sum to one and solve the coherent system for every n ≥ 1."),
            Node("result", "Existence for every copy number", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source), ClaimBody(),
                "The probabilities explicitQ n give the required distribution. Extracting the common square root from Racah's formula reduces the coherent sum to a rational binomial convolution. Its generating series evaluates the kernel. Two factorial sum identities, proved by telescoping and induction, give normalization and every equation of the system. The proof uses the original coherent sums directly and does not require a polynomial connection identity. Uniqueness is not asserted.")), []));

    private static DocumentBlock Node(string name, string title, DescribeRole role,
        AssessedProvenance provenance, Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("schoute-grinko-subasi-volkoff-2024-flat-spectrum"),
                ResolutionKind.Proved) : null);

    private static Formula SumDefinition()
    {
        var tj = X("tj");
        var j = X("J");
        var i = X("i");
        var cgType = Arrow(Naturals(), Arrow(Naturals(), Arrow(Naturals(),
            Arrow(Integers(), Arrow(Integers(), Arrow(Integers(), Reals()))))));
        var factorial = LambdaOf("x", Integers(),
            Cast(App(Qualified("Nat", "factorial"),
                App(Qualified("Int", "toNat"), X("x"))), Reals()));
        var cg = LambdaOf("a", Naturals(), LambdaOf("b", Naturals(),
            LambdaOf("c", Naturals(), LambdaOf("x", Integers(),
                LambdaOf("y", Integers(), LambdaOf("z", Integers(), RacahBody()))))));
        var sum = SumRange("i", Add(tj, Num(1)), Call("clebschGordan", tj, tj,
            Multiply(Num(2), j), Subtract(Cast(tj, Integers()), Multiply(Num(2), Cast(i, Integers()))),
            Subtract(Multiply(Num(2), Cast(i, Integers())), Cast(tj, Integers())), Num(0)));
        return All("tj", Naturals(), All("J", Naturals(), Equal(Call("S", tj, j),
            LetIn("fz", Arrow(Integers(), Reals()), factorial,
                LetIn("clebschGordan", cgType, cg, sum)))));
    }

    private static Formula RacahBody()
    {
        var a = Cast(X("a"), Integers());
        var b = Cast(X("b"), Integers());
        var c = Cast(X("c"), Integers());
        var x = X("x");
        var y = X("y");
        var z = X("z");
        var k = Cast(X("k"), Integers());
        var ab = Half(Subtract(Add(a, b), c));
        var ax = Half(Subtract(a, x));
        var by = Half(Add(b, y));
        var cbx = Half(Add(Subtract(c, b), x));
        var cay = Half(Subtract(Subtract(c, a), y));
        var valid = Conjoin(Equal(z, Add(x, y)), Leq(c, Add(a, b)), Leq(a, Add(b, c)),
            Leq(b, Add(a, c)), Call("Even", Add(Add(a, b), c)),
            Leq(new Formula.Absolute(x), a), Leq(new Formula.Absolute(y), b),
            Leq(new Formula.Absolute(z), c), Call("Even", Add(a, x)),
            Call("Even", Add(b, y)), Call("Even", Add(c, z)));
        var prefactor = Root(Fraction(Product(Add(Cast(X("c"), Reals()), Num(1)),
            Fz(Half(Subtract(Add(c, a), b))), Fz(Half(Add(Subtract(c, a), b))), Fz(ab)),
            Fz(Add(Half(Add(Add(a, b), c)), Num(1)))));
        var second = Root(Product(Fz(Half(Add(c, z))), Fz(Half(Subtract(c, z))),
            Fz(ax), Fz(Half(Add(a, x))), Fz(Half(Subtract(b, y))), Fz(by)));
        var term = Conditional(Conjoin(Leq(Num(0), Subtract(ab, k)),
                Leq(Num(0), Subtract(ax, k)), Leq(Num(0), Subtract(by, k)),
                Leq(Num(0), Add(cbx, k)), Leq(Num(0), Add(cay, k))),
            Fraction(Power(Parenthesized(Seq(Minus, Num(1))), X("k")),
                Product(Fz(k), Fz(Subtract(ab, k)), Fz(Subtract(ax, k)),
                    Fz(Subtract(by, k)), Fz(Add(cbx, k)), Fz(Add(cay, k)))), Num(0));
        var length = Add(Add(Add(X("a"), X("b")), X("c")), Num(1));
        return Conditional(valid, Product(prefactor, second, SumRange("k", length, term)), Num(0));
    }

    private static Formula ClaimBody()
    {
        var n = X("n");
        var k = X("k");
        var j = X("J");
        var spin = Subtract(n, Multiply(Num(2), k));
        var length = Add(App(Qualified("Nat", "div"), n, Num(2)), Num(1));
        var term = Conditional(Leq(j, spin),
            Multiply(Fraction(Call("q", k), Add(Cast(Typed(spin, Naturals()), Reals()), Num(1))),
                Power(Call("S", spin, j), Num(2))), Num(0));
        var equations = All("J", Naturals(), Implies(Leq(j, n),
            Implies(Equal(App(Qualified("Nat", "mod"), j, Num(2)),
                    App(Qualified("Nat", "mod"), n, Num(2))),
                Equal(Fraction(Add(Multiply(Num(2), Cast(j, Reals())), Num(1)),
                    Cast(Choose(Add(n, Num(2)), Num(2)), Reals())), SumRange("k", length, term)))));
        return All("n", Naturals(), Implies(Leq(Num(1), n), ExistsOf("q",
            Arrow(Naturals(), Reals()), Conjoin(
                All("k", Naturals(), Implies(Leq(k, App(Qualified("Nat", "div"), n, Num(2))),
                    Leq(Num(0), Call("q", k)))),
                Equal(SumRange("k", length, Call("q", k)), Num(1)), equations))));
    }

    private static Formula ExplicitDefinition()
    {
        var n = X("n");
        var k = X("k");
        var numerator = Product(Power(Cast(Typed(Add(Subtract(n, Multiply(Num(2), k)), Num(1)),
                Naturals()), Reals()), Num(2)),
            Cast(Choose(Add(Subtract(Multiply(Num(2), n), Multiply(Num(2), k)), Num(1)), Subtract(n, k)), Reals()),
            Cast(Choose(Multiply(Num(2), k), k), Reals()));
        return All("n", Naturals(), All("k", Naturals(), Equal(Call("explicitQ", n, k),
            Fraction(numerator, Multiply(Power(Typed(Num(4), Reals()), n),
                Cast(Choose(Add(n, Num(2)), Num(2)), Reals()))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Cast(Formula value, Formula type) => Typed(value, type);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(X("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOf(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Conjoin(params Formula[] xs) => xs.Length == 1 ? xs[0] :
        And(Parenthesized(xs[0]), Parenthesized(Conjoin(xs[1..])));
    private static Formula Product(params Formula[] xs) => xs.Aggregate(Multiply);
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Fz(Formula value) => Call("fz", value);
    private static Formula Half(Formula value) => App(Qualified("Int", "ediv"), value, Num(2));
    private static Formula Choose(Formula n, Formula k) => App(Qualified("Nat", "choose"), n, k);
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(Operatorname, Grp(X("fun")), Sp, Typed(X(name), type), Sp, Mapsto, Sp, body);
    private static Formula LetIn(string name, Formula type, Formula value, Formula body) =>
        Parenthesized(Seq(Operatorname, Grp(X("let")), Sp, Typed(X(name), type), Colon, Eq, Sp,
            value, Semi, Sp, body));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(Operatorname, Grp(X("if")), Sp, Parenthesized(condition), Sp,
            Operatorname, Grp(X("then")), Sp, yes, Sp, Operatorname, Grp(X("else")), Sp, no));
    private static Formula SumRange(string name, Formula length, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(X(name), Sp, InMacro, Sp,
            App(Qualified("Finset", "range"), length))), Sp, Parenthesized(body));
}
