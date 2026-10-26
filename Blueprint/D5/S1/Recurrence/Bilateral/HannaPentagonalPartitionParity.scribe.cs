using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Bilateral;

internal sealed class HannaPentagonalPartitionParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Bilateral/HannaPentagonalPartitionParity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Recurrence/hanna2023a361552");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal pentagonal unit equation and Hanna's ordinary-partition parity assertion.",
        H("Hanna's pentagonal partition parity"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS A361552 defines an integral formal unit A by "
                + "2*x = sum over every integer k of x^(k*(3*k+1)/2) "
                + "times (A^(3*k)-A^(-(3*k+1))). The conjecture states that for every "
                + "integer n at least one its coefficient is even, and its integer half "
                + "has the parity of the ordinary partitions of n-1.")),
            Paragraph(Text("PowerSeries denotes formal series, X its variable, and the superscript "
                + "unit group makes all negative powers defined. A coefficient window is an "
                + "interval of integer summation indices. The topology is the product topology "
                + "of coefficients; no analytic convergence is involved. The symbol val is Units.val, unit(F,G) is the unit with value F and inverse G "
                + "after its two inverse laws have been supplied, mk builds a series from its "
                + "coefficients, intCast casts a natural number to the integers, and ediv is "
                + "integer division. NatPartition is Nat.Partition and card is Fintype.card. "
                + "Integer coefficient division and remainder occur only after evenness has been proved.")),
            Node("exponent", "The exact pentagonal exponent", "Mathlib's pentagonal number at -k "
                + "is k*(3*k+1)/2. Its exact multiplication-by-two identity proves integrality; "
                + "the natural value is nonnegative and is at least the absolute value of k.", DescribeRole.Definition),
            Node("term", "The complete integer-index summand", "Both powers are powers of the "
                + "same integral unit. The exponent bound forces each monomial separately to "
                + "vanish at degree N outside [-N,N].", DescribeRole.Definition),
            Node("bilateral", "The full sum by coefficient windows", "At each degree this window "
                + "contains every possibly nonzero integer summand. The HasSum clause below "
                + "identifies it with the entire bilateral sum.", DescribeRole.Definition),
            Node("Original", "The original equation", "The equation imposes no initial constant "
                + "coefficient. Its degree-zero term is 1-A inverse, forcing that coefficient "
                + "to be one.", DescribeRole.Definition),
            Node("generatingSeries", "The constructed integral series", "Remove the zero-index "
                + "term and call the rest S(A). The iteration sends a unit A to the reciprocal "
                + "of 1-2*X+S(A), whose constant coefficient is one. Agreement through degree "
                + "d-1 improves through degree d. The nth coefficient is read after n+1 "
                + "iterations starting at the unit one. Stabilization proves the original "
                + "equation and equality with every other original unit solution.", DescribeRole.Definition),
            Node("generatingUnit", "The inhabited unit solution", "The constructed series has "
                + "constant coefficient one. Its inverse is the formal invOfUnit at that "
                + "constant unit; both inverse laws are kernel proofs.", DescribeRole.Definition),
            Node("partitionCount", "Ordinary partitions", "Nat.Partition n consists of ordinary "
                + "positive-part partitions of n. Its cardinality at zero is one.", DescribeRole.Definition),
            Node("partitionSeries", "The partition generating function", "The coefficients are "
                + "these ordinary cardinalities cast to integers. The product supplier "
                + "Nat.Partition.hasProd_powerSeriesMk_card_restricted is applied at predicate "
                + "True. Euler's pentagonal product and the geometric-factor inverse prove "
                + "that this series is the reciprocal of pentagonalSeries over the integers.", DescribeRole.Definition),
            Node("partition_reciprocal", "The partition series is the pentagonal reciprocal",
                "Euler's product and the geometric factors show that pentagonalSeries over the integers multiplied by the ordinary partition series is one.", DescribeRole.Theorem),
            Node("a", "The integer-index coefficients", "At a nonnegative integer n this reads "
                + "the coefficient at n.toNat. Negative indices are zero; the stated parity "
                + "range starts at one.", DescribeRole.Definition),
            Node("LiteralResolution", "All clauses of the original-domain assertion", "The "
                + "clauses give exponent validity, local finiteness of both monomials, the "
                + "whole bilateral HasSum, integral unit existence, forced constant coefficient "
                + "one, uniqueness among every original unit solution, all positive integer "
                + "indices, the unique empty partition, and the signed-index correspondence.", DescribeRole.Definition),
            Node("result", "The literal partition-parity assertion", "Map the original unit "
                + "equation to characteristic two and use uniqueness to obtain A=1 there. "
                + "Thus A=1+2*B with integral B defined by exact coefficient division. In "
                + "characteristic four this unit squares to one. Reducing integer powers "
                + "modulo two and multiplying Euler signs by two gives "
                + "2*(B*pentagonalSeries-X)=0 modulo four. Coefficientwise integer divisibility "
                + "4 divides 2*c implies 2 divides c; no nonunit cancellation is made in "
                + "characteristic four. The ordinary-partition reciprocal then gives "
                + "B=X*partitionSeries modulo two. The identity "
                + "n.toNat=(n-1).toNat+1 for n at least one completes the integer-index "
                + "coefficient statement.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a361552-literal-partition-parity"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a361552-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Statement(name)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Add(Formula x, Formula y) => Seq(Par(x), Sp, Plus, Sp, Par(y));
    private static Formula Sub(Formula x, Formula y) => Seq(Par(x), Sp, Minus, Sp, Par(y));
    private static Formula Mul(Formula x, Formula y) => Seq(Par(x), Sp, Cdot, Sp, Par(y));
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(Par(x), y);
    private static Formula Negate(Formula x) => Seq(Minus, Par(x));
    private static Formula And(Formula x, Formula y) => Seq(Par(x), Sp, Land, Sp, Par(y));
    private static Formula ImpliesF(Formula x, Formula y) => Seq(Par(x), Sp, Implies, Sp, Par(y));
    private static Formula Leq(Formula x, Formula y) => Seq(x, Sp, Le, Sp, y);
    private static Formula Bound(string name, Formula type) => Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula All(string name, Formula type, Formula body) => Seq(Bound(name, type), body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Par(Seq(F.Id(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series(Formula r) => Call("PowerSeries", r);
    private static Formula Units(Formula r) => Call("Units", Series(r));
    private static Formula Coeff(Formula n, Formula a) => Call("coeff", n, a);
    private static Formula Window(Formula n) => Call("Icc", Negate(Call("intCast", n)), Call("intCast", n));
    private static Formula E(Formula k) => Call("exponent", k);
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula X() => F.Id("X");
    private static Formula R() => F.Id("R");
    private static Formula WithRing(Formula body) => Seq(Bound("R", Named("Type")),
        OpenBracket, Call("CommRing", R()), CloseBracket, Sp, body);
    private static Formula SumWindow(Formula n, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id("k"), Sp, InMacro, Sp, Window(n))), Sp, Par(body));
    private static Formula Denominator(Formula a) => Add(Sub(D(1), Mul(D(2), X())), Call("nonzeroSum", a));
    private static Formula Body()
    {
        Formula k = F.Id("k"), a = F.Id("A"), n = F.Id("n"), degree = F.Id("N");
        Formula integerE = Call("intCast", E(k));
        Formula quadratic = Mul(k, Add(Mul(D(3), k), D(1)));
        Formula exponents = All("k", Integers(), And(Eqn(integerE, Call("ediv", quadratic, D(2))),
            And(Leq(D(0), integerE), Eqn(Mul(D(2), integerE), quadratic))));
        Formula first = Mul(Pow(X(), E(k)), Val(Pow(a, Mul(D(3), k))));
        Formula second = Mul(Pow(X(), E(k)), Val(Pow(a, Negate(Add(Mul(D(3), k), D(1))))));
        Formula outside = Seq(Neg, Sp, Par(Seq(k, Sp, InMacro, Sp, Window(degree))));
        Formula finite = All("A", Units(Integers()), All("N", Naturals(), All("k", Integers(),
            ImpliesF(outside, And(Eqn(Coeff(degree, first), D(0)), Eqn(Coeff(degree, second), D(0)))))));
        Formula sum = All("A", Units(Integers()), Call("HasSum",
            Lambda("k", Integers(), Call("term", a, k)), Call("bilateral", a)));
        Formula c = Coeff(Call("toNat", n), Val(a));
        Formula parity = All("n", Integers(), ImpliesF(Leq(D(1), n), And(
            Seq(D(2), Sp, Mid, Sp, c), Eqn(new Formula.Modulo(Call("ediv", c, D(2)), D(2)),
                new Formula.Modulo(Call("intCast", Call("partitionCount", Call("toNat", Sub(n, D(1))))), D(2))))));
        Formula gu = Call("generatingUnit", Integers());
        Formula solutions = All("A", Units(Integers()), ImpliesF(Call("Original", a),
            And(Eqn(Call("constantCoeff", Val(a)), D(1)), And(Eqn(a, gu), parity))));
        Formula index = All("n", Integers(), ImpliesF(Leq(D(0), n), Eqn(Call("a", n),
            Coeff(Call("toNat", n), Call("generatingSeries", Integers())))));
        return And(exponents, And(finite, And(sum, And(Call("Original", gu), And(solutions,
            And(Eqn(Call("partitionCount", D(0)), D(1)), index))))));
    }
    private static Formula Statement(string name)
    {
        Formula k = F.Id("k"), a = F.Id("A"), n = F.Id("n"), d = F.Id("d");
        return name switch
        {
            "exponent" => Disp(All("k", Integers(), Eqn(E(k), Call("pentagonal", Negate(k))))),
            "term" => Disp(WithRing(All("A", Units(R()), All("k", Integers(),
                Eqn(Call("term", a, k), Mul(Pow(X(), E(k)), Sub(Val(Pow(a, Mul(D(3), k))),
                    Val(Pow(a, Negate(Add(Mul(D(3), k), D(1)))))))))))),
            "bilateral" => Disp(WithRing(All("A", Units(R()), Eqn(Call("bilateral", a),
                Call("mk", Lambda("n", Naturals(), SumWindow(n, Coeff(n, Call("term", a, k))))))))),
            "Original" => Disp(WithRing(All("A", Units(R()), Seq(Call("Original", a), Sp, Iff, Sp,
                Eqn(Call("bilateral", a), Mul(D(2), X())))))),
            "generatingSeries" => Disp(new Formula.Aligned([
                WithRing(All("A", Units(R()), Eqn(Call("nonzeroSum", a), Call("mk", Lambda("n", Naturals(), Seq(
                    new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, Call("erase", Window(n), D(0)))), Sp,
                    Par(Coeff(n, Call("term", a, k))))))))),
                WithRing(Eqn(Call("approximation", R(), D(0)), D(1))),
                WithRing(All("d", Naturals(), Eqn(Call("approximation", R(), Add(d, D(1))), Call("step", Call("approximation", R(), d))))),
                WithRing(All("A", Units(R()), Eqn(Call("step", a), Call("unit",
                    Call("invOfUnit", Denominator(a), D(1)), Denominator(a))))),
                WithRing(Eqn(Call("generatingSeries", R()), Call("mk", Lambda("n", Naturals(),
                    Coeff(n, Val(Call("approximation", R(), Add(n, D(1)))))))))])),
            "generatingUnit" => Disp(WithRing(Eqn(Call("generatingUnit", R()), Call("unit",
                Call("generatingSeries", R()), Call("invOfUnit", Call("generatingSeries", R()), D(1)))))),
            "partitionCount" => Disp(All("n", Naturals(), Eqn(Call("partitionCount", n), Call("card", Call("NatPartition", n))))),
            "partitionSeries" => Disp(Eqn(Named("partitionSeries"), Call("mk", Lambda("n", Naturals(),
                Call("intCast", Call("partitionCount", n)))))),
            "partition_reciprocal" => Disp(Eqn(Mul(Call("pentagonalSeries", Integers()), Named("partitionSeries")), D(1))),
            "a" => Disp(All("n", Integers(), Eqn(Call("a", n), Call("ifThenElse", Leq(D(0), n),
                Coeff(Call("toNat", n), Call("generatingSeries", Integers())), D(0))))),
            "LiteralResolution" => Disp(Seq(Named("LiteralResolution"), Sp, Iff, Sp, Par(Body()))),
            "result" => Disp(Body()),
            _ => throw new System.InvalidOperationException("Unknown declaration " + name)
        };
    }
}
