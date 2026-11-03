using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class BourasA363347PrimeMultiplicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/BourasA363347PrimeMultiplicity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/bouras2023continuedfractionmultiplicity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every occurring prime other than five has exactly two indices in Bouras A363347.",
        H("Prime Multiplicity in Bouras Continued Fractions"),
        Blocks(
            Paragraph(Text("Indices are natural numbers, including zero; occurrence counts use only indices n at least three. "
                + "Continued fractions are rational, and Rat.den is their positive reduced denominator. "
                + "Natural subtraction is truncated at zero. Set.ncard counts a finite set, and is zero on an infinite set. "
                + "The proof exhibits the occurrence set as a pair, rather than assuming its finiteness.")),
            Node("BourasA356360.nested", "The right-folded inner fraction", NestedFormula(),
                "OEIS A363347, NAME (unpaginated): \"Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-4))))).\" "
                + "For a rational terminal value x, the inner expression is the right fold over k = 2 through n-1. "
                + "List.range' starts at two and has length n-2. The casts into the rationals are explicit.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("BourasA356360.K", "The reciprocal continued fraction", KFormula(),
                "K takes the reciprocal of the inner fraction. Rational division has Lean's total semantics; "
                + "the denominator identity in the proof applies to negative integer terminal values.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("BourasPolynomials.U", "The polynomial for terminal value minus two", UFormula(),
                "The natural polynomial n squared minus two describes the absolute linear denominator for terminal value minus two, at indices at least three.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("BourasPolynomials.cast_U", "Casting the polynomial into a residue ring", CastUFormula(),
                "For n at least three the natural subtraction agrees with subtraction in ZMod m, for every natural modulus m, including zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("BourasRoots.root_fiber_eq_pair", "The two roots in the index interval", RootFiberFormula(),
                "Two indices whose shifted sum is the prime modulus are the complete fiber of their common square. "
                + "The interval assumptions make equality in ZMod p imply equality of the natural representatives.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("BourasRoots.square_residue_pair", "Constructing two admissible square roots", SquarePairFormula(),
                "For either of the displayed shift and residue choices, a square root and its negative give two distinct indices at least three. "
                + "Their shifted sum is p; the small excluded indices cannot square to the stated residue.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("BourasPrimeValues.U_prime_constraints", "Necessary conditions for a prime denominator at minus two", UConstraintsFormula(),
                "A prime denominator is at least seven and divides U n. Its index is below the prime unless n squared equals twice p squared plus two. "
                + "The factorial divisibility bound eliminates larger quotients n divided by p.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("BourasPrimeValues.U_prime_of_root", "A root below the prime gives that denominator", URootFormula(),
                "If p divides U n and exceeds the index, the cofactor cancels against n!/2 and p remains in the reduced denominator.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("BourasA363347.a", "OEIS A363347", SequenceFormula(),
                "OEIS A363347, NAME (unpaginated): \"Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(-4))))).\" "
                + "The terminal value is -4 and the sequence uses the rational denominator, with offset n = 3.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("BourasA363347.claim", "Bouras's Conjecture 3", Disp(Equal(Q("BourasA363347", "claim"), Parenthesized(ClaimBody()))),
                "OEIS A363347, COMMENTS, Conjecture 3 (unpaginated): \"Conjecture 3: Except for 5, the primes all appear exactly twice.\" "
                + "Here p ranges over prime values that occur, excluding five. The counted set consists of every natural index n at least three with a n = p.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("BourasA363347.result", "Exactly two occurrences", Disp(ClaimBody()),
                "For each occurring prime p other than five, the indices are the two roots of (n+1) squared equal to five in ZMod p. "
                + "They lie below p and sum to p-2. Cancellation against n!/2 excludes every other index, so the occurrence set has cardinality two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bouras"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("bouras-" + name.Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula RatType() => Seq(Mathbb, Grp(V("Q")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Divides(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula Pow2(Formula a) => new Formula.Power(a, D(2));
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Zp() => Call("ZMod", V("p"));
    private static Formula U(Formula n) => App(Q("BourasPolynomials", "U"), n);
    private static Formula K(Formula n, Formula x) => App(Q("BourasA356360", "K"), n, x);
    private static Formula Den(Formula q) => App(Q("Rat", "den"), q);
    private static Formula Prime(Formula p) => App(Q("Nat", "Prime"), p);
    private static Formula Guards(Formula[] conditions, Formula conclusion)
    {
        for (var i = conditions.Length - 1; i >= 0; i--) conclusion = Imp(conditions[i], conclusion);
        return conclusion;
    }

    private static Formula NestedFormula()
    {
        var k = V("k"); var t = V("t"); var n = V("n"); var x = V("x");
        var step = Seq(Operatorname, Grp(V("fun")), Sp,
            Parenthesized(Seq(k, Colon, Sp, NatType())), Sp,
            Parenthesized(Seq(t, Colon, Sp, RatType())), Sp, Mapsto, Sp,
            Subtract(Cast(k, RatType()), new Formula.Fraction(Add(Cast(k, RatType()), D(1)), t)));
        var range = App(Seq(Q("List", "range"), Apos), D(2), Subtract(n, D(2)));
        var body = App(Q("List", "foldr"), Parenthesized(step), x, range);
        return Disp(All("n", NatType(), All("x", RatType(),
            Equal(App(Q("BourasA356360", "nested"), n, x), body))));
    }
    private static Formula KFormula() => Disp(All("n", NatType(), All("x", RatType(),
        Equal(K(V("n"), V("x")), new Formula.Fraction(D(1), App(Q("BourasA356360", "nested"), V("n"), V("x")))))));
    private static Formula UFormula() => Disp(All("n", NatType(), Equal(U(V("n")), Subtract(Pow2(V("n")), D(2)))));
    private static Formula CastUFormula() => Disp(All("n", NatType(), All("m", NatType(),
        Imp(Leq(D(3), V("n")), Equal(Cast(U(V("n")), Call("ZMod", V("m"))),
            Subtract(Pow2(Cast(V("n"), Call("ZMod", V("m")))), D(2)))))));
    private static Formula Shift(Formula n) => Add(n, V("s"));
    private static Formula ShiftSquare(Formula n) => Pow2(Cast(Cast(Shift(n), NatType()), Zp()));
    private static Formula RootFiberFormula()
    {
        var p = V("p"); var r = V("r"); var q = V("q"); var s = V("s"); var n = V("n");
        var set = Seq(OpenBrace, n, Colon, Sp, NatType(), Sp, Mid, Sp,
            And(Leq(D(3), n), And(Less(Shift(n), p), Equal(ShiftSquare(n), ShiftSquare(r)))), CloseBrace);
        var pair = Seq(OpenBrace, r, Comma, Sp, q, CloseBrace);
        var body = Guards([Prime(p), Leq(D(3), r), Leq(D(3), q), Less(Shift(r), p), Less(Shift(q), p),
            Equal(Add(Add(r, q), Multiply(D(2), s)), p)], Equal(set, pair));
        return Disp(All("p", NatType(), All("s", NatType(), All("r", NatType(), All("q", NatType(), body)))));
    }
    private static Formula SquarePairFormula()
    {
        var p = V("p"); var s = V("s"); var c = V("c"); var z = V("z"); var r = V("r"); var q = V("q");
        var cfg = Or(And(Equal(s, D(0)), And(Equal(c, D(2)), Leq(D(7), p))),
            And(Equal(s, D(1)), And(Equal(c, D(5)), Leq(D(1, 1), p))));
        var pair = Some("r", NatType(), Some("q", NatType(),
            And(Leq(D(3), r), And(Leq(D(3), q), And(Less(Shift(r), p), And(Less(Shift(q), p),
            And(NotEqual(r, q), And(Equal(Add(Add(r, q), Multiply(D(2), s)), p), Equal(ShiftSquare(r), Cast(c, Zp()))))))))));
        return Disp(All("p", NatType(), All("s", NatType(), All("c", NatType(),
            Guards([Prime(p), cfg], All("z", Zp(), Imp(Equal(Pow2(z), Cast(c, Zp())), pair)))))));
    }
    private static Formula UConstraintsFormula()
    {
        var n = V("n"); var p = V("p");
        return Disp(All("n", NatType(), All("p", NatType(), Guards(
            [Leq(D(3), n), Prime(p), Equal(Den(K(n, Seq(Minus, D(2)))), p)],
            And(Leq(D(7), p), And(Divides(p, U(n)), Or(Less(n, p),
                Equal(Pow2(n), Add(Multiply(D(2), Pow2(p)), D(2))))))))));
    }
    private static Formula URootFormula()
    {
        var n = V("n"); var p = V("p");
        return Disp(All("n", NatType(), All("p", NatType(), Guards(
            [Leq(D(3), n), Prime(p), Less(n, p), Divides(p, U(n))],
            Equal(Den(K(n, Seq(Minus, D(2)))), p)))));
    }
    private static Formula A(Formula n) => App(Q("BourasA363347", "a"), n);
    private static Formula SequenceFormula() => Disp(All("n", NatType(),
        Equal(A(V("n")), Den(K(V("n"), Seq(Minus, D(4)))))));
    private static Formula Occurrences() => Seq(OpenBrace, V("n"), Colon, Sp, NatType(), Sp, Mid, Sp,
        And(Leq(D(3), V("n")), Equal(A(V("n")), V("p"))), CloseBrace);
    private static Formula ClaimBody() => All("p", NatType(), Guards(
        [Prime(V("p")), NotEqual(V("p"), D(5)), Some("n", NatType(),
            And(Leq(D(3), V("n")), Equal(A(V("n")), V("p"))))],
        Equal(App(Q("Set", "ncard"), Occurrences()), D(2))));
}
