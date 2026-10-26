using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class BorsPanarioWangArithmeticComplexityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/borspanariowang2023cyclotomic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic complexity of singleton partitions has a positive normalized lower limit.",
        H("Arithmetic complexity of singleton partitions"),
        Blocks(
            Paragraph(Text(
                "A family of congruences separates the residues modulo m when no two standard "
                + "representatives have the same truth values for all its tests. For each prime p "
                + "dividing m, tests whose moduli lack the full p-power are constant on the fibres "
                + "modulo m/p. Representatives outside the remaining tests inject into those fibres. "
                + "Counting these representatives and summing prime-power charges bounds the sum of "
                + "the prime-power totients by the number of tests. A finite least-common-multiple "
                + "estimate and Chebyshev's bound then give a normalized ratio at least 1/64 whenever "
                + "log m is at least 64. All logarithms are real natural logarithms; the lower limit "
                + "is in EReal, with the natural index tending to infinity.")),
            Node("MCongruence", "Congruences with modulus dividing m", CongruenceFormula(),
                "Pages 10-11: \"For a given positive integer m, we define the notion of an "
                + "m-(in)congruence to be an (in)congruence of the form ν(x ≡ b (mod a)) where "
                + "ν ∈ {∅, ¬} is a “logical sign”, and a, b are integers with a ≥ 1 and a | m.\" "
                + "The record stores the positive modulus a as a natural number, b as an integer, "
                + "and proofs of 1 ≤ a and a ∣ m. Positive integer moduli and positive natural "
                + "moduli describe the same congruences. The displayed braces list its fields.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("MCongruence.Holds", "Truth of a congruence", HoldsFormula(),
                "Page 10: \"We identify the elements of Z/mZ with their standard representatives "
                + "in {0, 1, . . . , m − 1}.\" Holds evaluates x ≡ b (mod a) by Int.ModEq, "
                + "with the natural representative and modulus cast to integers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("SpansTrivial", "Separation of standard representatives", SpansFormula(),
                "Definition 1.5(1), pages 10-11: \"There is a unique partition of Z/mZ, which we "
                + "denote by P(x ≡ b_j (mod a_j) : j = 1, 2, . . . , K), such that each block of "
                + "this partition is the solution set modulo m of a system of m-CCs of the form\" "
                + "ν_1(x ≡ b_1 (mod a_1)), …, ν_K(x ≡ b_K (mod a_K)). Section 6.3, page 188, "
                + "calls T_m \"the trivial partition T_m of Z/mZ, all of whose blocks are singletons\". "
                + "Thus the partition is T_m precisely when equality of all test truth values "
                + "forces equality of the two representatives. Fin K indexes exactly K tests.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("acTrivial", "Minimum number of separating congruences", ComplexityFormula(),
                "Definition 1.5(3), page 11: \"When P is an arithmetic partition of Z/mZ, then "
                + "the smallest value of K ∈ N_0 such that P is spanned by K suitably chosen "
                + "m-congruences is called the (arithmetic) complexity of P, written AC(P).\" "
                + "The natural-number infimum is taken over exactly the separating families. "
                + "This set is nonempty for positive m, since the congruences x ≡ j (mod m) "
                + "separate all standard representatives.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Affirmative answer to Question 6.3.1", ClaimFormula(),
                "Question 6.3.1, page 189: \"Is it true that lim inf_{m→∞} "
                + "AC(T_m)/(log² m/log log m) > 0?\" The displayed proposition is the "
                + "affirmative answer, with acTrivial m for AC(T_m), real division and "
                + "coercion of the normalized ratio into EReal before Filter.liminf.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Positive normalized lower limit", Disp(ClaimBody()),
                "The prime-power separation estimate and Chebyshev's bound yield the eventual "
                + "real lower bound 1/64. Its positive image in EReal is a lower bound for the "
                + "lower limit, proving the full displayed proposition.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "bors-panario-wang-2023-arithmetic-complexity-question-6-3-1"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(name switch
        {
            "MCongruence" => "bpw631-congruence",
            "MCongruence.Holds" => "bpw631-holds",
            "SpansTrivial" => "bpw631-separation",
            "acTrivial" => "bpw631-complexity",
            _ => "bpw631-" + name,
        }),
        DeclarationHandle.Create(Prefix + (name == "MCongruence.Holds" ? "Holds" : name)), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Named("Nat");
    private static Formula Z() => Named("Int");
    private static Formula R() => Named("Real");
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOf(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula MC(Formula m) => Call("MCongruence", m);
    private static Formula Holds(Formula c, Formula x) => App(Qualified("MCongruence", "Holds"), c, x);

    private static Formula CongruenceFormula()
    {
        var m = F.Id("m");
        var a = F.Id("a");
        var b = F.Id("b");
        return Disp(All("m", N(), Seq(MC(m), Colon, Named("Type"), Sp, OpenBrace,
            a, Colon, N(), Semi, Sp, b, Colon, Z(), Semi, Sp,
            Leq(D(1), a), Semi, Sp,
            new Formula.Relation(a, FormulaRelationOperator.Divides, m), CloseBrace)));
    }

    private static Formula HoldsFormula()
    {
        var m = F.Id("m");
        var c = F.Id("c");
        var x = F.Id("x");
        var body = App(Qualified("Int", "ModEq"),
            Cast(App(Qualified("MCongruence", "a"), c), Z()), Cast(x, Z()), App(Qualified("MCongruence", "b"), c));
        return Disp(All("m", N(), All("c", MC(m), All("x", N(),
            Logic(Holds(c, x), FormulaLogicOperator.Iff, body)))));
    }

    private static Formula SpansFormula()
    {
        var m = F.Id("m");
        var k = F.Id("K");
        var c = F.Id("c");
        var x = F.Id("x");
        var y = F.Id("y");
        var j = F.Id("j");
        var tests = All("j", Call("Fin", k), Logic(Holds(App(c, j), x),
            FormulaLogicOperator.Iff, Holds(App(c, j), y)));
        var body = All("x", N(), All("y", N(),
            Logic(Less(x, m), FormulaLogicOperator.Implies,
                Logic(Less(y, m), FormulaLogicOperator.Implies,
                    Logic(tests, FormulaLogicOperator.Implies, Equal(x, y))))));
        return Disp(All("m", N(), All("K", N(),
            All("c", new Formula.TypeArrow(Call("Fin", k), MC(m)),
                Logic(Call("SpansTrivial", c), FormulaLogicOperator.Iff, body)))));
    }

    private static Formula ComplexityFormula()
    {
        var m = F.Id("m");
        var k = F.Id("K");
        var c = F.Id("c");
        var candidates = Seq(OpenBrace, k, Colon, N(), Sp, Mid, Sp,
            Parenthesized(ExistsOf("c", new Formula.TypeArrow(Call("Fin", k), MC(m)),
                Call("SpansTrivial", c))), CloseBrace);
        return Disp(All("m", N(), Equal(Call("acTrivial", m), Call("sInf", candidates))));
    }

    private static Formula ClaimBody()
    {
        var m = F.Id("m");
        var log = App(Qualified("Real", "log"), Cast(m, R()));
        var loglog = App(Qualified("Real", "log"), log);
        var denominator = new Formula.Fraction(new Formula.Power(log, D(2)), loglog);
        var ratio = new Formula.Fraction(Cast(Call("acTrivial", m), R()), denominator);
        var function = Parenthesized(Seq(Named("fun"), Sp, m, Colon, N(), Sp, Mapsto, Sp,
            Cast(Cast(ratio, R()), Named("EReal"))));
        var lowerLimit = App(Qualified("Filter", "liminf"), function, Qualified("Filter", "atTop"));
        return Less(D(0), lowerLimit);
    }

    private static Formula ClaimFormula() => Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, ClaimBody()));
}
