using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class GawronUlasFactorialSignConjectureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/gawronulas2022partitions");
    private const string ConjectureQuote =
        "Conjecture 4.4 (p. 11): \"Let m ∈ N≥2 and take U_m = {i! : i = 1, . . . , m}. "
        + "Then, for each k ∈ {0, . . . , m − 2}, (−1)^⌊(n+1)/2⌋ S_{U_m,k}(n) ≥ 0 for n ≫ 0, "
        + "i.e., the sequence of signs of the sequence (S_{U_m,k}(n))_{n∈N} is eventually "
        + "periodic of period 4. Moreover, if k ≥ m − 1 then (−1)^n S_{U_m,k}(n) ≥ 0 for n ≫ 0.\"";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Factorial partition signs fail on an unbounded even progression.",
        H("Factorial Partition Signs: Conjecture 4.4 is False"),
        Blocks(
            Paragraph(Text(
                "The statements are from arXiv:2202.05221v1. The integers n and k are nonnegative. "
                + "Nat.Partition n represents unordered "
                + "partitions into positive parts, including the empty partition of zero. "
                + "The integer power at exponent zero is one, including 0^0. "
                + "Nat.div denotes natural-number division, so Nat.div(n+1,2) is the floor "
                + "of (n+1)/2. Each threshold N may depend on m and k.")),
            Node("partition-count", "Partitions with a specified number of parts", CFormula(),
                "Pages 1–2: \"Let A ⊂ N+ be given and take n ∈ N. By an A-partition "
                + "λ = (λ_1, . . . , λ_k) with parts in A, of a non-negative integer n, we mean "
                + "a representation of n in the form n = λ_1 + . . . + λ_k, where λ_i ∈ A. "
                + "The representations of n differing only in order of the terms are counted "
                + "as one.\" \"c_A(i, n) is the number of A-partitions of n with exactly i parts.\" "
                + "The filter tests membership of every part in A and equality of the part "
                + "count with i. Allowing zero in the carrier of A changes no partition, "
                + "because every part of Nat.Partition n is positive.",
                "c", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weighted-sum", "The signed weighted partition sum", SFormula(),
                "Page 2: \"S_{A,k}(n) = Σ_{i=0}^{n} (−1)^i i^k c_A(i, n)\". "
                + "The range includes both endpoints 0 and n. The powers and products "
                + "are in the integers; the counts are cast from the natural numbers.",
                "S", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("factorial-set", "The factorial part set", UFormula(),
                "Page 11: \"Let m ∈ N≥2 and take U_m = {i! : i = 1, . . . , m}.\" "
                + "Set membership identifies repeated values. In particular U 3 is {1,2,6}.",
                "U", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-four-four", "Both assertions of Conjecture 4.4",
                Disp(Iff(F.Id("claim"), Parenthesized(ClaimBody()))),
                ConjectureQuote + " The two assertions are conjoined. The expression n ≫ 0 "
                + "means that there exists a threshold N such that every n ≥ N satisfies "
                + "the inequality. The floor in the first assertion is Nat.div.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-refuted", "The eventual alternating sign fails",
                Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "For U 3 = {1,2,6} and k=2, multiplicities of 2 and 6 parametrize the "
                + "partitions. Alternating quadratic sums and the ordinary power-sum "
                + "formula give 3 S(U 3,2,12r+2) = −52r³+69r²+82r+9 for every natural r. "
                + "Taking r=s+3 gives S(U 3,2,12s+38)<0 for every natural s. These arguments "
                + "are even and exceed any proposed threshold, contradicting the second "
                + "assertion. The first assertion and the signs for other k are not decided here.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string prose, string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula CFormula()
    {
        var a = F.Id("A");
        var i = F.Id("i");
        var n = F.Id("n");
        var p = F.Id("p");
        var x = F.Id("a");
        var parts = Qualified("Nat", "Partition", "parts");
        var pparts = new Formula.Apply(parts, [p]);
        var allowed = All("a", Nat(), Implies(Member(x, pparts), Member(x, a)));
        var predicate = Parenthesized(Seq(p, Colon, App("Nat", "Partition", n), Sp,
            Mapsto, Sp, And(allowed, Equal(App("Multiset", "card", pparts), i))));
        var univ = Parenthesized(Seq(Qualified("Finset", "univ"), Colon,
            Call("Finset", App("Nat", "Partition", n))));
        var rhs = App("Finset", "card", App("Finset", "filter", predicate, univ));
        return Disp(All("A", Call("Set", Nat()), All("i", Nat(), All("n", Nat(),
            Equal(Call("c", a, i, n), rhs)))));
    }

    private static Formula SFormula()
    {
        var a = F.Id("A");
        var k = F.Id("k");
        var n = F.Id("n");
        var i = F.Id("i");
        var summand = Multiply(Multiply(Pow(CastInt(new Formula.Negate(Num(1))), i), Pow(CastInt(i), k)),
            CastInt(Call("c", a, i, n)));
        var rhs = Seq(new Formula.Subscript(Sum, Member(i,
            App("Finset", "range", Add(n, Num(1))))), Parenthesized(summand));
        return Disp(All("A", Call("Set", Nat()), All("k", Nat(), All("n", Nat(),
            Equal(Call("S", a, k, n), rhs)))));
    }

    private static Formula UFormula()
    {
        var m = F.Id("m");
        var a = F.Id("a");
        var i = F.Id("i");
        var predicate = ExistsNat("i", And(Le(Num(1), i),
            And(Le(i, m), Equal(a, App("Nat", "factorial", i)))));
        return Disp(All("m", Nat(), Equal(Call("U", m),
            Seq(OpenBrace, a, Colon, Nat(), Bar, predicate, CloseBrace))));
    }

    private static Formula ClaimBody()
    {
        var m = F.Id("m");
        var k = F.Id("k");
        var n = F.Id("n");
        var threshold = F.Id("N");
        Formula Eventual(Formula exponent) => ExistsNat("N", All("n", Nat(),
            Implies(Le(threshold, n), Le(Num(0), Multiply(Pow(CastInt(new Formula.Negate(Num(1))), exponent),
                Call("S", Call("U", m), k, n))))));
        var first = All("k", Nat(), Implies(Le(k, Subtract(m, Num(2))),
            Eventual(App("Nat", "div", Add(n, Num(1)), Num(2)))));
        var second = All("k", Nat(), Implies(Le(Subtract(m, Num(1)), k), Eventual(n)));
        return All("m", Nat(), Implies(Le(Num(2), m), And(first, second)));
    }

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula CastInt(Formula value) =>
        Parenthesized(Seq(value, Colon, new Formula.Integers()));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsNat(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Nat(), body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(params string[] names) => Seq(names.Select((name, index) =>
        index == 0 ? Seq(Operatorname, Grp(F.Id(name)))
            : Seq(Dot, Operatorname, Grp(F.Id(name)))).ToArray());
    private static Formula App(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Qualified(owner, name), [.. arguments]);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
