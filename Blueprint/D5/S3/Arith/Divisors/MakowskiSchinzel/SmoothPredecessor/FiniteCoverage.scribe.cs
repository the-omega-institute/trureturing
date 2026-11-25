using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor;

internal sealed class SmoothPredecessorFiniteCoverageDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/FiniteCoverage.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completeness of the bounded candidate table",
        H("Completeness of the bounded candidate table"), Blocks(
            Node("candidatePredecessors", "The counted predecessor set",
                Eq(V("candidatePredecessors"), Call("candidateFilter",
                    Call("factoredMultiples", Call("toFinset", V("allPrimes")),
                        V("bound"), D(2)))),
                "This finite set contains the positive even predecessors at most one " +
                "million whose quotient by two uses primes at most 97 and whose " +
                "candidate test succeeds.", true),
            Node("candidate_of_prime", "Exact candidate test on primes",
                All("q", Imp(Call("Prime", V("q")),
                    Iff(Eq(Call("candidate", Sub(V("q"), D(1))), V("true")),
                        Call("notPowerOfTwo", Sub(V("q"), D(1)))))),
                "For a prime q, the candidate test succeeds exactly when q-1 is not " +
                "a power of two. Fermat's little theorem supplies its congruence and " +
                "primality excludes the listed trial divisors. No size bound or " +
                "smoothness assumption is needed."),
            Node("prime_mem_table", "Exact bounded candidate coverage",
                Coverage(),
                "For every list T whose entries pass validEntry, whose values are distinct, " +
                "and whose length is at least smoothSum(candidateWeight,allPrimes,bound,2), " +
                "a natural number q has a labelled entry exactly when q-1 is at most one million, " +
                "the candidate test succeeds, " +
                "and q-1 is 98-smooth. Smoothness already forces q to be at least two. " +
                "The general recursive count turns inclusion into " +
                "equality. Validity gives inclusion, distinctness converts length to " +
                "cardinality, and the count inequality excludes omissions. Without " +
                "validity spurious entries are possible; without distinctness repeated " +
                "entries can fill the length bound while omitting a candidate; without " +
                "the count bound a proper sublist need not cover every candidate. Candidate success is " +
                "not a primality certificate."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool definition = false) => Describe.Lean(
        DescribeId.Create("smooth-predecessor-finitecoverage-" +
            name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula Coverage()
    {
        var q = V("q"); var pred = Sub(q, D(1));
        var result = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("e"), Nat(), And(Call("member", V("e"), V("T")),
                Eq(Call("entryValue", V("e")), q)));
        var coverage = All("q", Iff(result, And(Le(pred, V("bound")),
            And(Eq(Call("candidate", pred), V("true")),
                Call("member", pred, Call("smoothNumbers", D(9,8)))))));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("T"),
            Call("List", Nat()), Imp(Eq(Call("all", V("validEntry"), V("T")), V("true")),
                Imp(Call("Nodup", Call("map", V("entryValue"), V("T"))),
                    Imp(Le(Call("smoothSum", V("candidateWeight"), V("allPrimes"),
                        V("bound"), D(2)), Call("length", V("T"))), coverage))));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat(), body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
}
