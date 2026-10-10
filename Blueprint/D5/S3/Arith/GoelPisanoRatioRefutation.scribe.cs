using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoelPisanoRatioRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoelPisanoRatioRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/goel2026sophiegermain");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime-domain Fibonacci period-to-rank ratios omit every multiple of five, answering Goel's OQ4 in the negative.",
        H("Goel's Pisano-Rank Ratio Question Is False"),
        Blocks(
            Paragraph(Text("The source states on p. 1: “For a prime p, the rank of apparition z(p) is the smallest positive integer k with p | Fₖ; it is well-defined for every prime p [3, 7]. The Pisano period π(n) is the period of (Fₘ mod n).” "
                + "Here Fₘ is Nat.fib m. The source's z is the existing zeroRank from D5.S3.Arith.FibonacciAtomic.TimeSampling, with exactly the least-positive-zero definition. Natural-number infima use zero for an empty set; the relevant sets are nonempty at prime moduli.")),
            new DocumentBlock.DisplayFormula(Disp(All("p", Nat, Equal(Call("zeroRank", F.Id("p")),
                Call("sInf", SetOf("k", And(Less(D(0), F.Id("k")),
                    Divides(F.Id("p"), Fib(F.Id("k")))))))))),
            Node("pisanoPeriod", "The least positive Pisano period", PiFormula(),
                "“The Pisano period π(n) is the period of (Fₘ mod n).” (p. 1). "
                + "The least positive period is taken over all natural time indices m. The operation mod is Nat.mod, and all arguments have type Nat.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("SophieGermain", "The standing prime domain", SophieFormula(),
                "A Sophie Germain prime q is a prime for which 2q+1 is also prime. "
                + "The source defines z at primes and treats q as an odd prime; with q>5 this gives the displayed domain.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The source question", ClaimFormula(),
                "“OQ4. Values of π(q)/z(2q + 1). Is {π(q)/z(2q + 1) : q > 5 with z(2q + 1) | π(q)} = {odd integers}?” (Section 10, p. 10). "
                + "The prime hypotheses are the standing domain of Sections 5–7: z(2q+1) is defined at a prime, and q is an odd prime throughout. "
                + "Every eligible ratio is positive, so the right side is encoded by Odd on Nat, the positive odd integers. The reading over all integers also fails, since it contains negative values. "
                + "Nat.div is natural-number division; the divisibility hypothesis makes this quotient exact. The two prime conjuncts are expanded here, matching the source domain.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Five is never a value", Disp(new Formula.Not(F.Id("claim"))),
                "The value five is odd, but it cannot occur. Set p=2q+1. The prime Fibonacci rank bound and the period bounds first force the quadratic character at p to be negative: a positive character would make zeroRank(p) divide both 2q and q²−1, hence two, whereas p>11 gives zeroRank(p)≥5. "
                + "A positive character at q would then make zeroRank(p) divide both q−1 and 2(q+1), hence four, the same contradiction. The negative character at q gives q mod 5 equal to two or three and π(q) dividing 2(q+1). Thus five divides neither π(q) nor its exact quotient by zeroRank(p). "
                + "The argument excludes every multiple of five. It does not assert that all remaining positive odd values occur.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("goel-2026-pisano-rank-ratio-oq4"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("goel-pisano-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Fib(Formula n) => new Formula.Apply(Qualified("Nat", "fib"), [n]);
    private static Formula Prime(Formula n) => new Formula.Apply(Qualified("Nat", "Prime"), [n]);
    private static Formula Period(Formula n) => Call("pisanoPeriod", n);
    private static Formula Div(Formula a, Formula b) =>
        new Formula.Apply(Qualified("Nat", "div"), [a, b]);
    private static Formula Mod(Formula a, Formula b) => new Formula.Modulo(a, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula TwicePlusOne(Formula q) => Add(new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, q), D(1));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsNat(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Nat, body);
    private static Formula SetOf(string name, Formula predicate) =>
        Seq(OpenBrace, F.Id(name), Colon, Sp, Nat, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula PiFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var m = F.Id("m");
        return Disp(All("n", Nat, Equal(Period(n), Call("sInf", SetOf("k",
            And(Less(D(0), k), All("m", Nat, Equal(Mod(Fib(Add(m, k)), n), Mod(Fib(m), n)))))))));
    }

    private static Formula SophieFormula()
    {
        var q = F.Id("q");
        return Disp(All("q", Nat, new Formula.Logic(Call("SophieGermain", q),
            FormulaLogicOperator.Iff, Parenthesized(And(Prime(q), Prime(TwicePlusOne(q)))))));
    }

    private static Formula ClaimFormula()
    {
        var q = F.Id("q");
        var r = F.Id("R");
        var rank = Call("zeroRank", TwicePlusOne(q));
        var domain = And(Prime(q), And(Prime(TwicePlusOne(q)), And(Less(D(5), q),
            And(Divides(rank, Period(q)), Equal(r, Div(Period(q), rank))))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Parenthesized(Equal(SetOf("R", ExistsNat("q", domain)), SetOf("R", Call("Odd", r))))));
    }
}
