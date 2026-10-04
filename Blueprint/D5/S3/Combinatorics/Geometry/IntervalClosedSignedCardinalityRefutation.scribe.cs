using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class IntervalClosedSignedCardinalityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/elder2024toggling");
    private static readonly LibraryNoteRef Followup =
        LibraryNoteRef.Create("D5/L/Combinatorics/lafreniere2025intervalclosed");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A literal 73-state orbit on a 3 by 12 rectangle has signed-cardinality sum minus one.",
        H("Signed cardinality need not be zero-mesic"),
        Blocks(
            Node("signed-weight", "The signed point statistic", "signedWeight", WeightFormula(),
                "Definition 3.17 (p. 21) reads: “Fix a finite poset P. For each x ∈ P, define the signed cardinality statistic SC(x): P → {−1, 1} as follows:” followed by SC(x) = 1 if rk(x) is even and −1 if rk(x) is odd. The zero-based point x in Point(m,n) = Fin m × Fin n has rank val(x.1) + val(x.2), equal to i + j − 2 for the paper's one-based coordinates (i,j). The integer conditional ite has its usual if-then-else meaning.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("signed-cardinality", "The signed statistic on a set", "signedCardinality", CardinalityFormula(),
                "Definition 3.17 (p. 21) reads: “For an interval-closed set I, SC(I) = ∑_{x∈I} SC(x).” The finite sum selects the members of I from all points of the rectangle. The same expression defines the statistic on every set, including the empty set.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("signed-cardinality-claim", "Conjecture 4.12", "claim", ClaimFormula(),
                "Conjecture 4.12 (p. 29) reads: “If m = 2 or m = 3, then the signed cardinality statistic is 0-mesic under rowmotion on interval-closed sets of [m]×[n] whenever m + n − 1 is even.” Definition 3.17 (p. 21) defines SC(x) = 1 if rk(x) is even and −1 if rk(x) is odd, and states: “For an interval-closed set I, SC(I) = ∑_{x∈I} SC(x).” Definition 2.6 (p. 4) reads: “Let x ∈ P and I ∈ IC(P) an interval-closed set of P. Define the toggle t_x: IC(P) → IC(P) as follows:” If x ∈ I, t_x(I) = I − {x} if I − {x} ∈ IC(P), and I otherwise. If x ∉ I, t_x(I) = I ∪ {x} if I ∪ {x} ∈ IC(P), and I otherwise. Its final sentence is: “That is, x is toggled in/out of I if doing so results in another interval-closed set.” Definition 2.9 (p. 5) reads: “Given an interval-closed set I ∈ IC(P), the rowmotion of I, Row(I), is given by applying all toggles in the reverse order of any linear extension.” Definition 2.24 (p. 10) reads: “We say that a statistic exhibits homomesy under some action when every orbit of that action has the same average when the statistic is calculated over the orbit.” Here N ranges over all enumeration lengths and e ranges over all equivalences Fin N ≃ Point(m,n); ReverseExtension(e) is precisely a complete enumeration in the reverse order of a linear extension. The reused trace applies the actual toggles, using symmetric difference and OrdConnected, and literalOrbit contains every distinct forward iterate once. Zero average on this nonempty finite orbit is equivalent to zero sum. The dimension n is positive, and subtraction in m + n − 1 is natural-number subtraction. Every linear extension and every interval-closed set are quantified. The follow-up retains the m = 3 case as a conjecture.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("signed-cardinality-result", "The conjecture is refuted", "result",
                Disp(new Formula.Not(F.Id("claim"))),
                "Take m = 3, n = 12 and the row-major linear extension. In one-based coordinates the initial set is {(1,7),(3,2),(3,3),(3,4),(3,5)}. Its literal rowmotion orbit has 73 distinct states and signed-cardinality sum −1, giving average −1/73. A bitmask uses bit j + 12i for the zero-based point (i,j). Lower- and upper-set masks certify order-convexity: a missing point cannot have both an included point below it and an included point above it. The encoding commutes with every actual toggle and every trace step. All 73 transitions, including the return to the seed, and the sum are checked; injectivity of the decoded cycle and induction identify it with the full distinct-state orbit. The even number of ranks does not force cancellation within an orbit.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Followup)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Point(Formula m, Formula n) => Call("Point", m, n);
    private static Formula SumOver(string name, Formula set, Formula value) =>
        Seq(Sum, Underscore, Grp(Seq(F.Id(name), Sp, InMacro, Sp, set)), Sp, value);

    private static Formula WeightFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), x = F.Id("x");
        Formula rank = Add(Call("val", Seq(x, Dot, D(1))), Call("val", Seq(x, Dot, D(2))));
        return Disp(All("m", Nat(), All("n", Nat(), All("x", Point(m, n),
            Equal(Call("signedWeight", x),
                Call("ite", Call("Even", rank), D(1), new Formula.Negate(D(1))))))));
    }

    private static Formula CardinalityFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), I = F.Id("I"), x = F.Id("x");
        Formula members = Seq(OpenBrace, x, Sp, InMacro, Sp, Point(m, n), Sp,
            Mid, Sp, Call("mem", x, I), CloseBrace);
        return Disp(All("m", Nat(), All("n", Nat(), All("I", Call("Set", Point(m, n)),
            Equal(Call("signedCardinality", I), SumOver("x", members, Call("signedWeight", x)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), N = F.Id("N"), e = F.Id("e"), I = F.Id("I");
        Formula sum = SumOver("S", Call("literalOrbit", e, I), Call("signedCardinality", F.Id("S")));
        Formula body = All("m", Nat(), All("n", Nat(), All("N", Nat(),
            Imp(Or(Equal(m, D(2)), Equal(m, D(3))),
                Imp(Leq(D(1), n), Imp(Call("Even", Sub(Add(m, n), D(1))),
                    All("e", Call("Equiv", Call("Fin", N), Point(m, n)),
                        Imp(Call("ReverseExtension", e),
                            All("I", Call("Set", Point(m, n)),
                                Imp(Call("OrdConnected", I), Equal(sum, D(0))))))))))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, body));
    }
}
