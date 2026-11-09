using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FinchZeroRunsModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/FinchZeroRunsModThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/finch2026quadraticrecurrences");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At lag 61 the ternary recurrence never attains the proposed fifteen-gap zero run.",
        H("A Forbidden Zero Pattern in Finch's Ternary Recurrence"),
        Blocks(
            Node("claim", "Universal attainment of the upper bound", "claim",
                Iff(X("claim"), Parenthesized(ClaimBody())),
                "Remark 20, p. 8: “Empirical data suggest that Theorem 16 is the best possible. "
                    + "For instance, runs with exactly ⌊(k−1)/4⌋ gaps were observed for k = 245, 297, 333 "
                    + "(where k ≡ 1) and for k = 288, 320, 340 (where k ≡ 0). Proving that such maximal "
                    + "runs always occur would be a nice exercise in experimentation, but maybe "
                    + "a hard one in theory!” The proposition states the universal attainment "
                    + "reading: source sequences exist for every k≥2, and every such sequence "
                    + "attains the bound when k modulo four is zero or one and the gap count is "
                    + "positive. Nat.div is natural-number division, so (k−1) div 4 is the floor "
                    + "in the source. A run has g+1 zeros and g gaps; maximal here refers to "
                    + "attaining the bound, without an extension condition on either endpoint.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The universal attainment assertion is false", "result",
                new Formula.Not(Parenthesized(ClaimBody())),
                "At k=61, the recurrence has a source sequence whose packed ternary states "
                    + "start at one and advance by shifting sixty retained digits and appending "
                    + "the quadratic recurrence value. A list of 9685 states contains the initial "
                    + "state and is closed under this transition: its last transition returns to "
                    + "entry 739. Every future state therefore belongs to the list. None has "
                    + "zeros exactly at the multiples of four among its lowest 45 digits. A "
                    + "fifteen-gap run beginning at r≥62 would produce that forbidden pattern "
                    + "in the state after r−17 transitions. This contradicts universal attainment "
                    + "at k=61, where the proposed bound is fifteen. The statement refutes "
                    + "attainment and makes no assertion against the upper bound of Theorem 16.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("finch-zero-runs"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("finch-zero-runs-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula SourceBody()
    {
        var k = X("k");
        var x = X("x");
        var n = X("n");
        var initial = All("n", Naturals(), Imp(AtMost(D(1), n),
            Imp(Less(n, k), Equal(Apply(x, n), D(0)))));
        var recurrence = All("n", Naturals(), Imp(AtMost(Add(k, D(1)), n),
            Equal(Apply(x, n),
                Add(Apply(x, Sub(n, D(1))), Pow(Apply(x, Sub(n, k)), D(2))))));
        return And(Parenthesized(initial),
            And(Equal(Apply(x, k), D(1)), Parenthesized(recurrence)));
    }

    private static Formula RunBody(Formula g)
    {
        var k = X("k");
        var x = X("x");
        var r = X("r");
        var i = X("i");
        var n = X("n");
        var zeros = All("i", Naturals(), Imp(AtMost(i, g),
            Equal(Apply(x, Add(r, Mul(D(4), i))), D(0))));
        var others = All("n", Naturals(), Imp(Less(r, n),
            Imp(Less(n, Add(r, Mul(D(4), g))),
                Imp(NotEqual(Mod(Sub(n, r), D(4)), D(0)), NotEqual(Apply(x, n), D(0))))));
        return And(AtMost(Add(k, D(1)), r), And(AtMost(D(1), g),
            And(Parenthesized(zeros), Parenthesized(others))));
    }

    private static Formula ClaimBody()
    {
        var k = X("k");
        var x = X("x");
        var gaps = Apply(Qualified("Nat", "div"), Sub(k, D(1)), D(4));
        var existence = Some("x", SequenceType(), SourceBody());
        var residues = Or(Equal(Mod(k, D(4)), D(0)), Equal(Mod(k, D(4)), D(1)));
        var run = Some("r", Naturals(), RunBody(gaps));
        var attainment = All("x", SequenceType(), Imp(SourceBody(),
            Imp(Parenthesized(residues), Imp(Less(D(0), gaps), run))));
        return All("k", Naturals(), Imp(AtMost(D(2), k),
            Parenthesized(And(Parenthesized(existence), Parenthesized(attainment)))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula SequenceType() => new Formula.TypeArrow(Naturals(), Call("ZMod", D(3)));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Mod(Formula a, Formula b) => new Formula.Modulo(a, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
