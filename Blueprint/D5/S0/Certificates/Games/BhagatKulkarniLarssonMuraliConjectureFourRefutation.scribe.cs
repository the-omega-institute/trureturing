using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Games;

internal sealed class BhagatKulkarniLarssonMuraliConjectureFourRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Games/BhagatKulkarniLarssonMuraliConjectureFourRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/bhagatkulkarnilarssonmurali2026tiebreaking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For {4,22,35,38} at heap 161, Bob gains from 77 to 78 under AvA instead of FvF.",
        H("A Counterexample to Conjecture 4 of Bhagat, Kulkarni, Larsson and Murali"),
        Blocks(
            Paragraph(Text(
                "Conjecture 4 of Bhagat, Kulkarni, Larsson and Murali states: "
                    + "\"Consider any subtraction set S, and suppose both players act friendly "
                    + "in case of indifference. Then each player's PSPE utility is never worse "
                    + "than if both players have antagonistic tie-breaking rules.\" The paper "
                    + "orders outcome pairs coordinatewise. Its Definition 2 uses the dual "
                    + "convention at every move; at the initial heap, the first coordinate "
                    + "belongs to Alice and the second to Bob.")),
            Node("bklm-c4-claim", "The coordinatewise conjecture", ClaimFormula(),
                "A duplicate-free, nonempty list of positive natural numbers represents "
                    + "a finite nonempty subtraction set. Every natural heap is covered. "
                    + "For each such list and heap, both coordinates of the AvA outcome "
                    + "are required to be at most the corresponding FvF coordinates. "
                    + "The outcome recurrence realizes Definition 2; only positive "
                    + "steps no larger than the heap are legal.",
                "claim", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("bklm-c4-subtractions", "The subtraction set", WitnessFormula(),
                "The four distinct positive steps are 4, 22, 35 and 38. The list "
                    + "represents the set without repeated elements.",
                "witnessSubtractions", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("bklm-c4-refutation", "The conjecture fails at heap 161", ResultFormula(),
                "At heap 161 the outcomes are FvF = (84,77), AvF = (84,77), "
                    + "FvA = (83,78) and AvA = (83,78). The two values used in the "
                    + "proof are checked by kernel reduction of the outcome "
                    + "function. Bob's AvA total 78 exceeds his FvF total 77, so the "
                    + "second coordinate of the conjecture fails. The same paper's "
                    + "Problem 6 is settled by SelfInterestConventionDeviationGain; "
                    + "this result settles only Conjecture 4. No global minimality "
                    + "or classification of counterexamples is asserted.",
                "result", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose, string declaration,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula ClaimFormula()
    {
        var subtractions = F.Id("subtractions");
        var s = F.Id("s");
        var heap = F.Id("heap");
        var nonempty = Relation(subtractions, FormulaRelationOperator.NotEqual,
            Seq(OpenBracket, CloseBracket));
        var positive = Universal("s", Naturals(), Implies(
            Relation(s, FormulaRelationOperator.MemberOf, subtractions),
            Relation(D(0), FormulaRelationOperator.LessThan, s)));
        var nodup = Seq(subtractions, Dot, F.Id("Nodup"));
        var avA = Call("outcome", subtractions, F.Id("AvA"), heap);
        var fvF = Call("outcome", subtractions, F.Id("FvF"), heap);
        var aliceBound = Relation(Project(avA, 1),
            FormulaRelationOperator.LessThanOrEqual, Project(fvF, 1));
        var bobBound = Relation(Project(avA, 2),
            FormulaRelationOperator.LessThanOrEqual, Project(fvF, 2));
        var body = Universal("subtractions", Call("List", Naturals()),
            Implies(nonempty, Implies(positive, Implies(nodup,
                Universal("heap", Naturals(), And(aliceBound, bobBound))))));
        return Disp(Iff(Parenthesized(F.Id("claim")), Parenthesized(body)));
    }

    private static Formula WitnessFormula() => Disp(Seq(
        F.Id("witnessSubtractions"), Colon, Sp, Call("List", Naturals()),
        Sp, Eq, Sp, OpenBracket, D(4), Comma, D(2, 2), Comma,
        D(3, 5), Comma, D(3, 8), CloseBracket));

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Project(Formula pair, byte component) =>
        Seq(Parenthesized(pair), Dot, D(component));
    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Universal(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            type, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Relation(Formula left, FormulaRelationOperator relation,
        Formula right) => new Formula.Relation(left, relation, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And,
            Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
}
