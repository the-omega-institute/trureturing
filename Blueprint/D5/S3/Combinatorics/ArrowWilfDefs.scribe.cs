using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfDefs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arrow-pattern containment combines an ordered subsequence with prescribed arrows in the inverse Foata cycle map.",
        H("Arrow Patterns and Their Avoidance Classes"),
        Blocks(
            Node("left-to-right-maximum", "Left-to-right maxima", "IsLtrMax",
                IsLtrMaxFormula(),
                "An entry at index i is a left-to-right maximum when it exceeds every entry at an earlier index. Indices start at zero, and getD returns zero outside the list.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("inverse-foata-map", "The inverse Foata cycle map", "hat",
                null,
                "Find the index of x in p. If the next entry exists and is not a left-to-right maximum, map x to that entry. Otherwise map x to the last left-to-right maximum at or before its index. Thus each block cut before a left-to-right maximum becomes a cycle.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("arrow-containment", "Containment of an arrow pattern", "Contains",
                null,
                "Contains nu H k p holds when a function x selects increasing values x(1) through x(k) from p, the list obtained by mapping nu through x is a sublist of p, and hat p maps x(b) to x(c) for every pair (b,c) in H.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("arrow-avoiders", "The avoidance class", "avoiders",
                AvoidersFormula(),
                "The class consists of lists permuting the natural numbers from one through n that do not contain the specified arrow pattern.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("arrow-wilf-claim", "Equality of the two avoidance counts", "claim",
                ClaimFormula(),
                "For every positive n, the avoidance classes of (12; 3 to 3) and (23; 1 to 1) have equal set cardinality.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula? formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula IsLtrMaxFormula()
    {
        var p = F.Id("p");
        var i = F.Id("i");
        var j = F.Id("j");
        return Disp(All("p", Call("List", Nat()), All("i", Nat(),
            Iff(Call("IsLtrMax", p, i), All("j", Nat(),
                Imp(Lt(j, i), Lt(Call("getD", p, j, D(0)), Call("getD", p, i, D(0)))))))));
    }

    private static Formula AvoidersFormula()
    {
        var n = F.Id("n"); var nu = F.Id("nu"); var h = F.Id("H");
        var k = F.Id("k"); var p = F.Id("p");
        return Disp(All("n", Nat(), All("nu", Call("List", Nat()),
            All("H", Call("List", Call("Pair", Nat(), Nat())), All("k", Nat(),
                All("p", Call("List", Nat()),
                    Iff(new Formula.Relation(p, FormulaRelationOperator.MemberOf,
                            Call("avoiders", n, nu, h, k)),
                        And(Call("Perm", p, Seq(F.Id("List"), Dot, F.Id("range"), Apos,
                                Open, D(1), Comma, Sp, n, Close)),
                            new Formula.Not(Call("Contains", nu, h, k, p))))))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var left = Call("ncard", Call("avoiders", n,
            Seq(OpenBracket, D(1), Comma, Sp, D(2), CloseBracket),
            Seq(OpenBracket, Seq(Open, D(3), Comma, Sp, D(3), Close), CloseBracket), D(3)));
        var right = Call("ncard", Call("avoiders", n,
            Seq(OpenBracket, D(2), Comma, Sp, D(3), CloseBracket),
            Seq(OpenBracket, Seq(Open, D(1), Comma, Sp, D(1), Close), CloseBracket), D(3)));
        return Disp(Iff(F.Id("claim"), All("n", Nat(), Imp(Le(D(1), n), Eq(left, right)))));
    }

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
