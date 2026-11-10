using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class PathMaximalIndependentCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual maximal independent subsets of finite paths", H("Actual maximal independent subsets of finite paths"), Blocks(
            Node("family", "The actual family", "family", "The family filters the powerset of 0,...,n-1 by maximal independence in Mathlib's native pathGraph n. A compiled bridge identifies this with bounded independent closed domination.", DescribeRole.Definition),
            Node("members", "Exact local membership", "mem_family", "Membership is equivalent to the original bounded labels, no adjacent selected pair, and closed domination of every path label.", DescribeRole.Theorem),
            Node("recurrence", "Invertible head and tail maps", "count_recurrence", "For every n, M(n+3)=M(n+1)+M(n). The first branch inserts label 0 and shifts the tail by two. The other inserts label 1 and shifts by three. Reading the tail reconstructs the original subset; the branches are disjoint by membership of label 0.", DescribeRole.Theorem),
            Node("singleton", "Singleton boundary witnesses", "valid_singleton", "For every n and t<n, if every label is t or adjacent to t then the singleton t satisfies Valid n. This helper is consumed by the exact short-path and endpoint boundary proofs.", DescribeRole.Theorem),
            Node("initial", "All short path boundaries", "count_initial", "The empty path has one maximal independent subset, the one-vertex path has one, and the two-vertex path has two. These auxiliary paths do not introduce graph cases below the source order three.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            Presentation(declaration), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static StatementSource Presentation(string name)
    {
        Formula n = V("n"), i = V("i"), t = V("t"), set = V("I");
        Formula M(Formula k) => Call("count", k);
        Formula? f = name switch
        {
            "mem_family" => All("n", Nat, All("I", Call("Finset", Nat), Iff(Mem(set, Call("family", n)), Call("Valid", n, set)))),
            "count_recurrence" => All("n", Nat, Eq(M(Add(n, D(3))), Add(M(Add(n, D(1))), M(n)))),
            "count_initial" => And(Eq(M(D(0)), D(1)), And(Eq(M(D(1)), D(1)), Eq(M(D(2)), D(2)))),
            "valid_singleton" => All("n", Nat, All("t", Nat, Imp(Lt(t, n), Imp(
                All("i", Nat, Imp(Lt(i, n), Or(Eq(i, t), Or(Eq(Add(i, D(1)), t), Eq(Add(t, D(1)), i))))),
                Call("Valid", n, new Formula.SetLiteral([t])))))),
            _ => null
        };
        return f is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(f));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Par(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
}
