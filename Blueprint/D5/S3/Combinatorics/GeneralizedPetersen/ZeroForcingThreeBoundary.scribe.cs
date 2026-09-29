using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeBoundary.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var n = V("n"); var x = V("X"); var u = V("u"); var v = V("v");
        return DocumentDefinition.Create(ScribeNode.Create(
            "The external boundary consists of unselected vertices adjacent to the selected set.",
            H("External Boundary in P(n,3)"),
            Blocks(
            Node("external-boundary", "External vertex boundary", "externalBoundary",
                Disp(Q(Eq(Call("externalBoundary", n, x), SetOf("v", Vertices(n), And(Not(Mem(v, x)), Ex("u", Vertices(n), And(Mem(u, x), Adj(Call("gp", n, Num(3)), u, v)))))), ("n", Nat()), ("X", Fs(Vertices(n))))),
                "A vertex is in the external boundary when it lies outside X and has a neighbor in X.",
                DescribeRole.Definition)),
            []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(long value) => new Formula.Number(value);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Not(Formula value) => new Formula.Not(value);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Vertices(Formula n) => Seq(Name("Bool"), Times, Sp, Fin(n));
    private static Formula Fs(Formula value) => Call("Finset", value);
    private static Formula SetOf(string variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, Sp, V(variable), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace, Sp);
    private static Formula Adj(Formula graph, Formula left, Formula right) => Call("Adj", graph, left, right);
}
