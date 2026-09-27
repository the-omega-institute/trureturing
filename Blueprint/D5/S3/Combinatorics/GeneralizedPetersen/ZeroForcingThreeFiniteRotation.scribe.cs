using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeFiniteRotationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteRotation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var r = V("r"); var v = V("v"); var w = V("w");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Column rotations preserve all edges of P(13,3).",
            H("Rotation Preserves Adjacency"),
            Blocks(
            Node("rotation-adjacency", "Adjacency under column rotation", "rotate13_adj",
                Disp(Q(Iff(Adj(Call("gp", Num(13), Num(3)), Call("rotate13", r, v), Call("rotate13", r, w)), Adj(Call("gp", Num(13), Num(3)), v, w)), ("r", Fin(Num(13))), ("v", Name("V13")), ("w", Name("V13")))),
                "Subtracting the same column index preserves outer edges, inner step-three edges, and spokes.",
                DescribeRole.Theorem)),
            []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

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
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Adj(Formula graph, Formula left, Formula right) => Call("Adj", graph, left, right);
}
