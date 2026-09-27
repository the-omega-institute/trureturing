using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class GonzalezDLeonWachsThreeVertexMobiusDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gonzalezdeleonwachs2026weighted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal three-vertex weighted bond posets have explicit Mobius polynomials.",
        H("Three-Vertex Weighted Bond Mobius Computation"),
        Blocks(
            PolynomialNode("triangle-three-source-mobius-polynomial",
                "The triangle source polynomial", "triangleThree",
                "triangle_three_source_mobius_polynomial", 2, 5, 2,
                "The proof classifies every connected weighted partition of K3, identifies the "
                    + "actual order intervals, and evaluates the incidence-algebra recurrence."),
            PolynomialNode("path-three-source-mobius-polynomial",
                "The path source polynomial", "pathThree",
                "path_three_source_mobius_polynomial", 1, 3, 1,
                "The same source-faithful classification for P3 retains exactly its two graph "
                    + "edges and evaluates the actual maximal weighted-partition sum."))));

    private static DocumentBlock PolynomialNode(
        string id, string title, string graph, string declaration,
        byte constant, byte linear, byte quadratic, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(PolynomialFormula(
                graph, constant, linear, quadratic)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);

    private static Formula PolynomialFormula(
        string graph, byte constant, byte linear, byte quadratic)
    {
        var x = F.Id("X");
        var value = Add(Add(D(constant), Multiply(D(linear), x)),
            Multiply(D(quadratic), new Formula.Power(x, D(2))));
        return Disp(Equal(Call("sourceMobiusPolynomial", F.Id(graph)), value));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
