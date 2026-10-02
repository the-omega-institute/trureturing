using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Persistence;

internal sealed class FiniteIntervalSplitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalSplit.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/bauer2015persistence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero finite diagram over any field admits an actual natural interval "
            + "retraction, vertexwise line/kernel isomorphisms and strict dimension descent.",
        H("Splitting an Interval from an Actual Finite Diagram"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-diagram"),
                DeclarationHandle.Create(Prefix + "Diagram"),
                H("Actual forward maps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The vertices are Fin(n), with arbitrary K-vector spaces V(i). "
                        + "For each i <= k the diagram contains the actual linear map F(i,k), "
                        + "identity maps at equal indices and the composition equations. "
                        + "No barcode, basis, common ambient space or dimension bound is supplied."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exists-interval-split"),
                DeclarationHandle.Create(Prefix + "exists_interval_split"),
                H("A natural interval and its complementary kernel diagram"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "K is an arbitrary field. Every V(i) is finite-dimensional, and at "
                            + "least one vertex contains a nonzero vector. There are b <= j, "
                            + "vectors w(i) and functionals p(i). Before b every vertex is zero. "
                            + "Outside b <= i <= j, both w(i) and p(i) vanish; inside, p(i)(w(i))=1.")),
                    Paragraph(Text(
                        "NaturalVectors means F(i,k)(w(i))=w(k) when b <= i and k <= j, "
                            + "and zero otherwise. NaturalFunctionals means p(k) composed with "
                            + "F(i,k) is p(i) in the same case and zero otherwise. These equations "
                            + "cover arrows entering and leaving the support, not only its interior.")),
                    Paragraph(Text(
                        "VertexSplittings gives actual linear equivalences from V(i) to "
                            + "span{w(i)} times ker(p(i)), with coordinates p(i)(x) w(i) and "
                            + "x-p(i)(x) w(i). The inverse adds the coordinates. "
                            + "NaturalProjectors says F(i,k) commutes with these projections. "
                            + "NaturalKernels says every arrow maps ker(p(i)) into ker(p(k)). "
                            + "StrictDescent compares the sums of the actual kernel and vertex finranks.")),
                    Paragraph(Text(
                        "Choose the earliest nonzero vertex and a nonzero vector there, then "
                            + "the last vertex where its forward image survives. Mathlib supplies "
                            + "a scalar linear left inverse at that last vector. Pulling it back "
                            + "along the actual composites gives the functionals. The earliest "
                            + "and last choices prove the boundary squares. Ordinary complement "
                            + "isomorphisms give the displayed splitting; one dimension is removed "
                            + "at every supported vertex, so the total kernel dimension decreases.")),
                    Paragraph(Text(
                        "The last vertex may lie in the support. No artificial terminal zero "
                            + "is appended. Iterating the construction is the finite-diagram "
                            + "classification step; real-parameter extension, multiset uniqueness "
                            + "and quantitative stability require further arguments."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula ResultFormula()
    {
        Formula field = F.Id("K"), spaces = F.Id("V"), diagram = F.Id("F");
        Formula birth = F.Id("b"), last = F.Id("j"), vectors = F.Id("w"), maps = F.Id("p");
        Formula conclusion = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("b", Call("Fin", F.Id("n"))), Bound("j", Call("Fin", F.Id("n"))),
             Bound("w", Call("VertexVectors", spaces)), Bound("p", Call("VertexFunctionals", field, spaces))],
            All(new Formula.Relation(birth, FormulaRelationOperator.LessThanOrEqual, last),
                Call("EarlierZero", spaces, birth), Call("SupportedNormalized", birth, last, vectors, maps),
                Call("NaturalVectors", diagram, birth, last, vectors),
                Call("NaturalFunctionals", diagram, birth, last, maps),
                Call("VertexSplittings", field, spaces, vectors, maps),
                Call("NaturalProjectors", diagram, vectors, maps), Call("NaturalKernels", diagram, maps),
                Call("StrictDescent", field, spaces, maps)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("K", F.Id("Type")), Bound("n", Call("Nat")),
             Bound("V", Call("VertexSpaces", F.Id("n"))), Bound("F", Call("Diagram", field, spaces))],
            new Formula.Logic(All(Call("Field", field), Call("FiniteDimensionalVertices", field, spaces),
                Call("NonzeroVertex", spaces)), FormulaLogicOperator.Implies, conclusion)));
    }
}
