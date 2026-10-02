using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Persistence;

internal sealed class FiniteIntervalDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/Persistence/FiniteIntervalDecomposition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/bauer2015persistence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual finite diagram over a field has a finite homogeneous interval basis.",
        H("Homogeneous Interval Bases for Finite Diagrams"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interval-basis"),
                DeclarationHandle.Create(Prefix + "IntervalBasis"),
                H("One occurrence set across all vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "An interval basis contains a finite occurrence type, birth and last "
                        + "indices b(a) <= j(a), and a vector w(a,i) at every vertex. "
                        + "The vectors vanish outside their supports. At vertex i the vectors "
                        + "indexed by occurrences with b(a) <= i <= j(a) form an actual basis. "
                        + "For i <= k, the actual map sends w(a,i) to w(a,k) when b(a) <= i "
                        + "and k <= j(a), and to zero otherwise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exists-interval-basis"),
                DeclarationHandle.Create(Prefix + "exists_interval_basis"),
                H("Constructing the simultaneous bases from arbitrary arrows"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "K is any field and the vertices are Fin(n). Each V(i) is finite-dimensional "
                            + "without a uniform supplied dimension bound. The diagram contains "
                            + "arbitrary actual forward maps with identity and composition laws. "
                            + "The conclusion constructs an interval basis, rather than assuming "
                            + "one as a classifier input.")),
                    Paragraph(Text(
                        "Strong induction uses the sum of the vertex finranks. If every vertex "
                            + "is zero, the occurrence type is empty. Otherwise a natural interval "
                            + "retraction gives an actual kernel diagram of strictly smaller total "
                            + "dimension. Its recursively constructed bases are combined with the "
                            + "supported singleton line bases using the vertexwise product splitting. "
                            + "The occurrence type is enlarged by one globally, not independently "
                            + "at each vertex. Naturality holds for every resulting occurrence.")),
                    Paragraph(Text(
                        "The supported basis coordinate isomorphisms give the finite-diagram "
                            + "interval classification. Empty chains and all-zero diagrams are "
                            + "included. The last vertex is an ordinary vertex and may be supported; "
                            + "no terminal zero is imposed. Real extension, multiset uniqueness "
                            + "on common refinements and exact stability are distinct further results."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ResultFormula()
    {
        Formula field = F.Id("K"), spaces = F.Id("V"), diagram = F.Id("F");
        Formula hypotheses = new Formula.Logic(Call("Field", field), FormulaLogicOperator.And,
            Call("FiniteDimensionalVertices", field, spaces));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("K", F.Id("Type")), Bound("n", Call("Nat")),
             Bound("V", Call("VertexSpaces", F.Id("n"))), Bound("F", Call("Diagram", field, spaces))],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies,
                Call("Nonempty", Call("IntervalBasis", diagram)))));
    }
}
