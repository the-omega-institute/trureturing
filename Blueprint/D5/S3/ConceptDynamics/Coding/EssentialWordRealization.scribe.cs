using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class EssentialWordRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/EssentialWordRealization.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Instances(Formula body, params Formula[] instances)
    {
        var items = new List<Formula>();
        foreach (var instance in instances)
            items.AddRange([OpenBracket, instance, CloseBracket, Comma, Sp]);
        items.Add(body);
        return Seq([.. items]);
    }
    private static Formula Parameters(Formula body) => All(Instances(All(
        new Formula.Logic(Call("Essential", F.Id("G")), FormulaLogicOperator.Implies,
            new Formula.Logic(new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan,
                F.Id("n")), FormulaLogicOperator.Implies, body)),
        B("G", Call("DirectedMultigraph", F.Id("V"), F.Id("E"))),
        B("n", F.Id("Nat")), B("word", Call("LegalWord", F.Id("G"), F.Id("n")))),
        Call("Fintype", F.Id("V")), Call("Fintype", F.Id("E")),
        Call("DecidableEq", F.Id("V"))), B("V", F.Id("Type")), B("E", F.Id("Type")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An essential directed multigraph realizes every prescribed positive legal word as one actual bi-infinite history, retaining every edge label.",
        H("Prescribed-word realization"),
        Blocks(Describe.Lean(DescribeId.Create("prescribed-word-history"),
            DeclarationHandle.Create(Prefix + "exists_history_containing"),
            H("One actual history containing the entire prescribed word"),
            StatementSource.FromAuthor(Disp(Parameters(Exists("x", Call("History", F.Id("G")),
                All(Equal(Call("historyEdge", F.Id("x"), F.Id("j")),
                    Call("wordEdge", F.Id("word"), F.Id("j"))), B("j", Call("Fin", F.Id("n")))))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Essential means that each vertex has an actual outgoing edge and an actual incoming edge. Edges are elements of the supplied edge type, so loops and distinct parallel edges remain distinct. LegalWord stores all those edges and each target/source adjacency equation. History is the subtype of Int-indexed actual edges satisfying every adjacency equation.")),
                Paragraph(Text("In the display, historyEdge(x,j) is x evaluated at the integer cast of j; wordEdge(word,j) is the j-th prescribed edge. The history uses iterated incoming choices at negative times, the entire prescribed word at times 0 through n minus 1, and iterated outgoing choices afterward. The proof verifies both outer seams and every interior seam. No strong connectivity, word-extension assumption or redefinition by globally realizable words is present.")),
                Paragraph(Text("The positive-length requirement covers both table lengths, both seam lengths and the common recovery length in the finite-window criterion, for all four natural radii including zero. The empty LegalWord type does not specify a vertex for a zero-edge path."))),
            DescribeRole.Theorem))));
}
