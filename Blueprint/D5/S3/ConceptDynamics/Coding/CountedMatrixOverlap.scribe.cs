using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedMatrixOverlapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedMatrixOverlap.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula U => F.Id("U");
    private static Formula V => F.Id("V");
    private static Formula UV => Call("product", U, V);
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("n", F.Id("Nat")), B("m", F.Id("Nat")),
             B("U", Call("CountMat", F.Id("n"), F.Id("m"))),
             B("V", Call("CountMat", F.Id("m"), F.Id("n"))), .. extra], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonnegative matrix records numbered parallel edges. Its product provides all data needed to split and reassemble each edge.",
        H("Counted edges and overlap conjugacy"),
        Blocks(
            Describe.Lean(DescribeId.Create("counted-split-join"),
                DeclarationHandle.Create(Prefix + "split_join"), H("Recover both numbered half-edges"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    Call("split", U, V, Call("join", U, V, F.Id("a"), F.Id("b"), F.Id("h"))),
                    Call("pair", F.Id("a"), F.Id("b"))),
                    B("a", Call("Edge", U)), B("b", Call("Edge", V)),
                    B("h", Equal(Call("target", F.Id("a")), Call("source", F.Id("b"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fiber equivalence preserves the middle vertex and both edge numbers. Splitting after joining therefore recovers the full pair, including parallel-edge identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("counted-join-split"),
                DeclarationHandle.Create(Prefix + "join_split"), H("Recover the original matrix edge"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    Call("join", U, V, Call("first", Call("split", U, V, F.Id("a"))),
                        Call("second", Call("split", U, V, F.Id("a"))),
                        Call("splitBoundary", U, V, F.Id("a"))), F.Id("a")),
                    B("a", Call("Edge", UV))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse finite-fiber equivalence recovers the original numbered edge. The outside endpoints are unchanged in both constructions."))),
                DescribeRole.Theorem))));
}
