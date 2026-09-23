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
    private static Formula VU => Call("product", V, U);
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula I => F.Id("i");
    private static Formula Read(Formula x, Formula i) => Call("coordinate", x, i);
    private static Formula Code(Formula x) => Call("elementaryHomeomorph", U, V, x);
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("n", F.Id("Nat")), B("m", F.Id("Nat")),
             B("U", Call("CountMat", F.Id("n"), F.Id("m"))),
             B("V", Call("CountMat", F.Id("m"), F.Id("n"))), .. extra], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonnegative matrix records numbered parallel edges. Its product provides all data needed to split and reassemble each edge.",
        H("Counted edges and overlap conjugacy"),
        Blocks(
            Describe.Lean(DescribeId.Create("counted-product-fiber-card"),
                DeclarationHandle.Create(Prefix + "fiber_card"), H("Count the actual factor paths"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    Call("card", Call("Fiber", U, V, I, F.Id("k"))),
                    Call("entry", UV, I, F.Id("k"))),
                    B("i", Call("Fin", F.Id("n"))), B("k", Call("Fin", F.Id("n")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each middle vertex, independently choose a numbered U edge and a numbered V edge. Summing their product cardinalities gives the corresponding matrix-product entry."))),
                DescribeRole.Theorem),
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
                        Call("split_boundary", U, V, F.Id("a"))), F.Id("a")),
                    B("a", Call("Edge", UV))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse finite-fiber equivalence recovers the original numbered edge. The outside endpoints are unchanged in both constructions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("counted-time-intertwining"),
                DeclarationHandle.Create(Prefix + "elementary_shift"), H("Conjugacy of the actual edge shifts"),
                StatementSource.FromAuthor(Disp(All(Equal(Code(Call("shift", UV, X)),
                    Call("shift", VU, Code(X))), B("x", Call("Path", UV))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After splitting every edge, regroup the second half-edge with the first half-edge of its successor and reassemble using the reverse product. Both directions are continuous, recover the input, and preserve one time step."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("counted-two-coordinate-window"),
                DeclarationHandle.Create(Prefix + "elementary_window"), H("The forward observation window"),
                StatementSource.FromAuthor(Disp(All(Window(),
                    B("x", Call("Path", UV)), B("y", Call("Path", UV)), B("i", F.Id("Int"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The new edge at i is assembled from the second half-edge at i and the first half-edge at i+1. Equality of these two input coordinates therefore determines the entire output edge."))),
                DescribeRole.Theorem))));

    private static Formula Window()
    {
        Formula next = new Formula.Binary(I, FormulaBinaryOperator.Add, F.D(1));
        return new Formula.Logic(Equal(Read(X, I), Read(Y, I)), FormulaLogicOperator.Implies,
            new Formula.Logic(Equal(Read(X, next), Read(Y, next)), FormulaLogicOperator.Implies,
                Equal(Read(Code(X), I), Read(Code(Y), I))));
    }
}
