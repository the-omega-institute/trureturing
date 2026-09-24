using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedGroupOverlapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula U => F.Id("U");
    private static Formula V => F.Id("V");
    private static Formula UV => Call("product", U, V);
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("H", F.Id("Type")), B("group", Call("Group", F.Id("H"))),
             B("finite", Call("Fintype", F.Id("H"))), B("n", F.Id("Nat")),
             B("m", F.Id("Nat")),
             B("U", Call("GroupMat", F.Id("H"), F.Id("n"), F.Id("m"))),
             B("V", Call("GroupMat", F.Id("H"), F.Id("m"), F.Id("n"))),
             .. extra], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each total group label has its own finite path fiber. Splitting those fibers transports both numbered histories and their group coordinates.",
        H("Counted group-labelled overlap codes"),
        Blocks(
            Describe.Lean(DescribeId.Create("group-counted-split-join"),
                DeclarationHandle.Create(Prefix + "split_join"), H("Recover both labelled half-edges"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    Call("split", U, V, Call("join", U, V, F.Id("a"), F.Id("b"), F.Id("h"))),
                    Call("pair", F.Id("a"), F.Id("b"))),
                    B("a", Call("Edge", U)), B("b", Call("Edge", V)),
                    B("h", Equal(Call("target", F.Id("a")), Call("source", F.Id("b"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The total-label fiber equivalence retains the middle vertex, both labels and both parallel-edge numbers, so splitting after joining recovers the full pair."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("group-counted-join-split"),
                DeclarationHandle.Create(Prefix + "join_split"), H("Recover the original labelled edge"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    Call("join", U, V, Call("first", Call("split", U, V, F.Id("a"))),
                        Call("second", Call("split", U, V, F.Id("a"))),
                        Call("split_boundary", U, V, F.Id("a"))), F.Id("a")),
                    B("a", Call("Edge", UV))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse total-label fiber equivalence recovers the original outside endpoints, total label and parallel-edge number."))),
                DescribeRole.Theorem))));
}
