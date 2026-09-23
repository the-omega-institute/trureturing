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
    private static Formula VU => Call("product", V, U);
    private static Formula P => F.Id("p");
    private static Formula Code(Formula p) => Call("elementaryHomeomorph", U, V, p);
    private static Formula All(Formula body, bool topology,
        params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("H", F.Id("Type")), B("group", Call("Group", F.Id("H"))),
             B("finite", Call("Fintype", F.Id("H"))), B("n", F.Id("Nat")),
             B("m", F.Id("Nat")),
             B("U", Call("GroupMat", F.Id("H"), F.Id("n"), F.Id("m"))),
             B("V", Call("GroupMat", F.Id("H"), F.Id("m"), F.Id("n"))),
             .. (topology ? new Formula.BoundVariable[] {
                 B("topology", Call("TopologicalSpace", F.Id("H"))),
                 B("continuousGroup", Call("IsTopologicalGroup", F.Id("H"))) } : []),
             .. extra], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each total group label has its own finite path fiber. Splitting those fibers transports both numbered histories and their group coordinates.",
        H("Counted group-labelled overlap codes"),
        Blocks(
            Describe.Lean(DescribeId.Create("group-counted-fiber-card"),
                DeclarationHandle.Create(Prefix + "fiber_card"), H("Count each group-label fiber"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    Call("card", Call("Fiber", U, V, F.Id("i"), F.Id("k"), F.Id("g"))),
                    Call("coefficient", Call("entry", UV, F.Id("i"), F.Id("k")), F.Id("g"))), false,
                    B("i", Call("Fin", F.Id("n"))), B("k", Call("Fin", F.Id("n"))),
                    B("g", F.Id("H"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a first-half label h and total label g, the second-half label must be h inverse times g. Counting all middle vertices and all h gives the group-ring convolution coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("group-counted-total-label"),
                DeclarationHandle.Create(Prefix + "split_label"), H("Preserve the ordered label"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    Call("product", Call("label", Call("first", Call("split", U, V, F.Id("a")))),
                        Call("label", Call("second", Call("split", U, V, F.Id("a"))))),
                    Call("label", F.Id("a"))), false, B("a", Call("Edge", UV))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The split labels are h and h inverse times g. Their product is g in the specified order; the group need not be commutative."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("group-counted-step-law"),
                DeclarationHandle.Create(Prefix + "elementary_step"), H("Intertwine the original time maps"),
                StatementSource.FromAuthor(Disp(All(Equal(Code(Call("step", UV, P)),
                    Call("step", VU, Code(P))), true,
                    B("p", Call("Prod", Call("Path", UV), F.Id("H")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The output group coordinate is the input coordinate multiplied by the first half-edge label. Splitting, overlap recoding, and joining preserve the original one-step skew dynamics."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("group-counted-action-law"),
                DeclarationHandle.Create(Prefix + "elementary_equivariant"), H("Preserve the specified left action"),
                StatementSource.FromAuthor(Disp(All(Equal(Code(Call("translate", F.Id("g"), P)),
                    Call("translate", F.Id("g"), Code(P))), true, B("g", F.Id("H")),
                    B("p", Call("Prod", Call("Path", UV), F.Id("H")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Left multiplication of the group coordinate commutes with the constructed right-side transfer. Both actions retain their order at every edge."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("group-counted-chain-code"),
                DeclarationHandle.Create(Prefix + "chain_has_group_conjugacy"), H("Interpret a complete finite matrix chain"),
                StatementSource.FromAuthor(Disp(ChainStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The empty chain gives the identity. Each nonempty chain composes one constructed counted group overlap homeomorphism with its tail. The time and group laws are preserved by composition, with arbitrary intermediate matrix dimensions."))),
                DescribeRole.Theorem))));

    private static Formula ChainStatement() => new Formula.BindMany(FormulaQuantifier.ForAll,
        [B("H", F.Id("Type")), B("group", Call("Group", F.Id("H"))),
         B("finite", Call("Fintype", F.Id("H"))),
         B("topology", Call("TopologicalSpace", F.Id("H"))),
         B("continuousGroup", Call("IsTopologicalGroup", F.Id("H"))),
         B("a", F.Id("Nat")), B("b", F.Id("Nat")), B("L", F.Id("Nat")),
         B("A", Call("GroupMat", F.Id("H"), F.Id("a"), F.Id("a"))),
         B("B", Call("GroupMat", F.Id("H"), F.Id("b"), F.Id("b"))),
         B("c", Call("ExchangeChain", Call("MonoidAlgebra", F.Id("Nat"), F.Id("H")),
             F.Id("A"), F.Id("B"), F.Id("L")))],
        Call("Nonempty", Call("GroupConjugacy", F.Id("A"), F.Id("B"))));
}
