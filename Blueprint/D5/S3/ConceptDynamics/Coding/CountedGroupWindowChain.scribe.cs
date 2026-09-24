using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedGroupWindowChainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedGroupWindowChain.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Id(string name) => F.Id(name);
    private static Formula A => Id("A");
    private static Formula Target => Id("B");
    private static Formula Length => Id("L");
    private static Formula Chain => Id("ch");
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("H", Id("Type")), B("group", Call("Group", Id("H"))),
             B("finite", Call("Fintype", Id("H"))),
             B("topology", Call("TopologicalSpace", Id("H"))),
             B("continuousGroup", Call("IsTopologicalGroup", Id("H"))),
             B("a", Id("Nat")), B("b", Id("Nat")), B("L", Id("Nat")),
             B("A", Call("GroupMat", Id("H"), Id("a"), Id("a"))),
             B("B", Call("GroupMat", Id("H"), Id("b"), Id("b"))),
             B("ch", Call("ExchangeChain", Call("MonoidAlgebra", Id("Nat"), Id("H")), A, Target, Length)),
             .. extra], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One finite matrix chain constructs one equivariant homeomorphism carrying both edge windows and both group-coordinate windows. The transfer is read from that same code.",
        H("Counted group chain recovery windows"),
        Blocks(
            Describe.Lean(DescribeId.Create("counted-group-chain-four-windows"),
                DeclarationHandle.Create(Prefix + "chain_has_window_group_conjugacy"),
                H("Construct one code with four recovery budgets"),
                StatementSource.FromAuthor(Disp(All(
                    Call("Nonempty", Call("WindowGroupConjugacy", A, Target, Length))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The elementary map is built from counted group-labelled edge fibers. Its forward edge uses the present and next input, its inverse uses the preceding and present output. The group transfers use the first split label and the preceding inverse split label. Composition adds all four budgets, and induction handles every intermediate matrix dimension."))),
                DescribeRole.Theorem))));
}
