using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedExchangeChainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedExchangeChain.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula A => F.Id("A");
    private static Formula C => F.Id("B");
    private static Formula L => F.Id("L");
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("n", F.Id("Nat")), B("m", F.Id("Nat")),
             B("A", Call("CountMat", F.Id("n"), F.Id("n"))),
             B("B", Call("CountMat", F.Id("m"), F.Id("m"))), B("L", F.Id("Nat")),
             B("c", Call("ExchangeChain", F.Id("Nat"), A, C, L)), .. extra], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite sequence of rectangular exchanges determines an actual conjugacy whose forward and inverse observation windows grow additively.",
        H("Counted matrix chains and bounded-window codes"),
        Blocks(
            Describe.Lean(DescribeId.Create("counted-chain-conjugacy-exists"),
                DeclarationHandle.Create(Prefix + "chain_has_window_conjugacy"), H("Construct the whole code"),
                StatementSource.FromAuthor(Disp(All(
                    Call("Nonempty", Call("WindowConjugacy", A, C, L))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The empty chain gives the identity. A nonempty chain composes the first counted-edge overlap homeomorphism with the recursively constructed tail. Every intermediate matrix size is retained."))),
                DescribeRole.Theorem))));
}
