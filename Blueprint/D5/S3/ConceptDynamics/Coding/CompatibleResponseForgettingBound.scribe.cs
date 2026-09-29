using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CompatibleResponseForgettingBoundDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lagged response quotients assemble a bounded exchange chain.",
        H("Compatible response chain bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compatible-exchange-chain-bound"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CompatibleResponseForgettingBound.compatible_exchange_chain_bound"),
                H("Compatible certificates give a bounded exchange chain"),
                StatementSource.FromAuthor(F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
                    [Bound("n", Id("Nat")), Bound("k", Id("Nat")), Bound("m", Id("Nat")),
                     Bound("A", Call("CountMat", Id("n"), Id("n"))),
                     Bound("B", Call("CountMat", Id("k"), Id("k"))),
                     Bound("R", Call("CountMat", Id("n"), Id("k"))),
                     Bound("S", Call("CountMat", Id("k"), Id("n"))),
                     Bound("c", Call("CompatibleCertificate", Id("A"), Id("B"),
                         Id("R"), Id("S"), Id("m")))],
                    Call("Nonempty", Call("ExchangeChain", Id("Nat"), Id("A"), Id("B"),
                        Subtract(Multiply(Num(2), Id("m")), Num(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A positive-lag compatible certificate on essential finite count matrices A and B gives a strong-shift-equivalence chain with 2m-1 steps. Thus the shortest chain has length at most 2m-1; no optimality claim is made. The first response matrices meet in a one-step diamond, and the remaining quotient exchanges reach A and B at the lag. At lag one the diamond gives the single exchange."))),
                DescribeRole.Theorem))));
}
