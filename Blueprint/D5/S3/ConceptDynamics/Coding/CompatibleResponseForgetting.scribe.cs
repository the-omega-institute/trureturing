using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CompatibleResponseForgettingDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compatible numbered path certificate constructs an essential finite square graph with both boundaries forgetting after its lag.",
        H("Compatible response forgetting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("incoming-response-step"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.incoming_response_step"),
                H("Incoming lifts respect response depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For two states with the same numbered path responses at depth d plus one, lifting the same incoming base edge places their predecessor states in one depth-d response class. Appending that edge to each depth-d path identifies the resulting lifted paths with the original depth-(d+1) observations."))),
                DescribeRole.Theorem),
            Paragraph(Text("Numbered compatible squares give incoming and outgoing lifts on the R-edge states. The two finite sweeps identify their lagged responses with the certificate path bijections; counting their actual edge fibers yields the first row and column response matrices.")),
            Describe.Lean(
                DescribeId.Create("compatible-exchange-chain-bound"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.compatible_exchange_chain_bound"),
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
                    Paragraph(Text("A positive-lag compatible certificate on essential finite count matrices A and B gives a strong-shift-equivalence chain with 2m-1 steps. Thus the shortest chain has length at most 2m-1; no optimality claim is made. Numbered compatible squares determine the two response quotients of the square graph. Their first matrices meet in a one-step diamond, and the remaining quotient exchanges reach A and B at the lag. At lag one the diamond gives the single exchange."))),
                DescribeRole.Theorem))));
}
