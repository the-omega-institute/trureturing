using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class TraceConjugationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden trace is invariant under Galois conjugation.",
        H("Trace Invariance Under Conjugation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("trace-invariance-under-conjugation"),
                DeclarationHandle.Create("D5/S0/Carrier/TraceConjugation.trace_conj"),
                H("Trace invariance"),
                StatementSource.FromAuthor(Equal(
                    Call("trace", Call("conj", Id("x"))),
                    Call("trace", Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Conjugating a golden integer preserves its integral trace. In coordinates, conjugation sends `(a,b)` to `(a+b,-b)`, and both traces simplify to `2a+b`."))),
                DescribeRole.Theorem)),
        edges: [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Carrier/Conj"))]));
}
