using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class TraceConjugationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/TraceConjugation",
            "The golden trace is invariant under Galois conjugation."),
        H("Trace Invariance Under Conjugation"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("trace-invariance-under-conjugation"),
                H("Trace invariance"),
                LeanTheorem("D5/S0/Carrier/TraceConjugation.trace_conj"),
                Equal(
                    Call("trace", Call("conj", Id("x"))),
                    Call("trace", Id("x"))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Conjugating a golden integer preserves its integral trace. In coordinates, conjugation sends `(a,b)` to `(a+b,-b)`, and both traces simplify to `2a+b`."))))),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Carrier/Conj"))]));
}
