using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis.TraceMap;

internal sealed class CarrierCoherenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var K = Id("K");
        var k = Id("k");

        var scaled = Equal(
            Call("t", Id("x"), Id("y"), Add(k, Num(1))),
            Call("t", Multiply(Id("x"), Id("phi")), Multiply(Id("y"), Id("psi")), k));

        var coherence = Equal(
            Call("tracePartial", Multiply(Id("x"), Id("phi")), Multiply(Id("y"), Id("psi")), K),
            Call("axisPartialSum", Id("x"), Id("y"), Add(K, Num(1))));

        const string declarationPrefix = "D5/S3/Axis/TraceMap/CarrierCoherence.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The two named partial sums agree after a substitution and a depth shift.",
            H("Carrier Coherence"),
            Blocks(
                Paragraph(Text(
                    "Two formalizations of the same partial sum exist in this repository, "
                        + "written eight days apart. An earlier module related one of them to a "
                        + "sum at a shifted weight index, which is not either of the two objects "
                        + "the digestion ledger names. Its comment claimed more than its type "
                        + "did, and that module is frozen, so the correction is carried here.")),
                Paragraph(Text(
                    "The missing step turns out not to be combinatorial. Shifting the weight "
                        + "index by one is exactly substituting each reading by its own "
                        + "embedding, because the weight is an exponential in the corresponding "
                        + "power. With that substitution the earlier relation transports onto "
                        + "the two carriers themselves.")),
                Describe.Lean(
                    DescribeId.Create("shifting-the-weight-is-scaling-the-readings"),
                    DeclarationHandle.Create(declarationPrefix + "axisWeight_succ_eq_scaled"),
                    H("Shifting the weight is scaling the readings"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(scaled)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "One step up in the weight index multiplies each reading by its own "
                            + "embedding, which is what turns an index shift into a parameter "
                            + "substitution."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("the-two-formalizations-of-the-weight-agree"),
                    DeclarationHandle.Create(declarationPrefix + "axisWeight_agree"),
                    H("The two formalizations of the weight agree"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(
                        Equal(Call("tA", Id("x"), Id("y"), k), Call("tB", Id("x"), Id("y"), k)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The same function written twice, eight days apart, under two names. "
                            + "Stating the agreement is what lets a theorem about one be used "
                            + "in a proof about the other."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("the-two-named-partial-sums-agree"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tracePartial_eq_axisPartialSum"),
                    H("The two named partial sums agree"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(coherence)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Substituting the two embeddings into the readings and shifting the "
                            + "depth by one carries one partial sum onto the other. Both shifts "
                            + "are explicit in the statement, and cutting either one makes the "
                            + "module fail to build."))),
                    DescribeRole.Theorem))));
    }
}
