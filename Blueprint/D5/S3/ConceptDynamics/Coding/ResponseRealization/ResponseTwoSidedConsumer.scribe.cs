using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.ResponseRealization;

internal sealed class ResponseTwoSidedConsumerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseTwoSidedConsumer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual response output is reduced to two concrete finite split towers and a terminal finite graph relabeling.",
        H("The concrete two-sided response terminal"),
        Blocks(
            Paragraph(Text("G has finite vertex and edge types, decidable equality on both, a discrete edge topology and Essential G. pair and S carry the four arbitrary natural radii and the exact original two-table conjugacy. original bundles precisely G and hG as a Presentation. response bundles the existing countedGraph and obtains its essentiality from numbered_response_reduction; the original matrix and all counted edge numbers are unchanged.")),
            Paragraph(Text("The horizontal map is the actual numberedOutput, one-block by its literal edge-output formula. The first step uses the response output partition on the source and id on the target. splitOutput, splitRecover and response_recovery supply the changed homeomorphism and its total inverse table with radii a+c,b+d. reduce runs on the remaining sum (a+c)+(b+d), not on an assumed paired chain.")),
            Paragraph(Text("terminal prepends that actual outgoing stage to both towers. Its source and target depths are therefore k=(a+c)+(b+d+1). Its finite relabeling and terminal graph types come from the recursion. Its square is proved on every response history by the first changed square followed by the recursive square. No constructor accepts an arbitrary history-map leaf.")),
            Paragraph(Text("Combining the numbered response equation with the retained terminal square gives the original-domain equality. ConstructedTowerProfiles and ResponsePositiveShiftConsumer use that concrete terminal to produce the positive word and signed correction. OriginalPositiveWordAssembly supplies the full outgoing input identification.")),
            Describe.Remark(DescribeId.Create("response-realization-response-two-sided-consumer-original"), DeclarationHandle.Create(Prefix + "original"), H("original"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Bundles the original finite essential graph and its exact typeclass data as a Presentation. It is used by terminal, the output word, OriginalPositiveWordAssembly and the preserved original application; its fields are data, not new graph theorems.")))),
            Describe.Remark(DescribeId.Create("response-realization-response-two-sided-consumer-response"), DeclarationHandle.Create(Prefix + "response"), H("response"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Bundles the exact numbered response graph with its unchanged counted edge type and essentiality from numbered_response_reduction. It is used by terminal and the output word. No new enumeration is supplied.")))),
            Describe.Remark(DescribeId.Create("response-realization-response-two-sided-consumer-terminal"), DeclarationHandle.Create(Prefix + "terminal"), H("terminal"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Constructs the first outgoing step, the recursive tail, both concrete terminal presentations and the finite relabeling. It proves both depths and the literal all-history square. The profile and positive-word construction use this data.")))))));
}
