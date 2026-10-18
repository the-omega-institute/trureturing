using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class FiniteFairBitReturnRestartDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitReturnRestart.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FiniteFairBitReturnRestart", H("Fresh suffixes at variable-request service returns"), Blocks(
            Paragraph(Text("The instruction graph is the existing deterministic/fair operational graph. Bounded execution observes the complete absorbing return label and its actual unused suffix. Deterministic steps preserve the suffix; a fair alternative consumes one bit even when the two destinations coincide. At a returned label the stopped analysis consumes no more bits. The physical service is not reset.")),
            Paragraph(Text("The one-step tape split and original primitive mass supplier give a joint factorization at every fixed physical step bound. Returned label/suffix events increase with that bound because absorption leaves both unchanged. Their countable union is the first-return readout, so continuity from below proves freshness at a variable number of fair requests. The nonreturn event is kept as none and has zero measure under the literal almost-sure-return premise. No geometric tail, rationality, normalization or renewal law is assumed.")),
            Paragraph(Text("The joint law is the product of its own actual returned-label marginal and the original fair-tape law. The pathwise clause identifies the suffix at a first hit n as the original tape shifted by requests at n. With complete ready snapshots as labels, every returned private field remains in that marginal. Index, labels, output lists and suffixes are proof-side readouts, not additions to charged memory.")),
            Paragraph(Text("Repeated services use one common graph and an explicit boundary map. Each invocation consumes the suffix left by its predecessor and enters from its predecessor's complete returned label. The finite-prefix theorem derives the ordered product of actual exit masses together with a fresh remaining suffix. An empty prefix consumes no bits. The boundary map names supplied entrances; the theorem does not establish that an arbitrary physical setup or input change costs zero. It asserts no eventual completion of an infinite native future.")),
            Paragraph(Text("For original PH37 installations, physical charging, paid fetch/decode, executable interface receipts, invocation-relative returns and semantic next-letter refinement remain necessary applications. These statements do not supply those bridges or the four-service PH38.1 theorem. In particular, first-return labels are not automatically semantic letters, a rendered old record is not a new selection, and a final buffer does not recover an erased emission. The same-update joint identity and actual-history compatibility remain separate original conditions.")),
            Node("statement-0", "actual_return_restart"),
            Node("statement-1", "repeated_service_prefix"))));
    private static DocumentBlock.Describe Node(string id, string name) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The compiled statement specifies the actual graph, lawful entrance return premises and exact execution readouts."))),
            DescribeRole.Theorem);
}
