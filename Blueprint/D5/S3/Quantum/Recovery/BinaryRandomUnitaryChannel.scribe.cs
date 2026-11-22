using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BinaryRandomUnitaryChannelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel";
    private static LibraryNoteRef RecoverySource => LibraryNoteRef.Create(
        "D5/L/Resource/fletchershorwin2007optimumrecovery");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, "Canonical overlap and actual CPTP realization of binary random-unitary channels.",
            "evidence-not-specified-by-formal-manifest"),
        H("Canonical fidelity of a binary random-unitary channel"),
        Blocks(
            Entry("reference", "canonical_reference", "Normalized untouched reference",
                "For every positive code dimension d, the canonical rank-one vector state has trace one. Tracing out the first, system factor leaves I/d on the second, reference factor."),
            Entry("kraus-overlap", "canonical_overlap_kraus", "Canonical Kraus trace identity",
                "On a nonzero code, the first-factor Kraus map tensored with the identity acts on the canonical rank-one state. "
                + "Each overlap amplitude is the Kraus trace divided by d. The overlap is the sum of squared moduli, with the reference left untouched and without rescaling the output trace."),
            Entry("binary-action", "binaryChannel_action", "Actual binary CPTP channel",
                "For real nonnegative weights p and q summing to one, square-root-weighted unitary Kraus matrices define a CPTP channel. Its action on every code matrix X is p UXU† + q VXV†."),
            Entry("binary-score", "binary_score_kraus", "Trace score after an actual CPTP decoder",
                "For d positive, an actual CPTP decoder D with Kraus matrices Kₐ acts after the binary channel. The score is the sum over a of p|tr(KₐU)|² + q|tr(KₐV)|² divided by d². The Kraus action hypothesis holds on every code matrix."),
            Entry("diagonal-optimum", "diagonal_binary_unitary_optimal", "One diagonal unitary bounds every decoder",
                "When the branches are the identity and a diagonal unitary, completeness of an arbitrary decoder bounds the norm of each vector of diagonal Kraus entries by one. The scalar optimizer realizes the resulting bound as a diagonal unitary CPTP channel."))));

    private static DocumentBlock Entry(string id, string name, string title, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(RecoverySource),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);
}
