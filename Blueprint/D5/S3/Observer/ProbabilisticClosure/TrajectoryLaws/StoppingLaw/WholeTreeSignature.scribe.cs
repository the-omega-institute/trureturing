using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw;

internal sealed class WholeTreeSignatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/WholeTreeSignature.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole-tree oriented signatures and paid execution", H("Whole-tree oriented signatures and paid execution"), Blocks(
            Paragraph(Text("A read position is a finite ordered list of Boolean branch choices. The parity skeleton retains every terminal label, branch and address parity. In each phase, the signature records equality and inequality among the target spin index and the minus and plus spin indices of every potential read occurrence. Missing and inactive positions repeat the target index, so they add no equality information.")),
            Theorem("address-at-skeleton", "addressAt_skeleton", "Positions in the parity skeleton", "For every tree and position, the address in the parity skeleton is the original address reduced modulo two, when that position is a read node."),
            Theorem("relabel-height", "relabel_height", "Relabeling preserves height", "Every integer address map preserves tree height on every formal branch."),
            Theorem("relabel-addresses", "relabel_addresses", "Potential address image", "The finite set of addresses after relabeling is exactly the image of the original set."),
            Theorem("address-at-relabel", "addressAt_relabel", "Relabeling at an occurrence", "At every ordered position, address lookup commutes with the integer address map."),
            Theorem("address-at-in-addresses", "addressAt_in_addresses", "Occurrence addresses are potential addresses", "Every successful address lookup belongs to the tree address set."),
            Theorem("addresses-card-le-read-count", "addresses_card_le_readCount", "Distinct addresses and read occurrences", "The number of distinct potential addresses is at most the number of potential read occurrences. Repeated addresses and mutually exclusive branches remain distinct occurrences in the latter count."),
            Theorem("read-count-height-bound", "readCount_height_bound", "Binary-tree occurrence bound", "For every tree, its potential read count plus one is at most two raised to its height."),
            Theorem("skeleton-relabel", "skeleton_relabel", "Parity-preserving relabeling", "A map preserving parity at every potential address leaves the complete ordered parity skeleton unchanged."),
            Theorem("same-signature-observation-law", "same_signature_observation_law", "Signature invariance of the full observation law", "For every Boolean target j, pair of read trees with the same signature, and permitted Bias, the original source pushforward laws agree. The observation includes the actual hidden target, optional output, return indicator and paid depth. The proof transports spin assignments phase by phase and then proves execution commutation by recursion over the common ordered skeleton. Nonreturn leaves retain their exact paid depth; repeated and separator calls remain charged."))));
    private static DocumentBlock.Describe Theorem(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
