using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233178NormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Normalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact first-appearance scanner identity with the correction for absent labels.",
        H("Symmetrizing the two noninitial complementary pairs"),
        Blocks(
            Paragraph(Text("The existing scanner weights count individual-colour lifts of a word "
                + "of complementary-pair labels. Exchanging labels one and two exchanges the two "
                + "possible orders of their first appearance. Label zero is fixed.")),
            Node("swap", "Exchange of the two noninitial labels", "The involution exchanges one "
                + "and two and fixes zero.", DescribeRole.Definition),
            Node("absent", "A whole-word absence indicator", "The integer indicator is one "
                + "exactly when the specified label never occurs, including for the empty word.",
                DescribeRole.Definition),
            Node("result", "Exact scanner symmetrization", "For every word length and every "
                + "pair-label word, four times the sum of its normalized scanner weight and that "
                + "of the exchanged word equals the displayed power of two times the absence "
                + "correction. The product term retains the all-zero case. The induction first "
                + "establishes the one-seen-label identity, then splits on the first label. "
                + "No colour-occurrence or surjectivity assumption is imposed. This pointwise "
                + "identity does not by itself identify a graph count or settle A233178.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
