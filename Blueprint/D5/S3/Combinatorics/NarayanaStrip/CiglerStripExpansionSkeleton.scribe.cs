using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.NarayanaStrip;

internal sealed class CiglerStripExpansionSkeletonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionSkeleton.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2026narayana");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting horizontal steps separates a two-colored Motzkin path into a Dyck skeleton and its ordered colored gaps.",
        H("Dyck Skeletons and Colored Gaps"),
        Blocks(
            Node("cigler-strip-expansion-skeleton-extract-data", "Extract the skeleton and its gaps", "extractData",
                "From a sequence of Boolean pairs, retain each equal pair as a skeleton step with that Boolean value. Record each mixed pair as a horizontal color given by its first Boolean value in the gap at its location. There is one gap before the first skeleton step, one between each two consecutive skeleton steps, and one after the last. The empty sequence has an empty skeleton and a single empty gap.", DescribeRole.Definition),
            Node("cigler-strip-expansion-skeleton-insert-data", "Insert the colored gaps", "insertData",
                "Given a Boolean skeleton and a list of colored gaps, replace each color c in the first gap by the mixed pair (c, not c). If the skeleton is nonempty, append the equal pair for its first step and continue with the remaining skeleton and gaps. An empty gap list produces an empty sequence. When the skeleton is empty, only the first gap is used.", DescribeRole.Definition),
            Node("cigler-strip-expansion-skeleton-gap-charge", "Alternating gap charge", "gapCharge",
                "The charge of a list of colored gaps is the total length of alternating gaps. A Boolean phase indicates whether the first gap has an even index: when the phase is true it contributes zero, and when the phase is false it contributes its length. The phase changes at each following gap. Starting with phase true gives the total number of colors in the gaps with odd indices, numbering gaps from zero.", DescribeRole.Definition),
            Node("cigler-strip-expansion-skeleton-decomposition", "The skeleton decomposition bijection", "skeleton_decomposition",
                "Every finite sequence of Boolean pairs corresponds bijectively to a Boolean skeleton together with a list of colored gaps whose length is one more than the skeleton length. The forward map extracts the skeleton and gaps, and the inverse inserts them. The number of pairs equals the skeleton length plus the total number of colors. For every natural strip height b, the original sequence is a Motzkin path in the strip of height b exactly when its skeleton is a Dyck path in that strip.", DescribeRole.Theorem),
            Node("cigler-strip-expansion-skeleton-weights", "Weights determined by the skeleton and gaps", "skeleton_weights",
                "For every two-colored Motzkin path in a strip of natural height b, let d be the number of down-steps in its extracted skeleton, u the number of true colors in all its gaps, and q the total length of its odd-indexed gaps. Its ordinary weight starting at height zero is t^(d + u). Its signed weight starting at height zero is (-1)^(d + q) times t^(d + u). These are equalities of integer polynomials.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
