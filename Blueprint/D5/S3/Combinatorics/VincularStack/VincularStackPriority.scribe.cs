using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.VincularStack;

internal sealed class VincularStackPriorityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/VincularStack/VincularStackPriority.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two inserted maxima retain the order prescribed by their original output gaps.",
        H("Priority of Maximum Insertion Sites"),
        Blocks(
            Node("vincularstack-vincularstackpriority-adjacent-sites-active", "The two adjacent sites remain active", "adjacent_sites_active",
                "Let a word have distinct entries, let M exceed them all, and let L exceed M. If inserting M at a gap gives an SC output avoiding 231, then inserting L immediately before M or immediately after M also gives an SC output avoiding 231.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackpriority-two-marker-order", "Ordering two inserted entries", "two_marker_order",
                "Choose two distinct input gaps, the first strictly earlier than the second, and insert at them two entries each greater than every original entry. The original SC output splits into three consecutive words, and the two inserted entries occur between those words at their original output gaps. The entry with the smaller output gap comes first; when the output gaps coincide, the entry at the earlier input gap comes first. Deleting the two inserted entries recovers the original SC output.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackpriority-later-site-activity", "Activity at a later site", "later_site_activity",
                "Let a word have distinct entries, let M exceed them all, and let L exceed M. Suppose insertion of M at an earlier gap gives an SC output avoiding 231. Inserting L at a strictly later input gap in that word gives an SC output avoiding 231 if and only if inserting L at that gap in the original word does so and the later gap has a strictly smaller original output gap than the gap chosen for M.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
