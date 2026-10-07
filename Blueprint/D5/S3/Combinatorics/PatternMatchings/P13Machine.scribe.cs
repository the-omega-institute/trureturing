using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class P13MachineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13Machine.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit local transitions retain every earlier survivor comparison at arbitrary height.",
        H("Normalized bases and pending openings"),
        Blocks(
            Node("p13-p13machine-base", "Post-closure base states", "Base",
                "S(m) has one decreasing block of old survivors. T(a,b) has two consecutive nonempty blocks in opening order, each decreasing in closing order, with the older block closing first. Pending openings are kept separately.", DescribeRole.Definition),
            Node("p13-p13machine-base-size", "Base survivor count", "size",
                "The size of S(m) is m, and that of T(a,b) is a+b.", DescribeRole.Definition),
            Node("p13-p13machine-base-cut", "Block boundary", "cut",
                "The boundary is zero for a single block and a for two blocks.", DescribeRole.Definition),
            Node("p13-p13machine-base-valid", "Normalized state validity", "Valid",
                "Every single-block state is valid. A two-block state is valid when both block sizes are positive.", DescribeRole.Definition),
            Node("p13-p13machine-before", "Prescribed precedence", "Before",
                "The first block precedes the second; within either block, larger opener indices precede smaller ones.", DescribeRole.Definition),
            Node("p13-p13machine-blocks", "Deleting zero-sized blocks", "blocks",
                "A two-block description with one empty block becomes a single decreasing block of the surviving size.", DescribeRole.Definition),
            Node("p13-p13machine-permitted", "Explicit closing-rank rules", "Permitted",
                "Ranks r are zero-based. With k pending openings, S(m) permits r<m+k and m<=r+1. T(a,b) permits exactly r+1=a, still within the active range. Thus the corresponding one-based rank i is r+1.", DescribeRole.Definition),
            Node("p13-p13machine-afterclose", "The next post-closure base", "afterClose",
                "After closing rank r, the survivors have consecutive block sizes r and size(base)+k-r-1, with empty blocks removed. Pending openings reset to zero.", DescribeRole.Definition),
            Node("p13-p13machine-compatible", "Preservation of the old base", "Compatible",
                "An old selected opener must precede all other old survivors. Every prescribed old comparison among the remaining openers must agree with the order imposed by this closure.", DescribeRole.Definition),
            Node("p13-p13machine-compatible-iff", "Exactly the permitted ranks preserve the old constraints", "compatible_iff",
                "For every valid base and every number of pending openings, compatibility with all old comparisons is equivalent to the explicit S/T closing-rank rule. In a T state, closing a pending opener would reverse a required comparison between the two nonempty old blocks.", DescribeRole.Theorem),
            Node("p13-p13machine-liftrank", "Original indices after deletion", "liftRank",
                "A surviving index below the deleted rank is unchanged; any other survivor index increases by one when mapped back to the old queue.", DescribeRole.Definition),
            Node("p13-p13machine-before-lift", "Ordering survives index deletion", "before_lift",
                "The two-block comparison is unchanged by lifting survivor indices back across the deleted rank.", DescribeRole.Theorem),
            Node("p13-p13machine-blocks-spec", "Normalization retains the exact order", "blocks_spec",
                "Removing empty blocks preserves survivor size and all pair comparisons and yields a valid base.", DescribeRole.Theorem),
            Node("p13-p13machine-transition-spec", "Every legal transition preserves every earlier comparison", "transition_spec",
                "The new base has exactly one fewer active opener, is valid, realizes the prescribed two-block order under the actual index deletion, and is compatible with every old precedence constraint.", DescribeRole.Theorem),
            Node("p13-p13machine-step", "General-rank scan letters", "Step",
                "A vertex either opens an arc or closes an arbitrary zero-based active rank.", DescribeRole.Definition),
            Node("p13-p13machine-acceptfrom", "Independent local acceptance", "AcceptFrom",
                "Opening increases the pending count without changing the old base. Closing requires a permitted rank, replaces the base by its normalized survivor state and clears pending openings. The empty suffix requires both old and pending counts to be zero.", DescribeRole.Definition),
            Node("p13-p13machine-accepted", "Complete scans", "Accepted",
                "For every n, accepted scans have length 2n and start from S(0) with zero pending openings. The carrier is defined solely by these local rules.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
