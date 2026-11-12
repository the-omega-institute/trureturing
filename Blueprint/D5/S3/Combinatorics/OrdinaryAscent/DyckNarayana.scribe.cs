using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OrdinaryAscent;

internal sealed class DyckNarayanaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OrdinaryAscent/DyckNarayana.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/alexandersson2026dyck");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Licensed suffix-ballot enumeration of actual Mathlib Dyck-word peak fibers, used by the ordinary-avoider statistic equivalence.",
        H("Dyck peaks and Narayana numbers"),
        Blocks(
            Paragraph(Text("Adapted from Per Alexandersson's Apache-2.0 RealRooted source at commit 27276f93bbaf6b46bce689bca110bbacab1bba6b, with proof credit to Aristotle (Harmonic). The Lean module preserves the copyright notice, complete license and modification notice. No broad dependency or pin upgrade is introduced.")),
            Node("narayana", "Narayana numbers", "narayana",
                "The natural-number quotient choose(n,k) choose(n,k-1) divided by n, with N(0,0)=1 and N(0,k)=0 for positive k. Truncated subtraction requires the explicit positive-peak hypotheses in the quotient theorem.", DescribeRole.Definition),
            Node("peakCountList", "Adjacent UD count", "peakCountList",
                "Count adjacent up-down factors in a list of Dyck steps.", DescribeRole.Definition),
            Node("peakCount", "Peaks of an actual Dyck word", "peakCount",
                "Apply the adjacent UD count to the underlying list of a Mathlib DyckWord.", DescribeRole.Definition),
            Node("pc-U", "Prepending an upstep", "pc_U",
                "Prepending an upstep creates exactly one new peak when the previous list starts with a downstep.", DescribeRole.Theorem),
            Node("pc-D", "Prepending a downstep", "pc_D",
                "Prepending a downstep preserves the adjacent UD count.", DescribeRole.Theorem),
            Node("narayana-mul", "Positive-size positive-peak quotient identity", "narayana_mul",
                "For nonzero n and nonzero k, n times the Narayana number equals choose(n,k) choose(n,k-1). The zero-peak case is excluded because natural subtraction makes the unrestricted formula false.", DescribeRole.Theorem),
            Node("cardinality", "Actual Dyck peak fibers", "card_semilength_peakCount",
                "The cardinality of actual Dyck words with semilength n and k adjacent UD peaks is N(n,k), provided the pair is not (1,0). This is a statement about actual finite fibers, not a formal generating series.", DescribeRole.Theorem),
            Node("excluded-case", "The excluded fiber is empty", "card_semilength_one_peakCount_zero",
                "No actual Dyck word has semilength one and zero peaks. This separately handles the exceptional natural-quotient boundary.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(("dycknarayana-" + id).ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
