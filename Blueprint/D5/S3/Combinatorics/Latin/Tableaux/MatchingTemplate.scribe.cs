using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Latin.Tableaux;

internal sealed class MatchingTemplateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/daugherty2026counting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal source Latin tableaux: MatchingTemplate", H("MatchingTemplate for Latin tableaux"),
        Blocks(
            Paragraph(Text("Daugherty et al., arXiv:2610.29291v1, Conjecture 6.3 asks for the full count of Latin tableaux of shape (k,k-1,...,5,4,3,3) for every integer k at least five. Cells and integer symbols retain their fixed identities, and the prescribed symbol multiplicities are those of the conjugate partition.")),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-matchings"),
                DeclarationHandle.Create(Prefix + "matchings"), H("Literal matchings"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Ordered injective choices from the actual availability sets; the carrier retains each fixed column and symbol."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-mem-matchings"),
                DeclarationHandle.Create(Prefix + "mem_matchings"), H("Exact matching membership"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Membership is equivalent to positional set membership and no repeated entry."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-border"),
                DeclarationHandle.Create(Prefix + "border"), H("Insertion of a new row and symbol"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Remove each chosen symbol from its actual column, insert the fresh symbol in every column, then append the new universal column."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-tail"),
                DeclarationHandle.Create(Prefix + "Tail"), H("Ordered tail templates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The three-column base is [{x},{y,z},{x,y,z}], with distinct actual symbols. A step prefixes a fresh forced symbol and inserts it in every remaining column."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-tail-subsets"),
                DeclarationHandle.Create(Prefix + "tail_subsets"), H("Tail symbols lie in their actual carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Induction on the template proves each availability set is contained in B."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-tail-matchings"),
                DeclarationHandle.Create(Prefix + "tail_matchings"), H("Two tail choices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The base has two choices. Every inductive forced prefix preserves that exact number."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-tail-transition"),
                DeclarationHandle.Create(Prefix + "tail_transition"), H("Tail preservation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every actual matching and every fresh universal symbol, deleting the matching and bordering yields another tail template on the enlarged actual symbol set."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-headgraph"),
                DeclarationHandle.Create(Prefix + "headGraph"), H("The three distinguished columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("One column contains {a,c}, the other two contain {b,c}; the distinguished column remains a fixed position."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-headrows"),
                DeclarationHandle.Create(Prefix + "headRows"), H("The two head choices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The two literal permutations compatible with each distinguished position. No symmetry quotient is taken."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-full"),
                DeclarationHandle.Create(Prefix + "Full"), H("The complete availability invariant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Three distinct high symbols a,b,c lie outside B. The fixed head is followed by a tail whose columns are enlarged by all three high symbols."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-full-matchings"),
                DeclarationHandle.Create(Prefix + "full_matchings"), H("Four literal next rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("An exact head-tail splitting gives a product of two head choices and two tail choices. Append is injective on the fixed three-entry head."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("latin-matchingtemplate-full-transition"),
                DeclarationHandle.Create(Prefix + "full_transition"), H("The full all-parameter transition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every one of the four rows preserves the complete invariant. The high triple (a,b,c) becomes (b,c,u), and the low carrier becomes insert a B. All six distinguished-position/head-choice cases are proved."))), DescribeRole.Theorem)), []));
}
