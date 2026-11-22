using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry.Permutohedra;

internal sealed class FaceFlagsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Geometry/Permutohedra/FaceFlags";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/rossi2026permutohedron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutation flags and free ranks.",
        H("Permutation flags and free ranks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("faceflags-preceding"),
                DeclarationHandle.Create(Module + ".preceding"),
                H("Cuts preceding a label"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a cut chain and a label, keep the cuts of the chain that omit the label."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("faceflags-exists-flag-extension"),
                DeclarationHandle.Create(Module + ".exists_flag_extension"),
                H("Extending a chain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Sort the labels by the number of cuts they lie outside, breaking ties by label. Every cut is an initial segment of the resulting permutation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("faceflags-isatom-iff-flag"),
                DeclarationHandle.Create(Module + ".isAtom_iff_flag"),
                H("Atoms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A face is an atom exactly when it is the full chain of proper prefixes of a permutation. Each full chain has one cut at every proper rank, so it has no proper extension as a chain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("faceflags-occupied"),
                DeclarationHandle.Create(Module + ".occupied"),
                H("Occupied ranks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The occupied ranks of a chain are the cardinalities of its cuts, viewed as proper ranks."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("faceflags-free"),
                DeclarationHandle.Create(Module + ".free"),
                H("Unoccupied ranks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The free ranks of a chain are the proper ranks outside its occupied set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("faceflags-card-rank-type"),
                DeclarationHandle.Create(Module + ".card_rank_type"),
                H("Number of proper ranks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n, the number of ranks strictly between zero and n is n minus one in the natural numbers, with subtraction truncated at zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("faceflags-card-free"),
                DeclarationHandle.Create(Module + ".card_free"),
                H("Free ranks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a positive number of labels, the number of proper ranks without a cut equals the rank of the face. The sizes of the cuts of a chain are distinct."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("faceflags-prefix-mem-cuts-iff"),
                DeclarationHandle.Create(Module + ".prefix_mem_cuts_iff"),
                H("Prefixes at occupied ranks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If a permutation flag contains all cuts of a chain, the prefix at a proper rank belongs to the chain exactly when that rank is occupied by the chain."))),
                DescribeRole.Theorem))));
}
