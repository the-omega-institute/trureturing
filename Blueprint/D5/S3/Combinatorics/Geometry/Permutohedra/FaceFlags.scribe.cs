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
                DescribeId.Create("faceflags-card-free"),
                DeclarationHandle.Create(Module + ".card_free"),
                H("Free ranks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a positive number of labels, the number of proper ranks without a cut equals the rank of the face. The sizes of the cuts of a chain are distinct."))),
                DescribeRole.Theorem))));
}
