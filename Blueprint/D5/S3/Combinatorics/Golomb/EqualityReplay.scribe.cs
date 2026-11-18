using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Golomb;

internal sealed class GolombEqualityReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Golomb/EqualityReplay.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/notik2026golomb");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader("D5/S3/Combinatorics/Golomb/EqualityReplay",
            "Checked equality leaves prove integral gaps and normalized marks.",
            "kernel-replayed-certificate"),
        H("Golomb equality certificates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golomb-equality-leaf-cert"),
                DeclarationHandle.Create(Prefix + "LeafCertificate"),
                H("Exact certificates for a tied leaf"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A certificate checks a contradiction, proves an integral expression for each gap, "
                    + "or closes both signs of a separation relation. It can also exhaust the finite "
                    + "integer ranks of slots in a saturated packing row. Signed combinations use only "
                    + "rows already proved tight, and inequality combinations require nonnegative weights."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golomb-equality-cover"),
                DeclarationHandle.Create(Prefix + "cover"),
                H("Traversal checks a certificate at every tied bound leaf"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For the same tree used by the bound proof, the checker recomputes the weighted "
                    + "right-hand side at each bound leaf. A tie consumes the next certificate, keyed "
                    + "by the actual leaf identifier. Acceptance at the root requires an empty remainder."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golomb-equality-replay"),
                DeclarationHandle.Create(Prefix + "replay_marks_integral"),
                H("Every normalized mark is integral at an accepted target"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A real ruler at the target follows a valid route in one of the two orientations. "
                    + "The checked certificate on that route proves that its gaps are integral. Reflection "
                    + "reverses the gaps, and prefix sums recover every mark from the prescribed initial zero."))),
                DescribeRole.Theorem)), []));
}
