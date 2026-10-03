using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Persistence;

internal sealed class RealIntervalUniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/Persistence/RealIntervalUniqueness.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/bauer2015persistence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual supported interval sums used in natural classification and endpoint recovery.",
        H("Actual Real Interval Sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mono-death-window-count"),
                DeclarationHandle.Create(Prefix + "mono_death_window_count"),
                H("Actual monomorphisms bound birth/death window counts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For finite occurrence families and an actual natural map injective at every "
                        + "real time, the number of source intervals born by s and dying in (t,u] "
                        + "is at most the corresponding target number, for s <= t <= u. "
                        + "The upper cut u may be infinity; this version uses the birth image "
                        + "without an artificial arrow to an infinite-time object. "
                        + "Extend window coordinates into the source at s and t. Naturality at "
                        + "s -> t and, for finite u, t -> u puts their actual images in the target birth-image "
                        + "and death-kernel intersection. Restriction to the target window is "
                        + "injective, so the existing finrank comparison gives the count bound. "
                        + "No occurrence injection or quantitative endpoint bound is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("epi-birth-window-count"),
                DeclarationHandle.Create(Prefix + "epi_birth_window_count"),
                H("Actual epimorphisms bound surviving birth-window counts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For an actual natural map surjective at every real time and r <= s <= t, "
                        + "the target number of intervals born in (r,s] and surviving t is at "
                        + "most the source number. Lift target window coordinates at s. Split "
                        + "the lifted source vector at t into the recent-birth coordinates and "
                        + "the actual image from r. Naturality makes the latter invisible in "
                        + "the target recent-birth quotient. The resulting coordinate map is "
                        + "surjective; the existing surjective finrank comparison gives the "
                        + "count bound. Infinite deaths are included. Ordered occurrence "
                        + "injections, their composition, sandwiches and stability are not "
                        + "conclusions of this theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mono-ordered-occurrence-injection"),
                DeclarationHandle.Create(Prefix + "mono_ordered_occurrence_injection"),
                H("Monomorphism matching by increasing-birth ordinals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Fix a bijective increasing-birth enumeration of each death class in both "
                        + "finite families, including the essential class. An actual natural "
                        + "map injective at every real time gives an occurrence embedding "
                        + "preserving death and class ordinal, with target birth at most source "
                        + "birth. A finite real sample isolates each death class from the "
                        + "actual window inequality. The first k+1 source occurrences force "
                        + "the target occurrence of ordinal k to exist and be born in time. "
                        + "The enumeration retains tied occurrences separately. With a shared "
                        + "intermediate enumeration, ordinal preservation forces classwise "
                        + "composition; no arbitrary Hall matching is selected."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("epi-ordered-occurrence-injection"),
                DeclarationHandle.Create(Prefix + "epi_ordered_occurrence_injection"),
                H("Epimorphism matching by decreasing-death ordinals"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Fix a bijective decreasing-death enumeration of each birth class, with "
                        + "infinity first and a fixed order of tied occurrences. An actual "
                        + "natural map surjective at every real time gives a target-to-source "
                        + "occurrence embedding preserving birth and class ordinal, with "
                        + "target death at most source death. An earlier cutoff isolates the "
                        + "birth class, and a later finite sample isolates all survivors at "
                        + "a finite or infinite death threshold. Their actual window count "
                        + "forces the ordinal-k source occurrence to survive long enough. "
                        + "Shared intermediate ordinals force epimorphism-class composition. "
                        + "Quantitative estimates additionally require actual kernel or cokernel "
                        + "conditions; exact stability is not an assertion of this injection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mono-cokernel-trim-estimates"),
                DeclarationHandle.Create(Prefix + "mono_cokernel_trim_estimates"),
                H("Cokernel birth trims bound the fixed monomorphism matching"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Fix the increasing-birth enumerations in every death fiber and an "
                        + "ordinal-preserving occurrence injection for an actual natural "
                        + "monomorphism. For every nonnegative eta, assume that the actual "
                        + "target structure-map image from t to t+eta lies in the morphism's "
                        + "range at t+eta. Shift the birth of every target interval by eta "
                        + "and retain precisely the positive-length trims, including all "
                        + "essential intervals. Their coordinate inclusion at t has exactly "
                        + "the range of the target arrow from t-eta to t. Lift it through "
                        + "the actual monomorphism using its range equivalence. Cancellation "
                        + "proves naturality, and zero extension proves injectivity. "
                        + "A long target occurrence of ordinal k supplies k+1 trimmed "
                        + "occurrences, so their images force the same fixed ordinal-k "
                        + "image occurrence to exist and have birth at most target birth "
                        + "plus eta. A matched short occurrence satisfies the bound by "
                        + "positivity and equal death. Every long target occurrence is "
                        + "covered, every essential is covered without subtracting infinity, "
                        + "and eta zero forces full coverage and equal births."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("epi-kernel-trim-estimates"),
                DeclarationHandle.Create(Prefix + "epi_kernel_trim_estimates"),
                H("Kernel death trims bound the fixed epimorphism matching"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Fix decreasing-death enumerations in every birth fiber and an "
                        + "ordinal-preserving occurrence injection for an actual natural "
                        + "epimorphism. For every nonnegative eta, assume its actual kernel "
                        + "at t is contained in the kernel of the source arrow to t+eta. "
                        + "Retain intervals longer than eta, move each finite death left "
                        + "by eta and leave infinite deaths infinite. The canonical "
                        + "coordinate quotient is surjective and its kernel equals that "
                        + "actual structure-map kernel. The kernel inclusion permits "
                        + "the quotient lift; the surjective kernel-quotient equivalence "
                        + "factors it through the epimorphism. Its evaluation equation "
                        + "proves surjectivity, and precomposition with the original "
                        + "surjection proves naturality. Long source prefixes force "
                        + "coverage and a trimmed source death at most the paired image "
                        + "death for the already fixed injection. Short matched bars "
                        + "satisfy this by positivity. Finite source deaths are at most "
                        + "image death plus eta. Essential death is equivalent on paired "
                        + "occurrences and all source essentials are covered. Eta zero "
                        + "forces full source coverage and equality of deaths."))),
                DescribeRole.Theorem))));

}
