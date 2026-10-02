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
            Definition("interval-family", "IntervalFamily", "Positive finite or essential intervals",
                "An occurrence has a real birth and a death in WithTop(Real), strictly greater than "
                    + "birth. Infinity is allowed. Repeated intervals retain separate occurrences."),
            Definition("interval-space", "intervalSpace", "The actual supported coordinate subspace",
                "At time r this is the subspace of K-valued occurrence coordinates that vanish "
                    + "unless birth <= r < death. The field is arbitrary."),
            Definition("interval-arrow", "intervalArrow", "The actual structure map",
                "For s <= t, retain source coordinates whose deaths are strictly above t and kill "
                    + "the others. The output lies in the supported subspace at t."),
            Definition("interval-sum", "intervalSum", "A real persistence functor",
                "The supported spaces and actual arrows form a functor from the real preorder to "
                    + "ModuleCat. Identity and composition hold at exact birth/death points, "
                    + "zero spaces and infinite tails. The substantive classification and "
                    + "arbitrary competing-decomposition uniqueness proof is in RealDecomposition."),
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
                        + "s -> t and t -> u puts their actual images in the target birth-image "
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
                        + "Same-image quantitative sandwiches and exact stability are "
                        + "additional conclusions, not assertions of these injections."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(string id, string declaration, string heading, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(body))), DescribeRole.Definition);
}
