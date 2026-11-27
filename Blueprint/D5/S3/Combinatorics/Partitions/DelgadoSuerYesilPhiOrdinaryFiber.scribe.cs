using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class DelgadoSuerYesilPhiOrdinaryFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiOrdinaryFiber.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/mazhang2026symmetrizationnegative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pseudo-Frobenius row deletion sends a proper numerical set to ℕ₀ ∖ {1} exactly when "
            + "the set is ordinary, and each ordinary semigroup is almost symmetric.",
        H("The fiber of row deletion over the numerical set missing only one"),
        Blocks(
            Describe.Lean(DescribeId.Create("delgado-suer-yesil-phi-ordinary"),
                DeclarationHandle.Create(Prefix + "ordinary"),
                H("The ordinary numerical sets"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For m ≥ 2, ordinary(m) is the numerical set O_m = {0} ∪ {n : n ≥ m}, "
                    + "encoded by its gaps 1, …, m − 1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("delgado-suer-yesil-phi-ordinary-fiber-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The ordinary fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every proper numerical set U with Frobenius number F, the row "
                        + "deletion Φ gives ℕ₀ ∖ {1} if and only if U = {0} ∪ {n : n > F}. For "
                        + "every m ≥ 2, O_m is an almost symmetric numerical semigroup with "
                        + "Frobenius number m − 1, and Φ(O_m) = ℕ₀ ∖ {1}. Hence the fiber of Φ over "
                        + "ℕ₀ ∖ {1} consists exactly of the sets O_m with m ≥ 2, with one source at "
                        + "each positive Frobenius number F, namely O_{F+1}. This is Corollary 4 "
                        + "of H. Ma and W. Zhang (version 2), stated there for numerical "
                        + "semigroups; the characterization holds for every proper numerical set.")),
                    Paragraph(Text(
                        "After deletion each retained row r is relabelled by its length plus the "
                        + "number of retained rows below it, so the retained labels strictly "
                        + "increase. Thus Φ(U) = ℕ₀ ∖ {1} forces the Frobenius row, which is always "
                        + "retained, to be the only retained row and to have length one, so no "
                        + "positive member lies below F. Conversely, if U = {0} ∪ {n : n > F}, "
                        + "every gap below F is pseudo-Frobenius, only the Frobenius row is "
                        + "retained and it has length one. For O_m all m − 1 gaps are "
                        + "pseudo-Frobenius, so 2g = 2(m − 1) = F + |PF|."))),
                DescribeRole.Theorem))));
}
