using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubsetSpectrum;

internal sealed class NonnegativeRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubsetSpectrum/NonnegativeRecovery.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/ciprietti2023subsetsums");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative real coefficient multisets are determined by their full subset-sum multisets.",
        H("Nonnegative coefficient recovery"),
        Blocks(
            Describe.Lean(DescribeId.Create("nonnegative-recovery"),
                DeclarationHandle.Create(Prefix + "nonnegative_subset_sum_recovery"),
                H("Recovery with zeros and repetitions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For arbitrary finite multisets s,t of nonnegative reals, "
                    + "equality of their full occurrence spectra implies s=t. The cardinalities "
                    + "need not be assumed equal. Erasing one occurrence of zero from the spectrum "
                    + "removes the empty subset exactly once; its minimum is a least coefficient, "
                    + "including when this coefficient is zero. Cancelling its factor 1+X^a in "
                    + "the natural-coefficient additive monoid algebra reduces the coefficient count. "
                    + "This is a nonnegative consequence of Ciprietti and Glaudo's full-spectrum recovery."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("indexed-full-spectrum"),
                DeclarationHandle.Create(Prefix + "indexed_full_spectrum"),
                H("Indexed and multiset spectra"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The spectrum formed from all subsets of a finite index universe "
                    + "agrees with the multiset powerset construction on the coefficient occurrences. "
                    + "The powerset-map identity preserves repetitions and does not require an injective coefficient map."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SubsetSpectrum/SignAction"))]));
}
