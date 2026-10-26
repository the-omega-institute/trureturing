using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubsetSpectrum;

internal sealed class EvenBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first moment and complementation recover the full spectrum from its even part in odd length.",
        H("Even and full subset spectra"),
        Blocks(
            Definition("even-subsets", "evenSubsets", "Even index subsets",
                "For a finite index set s, evenSubsets s consists of its subsets with even cardinality."),
            Definition("odd-subsets", "oddSubsets", "Odd index subsets",
                "For a finite index set s, oddSubsets s consists of its subsets with odd cardinality."),
            Definition("even-spectrum", "evenSubsetSums", "The even occurrence spectrum",
                "For b indexed by s, each even index subset contributes one occurrence of its coefficient sum. "
                + "Equal numerical sums from different subsets remain separate occurrences; zero coefficients "
                + "and repeated coefficients are allowed."),
            Definition("odd-spectrum", "oddSubsetSums", "The odd occurrence spectrum",
                "Each odd index subset contributes one occurrence of its coefficient sum."),
            Definition("full-spectrum", "fullSubsetSums", "The full occurrence spectrum",
                "Each index subset, including the empty set exactly once, contributes one occurrence of its sum."),
            Theorem("even-first-moment", "even_first_moment", "The even incidence first moment",
                "If s has at least two indices, summing the even spectrum gives "
                + "2^(|s|-2) times the sum of the coefficients. Inserting one index splits "
                + "subsets into those containing it and those avoiding it, interchanges the two "
                + "parities in the containing part, and gives the cardinal and weighted recurrences."),
            Theorem("odd-reflection", "odd_spectrum_reflection", "Complementation reflects the even spectrum",
                "For an odd finite index universe and total coefficient sum B, the odd spectrum "
                + "is the multiset image of the even spectrum under x ↦ B-x. Complementation "
                + "is a bijection on index subsets, so this equality preserves multiplicities "
                + "even when several subsets have the same sum."),
            Theorem("even-determines-full", "even_spectrum_determines_full", "Even equality determines full equality",
                "Let m be odd and at least three, and let b,c be arbitrary real coefficient families "
                + "on Fin m. Equality of their even occurrence spectra implies equality of their "
                + "total coefficient sums and equality of their full occurrence spectra. The "
                + "positive first-moment factor determines the common total; reflection then "
                + "recovers both odd spectra, and adjoining the even and odd parts recovers the full spectra.")),
        []));

    private static DocumentBlock Definition(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
