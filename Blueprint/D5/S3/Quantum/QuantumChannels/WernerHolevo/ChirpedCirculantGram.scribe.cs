using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.WernerHolevo;

internal sealed class ChirpedCirculantGramDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedCirculantGram";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/HilbertOperators/girard2022mixedunitaryrank");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier construction and Gram factorization of chirped circulants.",
        H("Fourier construction and Gram factorization of chirped circulants"),
        Blocks(
            Describe.Lean(DescribeId.Create("chirped-unitary"),
                DeclarationHandle.Create(Module + ".chirped_unitary"),
                H("Unitarity under diagonal phase multiplication"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A unit-modulus spectrum gives a unitary circulant. Multiplying on both sides by the diagonal "
                    + "chirp and modulation phases preserves unitarity. Evenness of the spectrum supplies the separate "
                    + "transpose identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("chirped-gram"),
                DeclarationHandle.Create(Module + ".chirped_gram"),
                H("Separation of the Hilbert–Schmidt pairing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The equality holds for arbitrary complex spectra and all chirp and modulation indices over a "
                    + "nonzero cyclic order admitting an inverse of two. The change of variables to the sum and "
                    + "difference of the matrix indices separates the seed pairing from the quadratic character sum."))),
                DescribeRole.Theorem))));
}
