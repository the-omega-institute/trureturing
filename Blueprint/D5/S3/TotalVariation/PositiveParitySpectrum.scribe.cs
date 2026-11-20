using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class PositiveParitySpectrumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Embedding =
        LibraryNoteRef.Create("D5/L/TotalVariation/ardiyansyahkosta2021embedding");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half-space moment products decide affine independent-bit realizability when all sign moments are positive.",
        H("Realizing a positive parity spectrum"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-moment-realizability"),
            DeclarationHandle.Create(
                "D5/S3/TotalVariation/PositiveParitySpectrum.positive_moment_realizability"),
            H("The half-space product criterion"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Embedding),
            Blocks(
                Paragraph(Text(
                    "Let A be a finite additive commutative group with x+x=0 for all x. " +
                    "Let p be a real mass function whose total mass is one and whose sign " +
                    "moments are all strictly positive. For every nonzero a in A, compare " +
                    "the product of the moments over characters taking value -1 at a to the " +
                    "product over characters taking value +1 there. The former must be " +
                    "at most the latter.")),
                Paragraph(Text(
                    "The inequalities are necessary if p is an affine independent-bit law " +
                    "for any finite input type, any column map into A, any offset, and any " +
                    "input bias factors in the closed interval from -1 to 1. If the " +
                    "inequalities hold, there is a representation with offset zero and " +
                    "the identity column map on A. Every bias factor lies in (0,1]. " +
                    "A bit on the zero column contributes zero regardless of its value.")),
                Paragraph(Text(
                    "Take logarithms of the positive moments. Fourier inversion gives a " +
                    "logarithmic bias at each column. The half-space inequalities make each " +
                    "nonzero-column logarithmic bias nonpositive, so exponentiating gives " +
                    "a valid bias factor. Moment inversion identifies the reconstructed " +
                    "mass function with p. This is the elementary binary-group case of " +
                    "the symmetric model embedding criterion."))),
            DescribeRole.Theorem))));
}
