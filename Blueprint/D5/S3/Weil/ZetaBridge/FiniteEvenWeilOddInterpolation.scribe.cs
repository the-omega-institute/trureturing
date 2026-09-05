using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class FiniteEvenWeilOddInterpolationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaBridge/FiniteEvenWeilOddInterpolation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite sign-separated conjugate spectral pairs admit an explicit linear synthesis by scalar even Weil tests, with an exact multiplicity-weighted negative Gram matrix.",
        H("Finite Even Weil Odd Interpolation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-even-weil-odd-interpolation"),
                DeclarationHandle.Create(
                    Prefix + "finite_even_weil_odd_interpolation_spec"),
                H("Reduced odd evaluation has an explicit finite right inverse"),
                StatementSource.FromAuthor(Disp(F.Id(
                    "frameOddReadout (frameOddSynthesis a) equals a and the basis Gram has full negative index"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A frame records finitely many off-line nonreal orbit channels, a two-node presentation for each conjugate spectral pair, and the exact sign-separation hypothesis required by the frozen even Paley-Wiener interpolation theorem.")),
                    Paragraph(Text(
                        "Chosen coordinate interpolants are combined by an explicit bundled finite linear-combination constructor. Fourier-Laplace linearity proves that this synthesis is a right inverse to the reduced odd readout, rather than merely a collection of unrelated existential witnesses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("observable-odd-gram-negative-index"),
                DeclarationHandle.Create(Prefix + "frameOddGram_negIndex"),
                H("The observable odd Gram index equals the number of independent orbit channels"),
                StatementSource.FromAuthor(Disp(F.Id(
                    "negIndex(-4 diagonal multiplicity) equals the finite frame cardinality"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The basis Gram is exactly minus four times the positive analytic-multiplicity diagonal. Consequently its negative is positive definite and the repository spectral inertia owner computes one negative direction per independently interpolated orbit channel. Multiplicity changes the weight and strict margin, not the scalar observer dimension."))),
                DescribeRole.Theorem)),
        []));
}
