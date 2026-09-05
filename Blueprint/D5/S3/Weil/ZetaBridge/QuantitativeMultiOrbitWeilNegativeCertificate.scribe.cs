using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class QuantitativeMultiOrbitWeilNegativeCertificateDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaBridge/QuantitativeMultiOrbitWeilNegativeCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform quadratic remainder below the least multiplicity-weighted odd margin preserves a whole finite-dimensional family of strict negative full Weil squares.",
        H("Quantitative Multi-Orbit Weil Negative Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-quadratic-remainder-preserves-negativity"),
                DeclarationHandle.Create(
                    Prefix + "strictNegative_of_uniformQuadraticRemainder"),
                H("A strict diagonal margin dominates a uniform quadratic remainder"),
                StatementSource.FromAuthor(Disp(F.Id(
                    "epsilon below margin implies target plus remainder is strictly negative on every nonzero vector"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem is a reusable finite-dimensional perturbation result. The negative target is bounded above by minus the margin times coefficient energy, while the absolute remainder is bounded by epsilon times the same energy. Strict epsilon-margin separation preserves negative definiteness on the entire space, including all cross terms represented by the remainder."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("multi-orbit-full-weil-negative-family"),
                DeclarationHandle.Create(
                    Prefix + "quantitative_multiOrbit_weil_negative_certificate"),
                H("A certified reduced frame yields an injective family of negative full Weil tests"),
                StatementSource.FromAuthor(Disp(F.Id(
                    "frameOddSynthesis is injective and every nonzero synthesized coefficient vector has negative full zeroSum"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The exact selected-orbit target is minus four times the multiplicity-weighted odd energy. Everything else in the unconditional symmetric zero sum is defined as the remainder. A certificate consists only of a positive multiplicity floor and an independently proved uniform remainder bound below the resulting strict margin.")),
                    Paragraph(Text(
                        "The theorem does not assume a bound on each basis vector separately. It requires a single quadratic estimate valid for every coefficient vector, which is the correct condition for preserving an entire negative subspace."))),
                DescribeRole.Theorem)),
        []));
}
