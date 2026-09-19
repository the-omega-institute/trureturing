using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy;

internal sealed class IntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full Lebesgue translation energy.",
        H("Full Lebesgue translation energy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integral-checked-canonical-cell-integral-encloses"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Integral.checked_canonical_cell_integral_encloses"),
                H("Cell integration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a successful canonical cell check and the exact literal Weil test, the cell length times the rational integrand bounds encloses the real interval integral of the squared translation difference. Continuity supplies interval integrability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral-checked-literal-translation-energy-sound"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Integral.checked_literal_translation_energy_sound"),
                H("Whole-line enclosure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For rational polynomials p and q represented by the supplied lists and any rational shift s, checkFull verifies one payload for every adjacent source cell, exact hull endpoints, all cell checks and the requested binary width.")),
                    Paragraph(Text("A successful check encloses the genuine whole-line Lebesgue translationEnergy of any WeilTestFunction equal pointwise to the literal cutoff times the even polynomial. Adjacent interval integrals telescope, and the integrand vanishes outside the support hull. The aggregate rational width is at most 2^-k.")),
                    Paragraph(Text("The same module constructs literalRationalTest for every positive natural radius and rational p and q. Its smoothness follows from the smooth bump construction, its support lies in [-2R,2R], and its value is even."))),
                DescribeRole.Theorem)),
        []));
}
