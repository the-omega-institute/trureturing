using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomeryCauchyDeficitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An upper Montgomery pair-sum bound strictly below the Cauchy threshold yields a fractional phase deficit.",
        H("A positive phase deficit from a Cauchy energy bound"),
        Blocks(
            Describe.Lean(DescribeId.Create("fractional-deficit-of-cauchy-cap"),
                DeclarationHandle.Create("D5/S3/Analytic/Oscillation/MontgomeryCauchyDeficit.fractional_deficit_of_cauchy_cap"),
                H("Phase deficit on fixed logarithmic bands"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let S be a locally finite positive spectrum with the inclusive counting asymptotic N(Y) divided by Y log Y tending to c = 1/(2 pi). Assume the unnormalized Montgomery pair sum is bounded above by kappa Y (log Y)^2 for one fixed kappa < 2 pi c^2. For each fixed A > 1 the bound holds for all sufficiently large Y and uniformly at log Y <= |t| <= A log Y.")),
                    Paragraph(Text("There is a fixed d > 0 such that on every such band, for sufficiently large Y, the magnitude of the multiplicity-weighted phase sum over ordinates through Y is at most (1-d)N(Y). Use the Cauchy lower estimate with R = epsilon Y. Choose epsilon small enough that the enlarged interval preserves the strict gap in the energy coefficient. The lost mass fraction tends to zero and the count asymptotic makes the gap uniform on each band."))),
                DescribeRole.Theorem))));
}
