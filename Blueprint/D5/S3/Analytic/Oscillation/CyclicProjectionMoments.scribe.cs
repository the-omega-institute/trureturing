using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class CyclicProjectionMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Oscillation/CyclicProjectionMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The squared-minor law turns cyclic Fourier column overlaps into exact second moments.",
        H("Character sums of cyclic Fourier projection ensembles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("selected-fourier-columns"),
                DeclarationHandle.Create(Prefix + "selectedColumns"),
                H("Selected cyclic Fourier columns"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive integer M, an embedding a of k indices into Z/MZ "
                    + "selects the columns. The row indexed by x and the column indexed "
                    + "by i have entry s times the standard additive character at a(i)x, "
                    + "where s is a complex scaling factor."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cyclic-projection-second-moment"),
                DeclarationHandle.Create(Prefix + "cyclic_projection_second_moment"),
                H("Second moment of a cyclic character sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A be the image of the selected columns and choose s with "
                        + "s times its conjugate equal to 1/M. On each k-element subset X "
                        + "of the M sites, the probability is the squared modulus of its "
                        + "row minor. Sum the r-th cyclic character over X. The expectation "
                        + "of the squared modulus of this sum is k plus k squared at r=0, "
                        + "minus the number of a in A for which a-r also belongs to A.")),
                    Paragraph(Text(
                        "The diagonal site pairs contribute k. For distinct sites the "
                        + "squared-minor inclusion formula uses a product of two diagonal "
                        + "projection entries minus the product of conjugate entries. "
                        + "Expanding the latter and summing both site characters leaves "
                        + "exactly the ordered column pairs whose difference is r.")),
                    Paragraph(Text(
                        "This is a finite expectation at cyclic frequencies. A statement "
                        + "about one deterministic spectrum, all real cutoff heights or "
                        + "Lorentz-weighted pair correlations needs additional estimates."))),
                DescribeRole.Theorem))));
}
