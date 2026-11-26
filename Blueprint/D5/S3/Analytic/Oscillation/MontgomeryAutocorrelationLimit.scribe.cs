using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class MontgomeryAutocorrelationLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Autocorrelation from the Montgomery unit band",
        H("An unweighted autocorrelation limit for finite spectral cutoffs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-band-autocorrelation-limit"),
                DeclarationHandle.Create("D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit.spectral_unweighted_limit"),
                H("Autocorrelation from the Montgomery unit band"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume bounded two-term counting discrepancy at every real height at least two pi and a uniform Montgomery profile on the unit band. For a real Schwartz test with Fourier support in the unit band, form the sum of its autocorrelation over all ordered pairs of ordinates through H at the mean spacing scale. Include all multiplicities. Divide by H log H over two pi.")),
                    Paragraph(Text("The quotient tends to the square of the integral of the test plus its Fourier energy weighted by absolute frequency. The Fourier transform of the autocorrelation is the squared modulus of the Fourier transform of the test. The exponential peak in the profile becomes an approximate identity of mass one, and the uniform remainder gives a vanishing integrated error.")),
                    Paragraph(Text("Bounded discrepancy bounds the number of atoms in each scaled distance shell. Rapid decay of the autocorrelation controls the shell sum of the change from the Lorentz pair weight to one. After counting normalization the cost tends to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("autocorrelation-from-test-convergence"),
                DeclarationHandle.Create("D5/S3/Analytic/Oscillation/MontgomeryAutocorrelationLimit.spectral_unweighted_limit_of_test_limit"),
                H("Unweighted autocorrelation from convergence against fixed tests"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the same spectrum, assume that for every fixed real Schwartz test with Fourier support on the unit band, integrating the Montgomery profile against its squared Fourier modulus tends to the square of the test integral plus the Fourier energy weighted by absolute frequency. If a single bound controls the two-term counting discrepancy at every real height at least two pi, the unweighted autocorrelation sum of that test has the same limit after division by H log H over two pi.")),
                    Paragraph(Text("The Fourier integral equals the normalized Lorentz-weighted autocorrelation at the same cutoff. The bound on the number of ordinates per scaled distance shell makes the normalized cost of removing the Lorentz weight tend to zero."))),
                DescribeRole.Theorem))));
}
