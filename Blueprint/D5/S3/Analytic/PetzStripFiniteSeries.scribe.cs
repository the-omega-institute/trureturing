using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PetzStripFiniteSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weighted boundary deficits of a finite complex exponential overlap recover its negative real derivative at zero.",
        H("Finite complex overlaps on the Petz strip"),
        Blocks(
            Paragraph(Text("Let F(z) be the finite sum of c(i) exp(omega(i) z) with complex coefficients and real frequencies. Define each boundary deficit at real part a and imaginary part s to be 2(1 - Re F(a + i s)). The real parts of the left and right edges are zero and one half.")),
            Describe.Lean(
                DescribeId.Create("petz-finite-overlap-derivative"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzStripFiniteSeries.hasDerivAt_finiteOverlap_zero"),
                H("Derivative of the finite overlap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The complex derivative of F at zero is the finite sum of c(i) omega(i). Zero frequencies contribute zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-finite-overlap-strip"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzStripFiniteSeries.integral_finiteOverlap_strip"),
                H("Two integrable boundary deficits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/yang2026quantumdataprocessing")),
                Blocks(
                    Paragraph(Text("Assume Re F(0) = 1 and the lower boundary deficit is nonnegative at every real s. The deficits multiplied respectively by pi/(cosh(2 pi s) - 1) and pi/(cosh(2 pi s) + 1) are each Lebesgue integrable on the whole line. Their integrals sum to the negative real part of the complex derivative at zero.")),
                    Paragraph(Text("Yang's Lemma III.1, Eq. (III.2), gives the strip weights and boundary derivative formula for bounded harmonic functions with quadratic vanishing at the lower point. The repository proves integrability and the identity for finite exponential overlaps. Normalization and lower nonnegativity give quadratic vanishing at the singular lower point, where the reflection average dominates the actual deficit after weighting. On the upper line, finite exponential magnitudes bound the full deficit in absolute value and the Poisson weight is integrable. Reflection cancels the imaginary-coefficient sine terms in the two integrals. The upper cosine transform follows by dilating the compensated lower mode."))),
                DescribeRole.Theorem))));
}
