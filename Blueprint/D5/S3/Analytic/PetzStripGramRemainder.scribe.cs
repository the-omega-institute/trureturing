using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PetzStripGramRemainderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact Gram of exponential deficits on the two Petz strip boundaries dominates the logistic Gram of the boundary jump.",
        H("The exponential deficit Gram and its logistic remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petz-strip-gram-logistic"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzStripGramRemainder.logistic"),
                H("Logistic Fourier kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At zero the kernel is one. At frequency x away from zero it is (x/2) divided by sinh(x/2)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-strip-gram-deficit"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzStripGramRemainder.deficit"),
                H("Exponential deficit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At real frequency x and complex argument z the deficit is 1 minus exp(x z)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-strip-gram-entry"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzStripGramRemainder.stripGram"),
                H("Closed strip Gram entry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For frequencies x and y, the entry is minus (x+y)/2 plus exp(x/2) exp(y/2) times the logistic kernel at y-x, minus (y-x)/2 times coth((y-x)/2). The last factor takes the value one when x=y."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-strip-gram-weighted-pair"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzStripGramRemainder.weightedPair"),
                H("Weighted conjugate product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the vertical line with real part a, multiply the conjugate of the first deficit by the second deficit and by the weight at the imaginary coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-strip-gram-weighted-integrals"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzStripGramRemainder.weighted_strip_gram"),
                H("Exact weighted strip Gram"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/yang2026quantumdataprocessing")),
                Blocks(
                    Paragraph(Text("The weighted conjugate products on the lines with real parts zero and one half are integrable, and the sum of their whole-line integrals is the closed strip Gram entry. The weights are pi/(cosh(2 pi t) - 1) on the lower line and pi/(cosh(2 pi t) + 1) on the upper line. At x=y the entry is exp(x) - 1 - x.")),
                    Paragraph(Text("On the lower line, the two diagonal deficits dominate the absolute value of the mixed product. Reflecting the imaginary coordinate then reduces the integral to three compensated cosine modes. On the upper line each individual Fourier mode is integrable. The logistic Gram factorization supplies its real transform and fixes the unit mass. The finite-overlap strip identity evaluates the cosine coefficient using the coth integral on the lower line. Summing the two boundary contributions gives the closed formula, including zero and coincident frequencies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-strip-gram-remainder"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzStripGramRemainder.remainder"),
                H("Logistic remainder entry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtract the logistic kernel at y-x multiplied by the two real jump coefficients 1-exp(x/2) and 1-exp(y/2) from the closed strip Gram entry."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-strip-gram-remainder-nonneg"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzStripGramRemainder.remainder_quadratic_nonneg"),
                H("Nonnegative remainder for complex amplitudes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/yang2026quantumdataprocessing")),
                Blocks(
                    Paragraph(Text("For any finite family of real frequencies and complex amplitudes, the real part of the quadratic form of the closed logistic remainder is nonnegative. The family may contain coincident or zero frequencies.")),
                    Paragraph(Text("Apply the bounded analytic strip comparison to the finite linear combination of the deficits. The boundary energies give the closed strip Gram, while the difference of the two boundary values gives the logistic energy of the jump coefficients."))),
                DescribeRole.Theorem))));
}
