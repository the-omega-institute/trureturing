using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class SingletonPrimeInsertionNegativeRegimeDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every increasing singleton prime insertion except (2,3) gives a negative full first compensated Laplace difference at every positive damping.",
        H("The Negative Regime of Singleton Prime Insertion"),
        Blocks(
            Paragraph(Text(
                "For actual primes q<p, use the original finite Euler product on the singleton {q} "
                + "and on the two-prime set {q,p}. Both normalized ratios use the common clock log(p), "
                + "and each numerator subtracts its exact slope at zero. The complete integrals extend "
                + "over the whole positive half-axis.")),
            Describe.Lean(
                DescribeId.Create("singleton-prime-insertion-negative-regime"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/SingletonPrimeInsertionNegativeRegime.result"),
                H("All increasing prime pairs except (2,3) have a strictly negative difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every prime pair q<p other than (2,3), and every sigma>0, both literal "
                        + "compensated integrands are absolutely integrable. The inserted integral minus "
                        + "the singleton integral is strictly negative.")),
                    Paragraph(Text(
                        "Let c=log(q)/log(p). The exact difference numerator is "
                        + "G(v)=((q-exp(-c*v))*(1-exp(-v))-(q-1)*v)/((p-1)*(q-1)). "
                        + "The curvature bracket is strictly negative for v>0 whenever 2*c<=q-1, "
                        + "including equality. Zero value and slope then give a strictly negative "
                        + "numerator on the entire positive axis. A global quadratic bound pays absolute "
                        + "integrability; positivity of the measure gives the strict integral sign.")),
                    Paragraph(Text(
                        "The already proved (2,3) transition is isolated within this increasing singleton "
                        + "family. A singleton {q} is not the full cutoff of all primes <=q. This result "
                        + "does not classify consecutive primorial insertions, the other factorial-density "
                        + "terms, or the complete Robin pairing, and it does not prove RH."))),
                DescribeRole.Theorem))));
}
