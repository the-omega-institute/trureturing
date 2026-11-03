using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class FiniteSlitCoefficientIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCoefficientIdentity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual analytic coefficient is the same outer circle contribution plus the upper-bank imaginary moment.",
        H("FiniteSlitCoefficientIdentity"), Blocks(
            Describe.Lean(DescribeId.Create("same-source-coefficient-identity"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Every positive composition and every natural coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text("For every positive head, positive-entry tail and positive ell, this result reuses the SAME R0, rho, R, upper and B from FiniteSlitCircleDefect.result and FiniteSlitCompositionMoments.result. It preserves actual slit analyticity, agreement with the normalized disk reciprocal and the assigned removable value at zero. The statement includes head=1, the empty tail and n=0.")),
                    Paragraph(Text("For every natural n the actual derivative divided by n! equals outerCoefficient plus (1/pi) times the integral from 1 to R of Im(upper(x))/x^(n+1). outerCoefficient is the existing positively oriented circle integral with its single cut point set to zero. Both CircleIntegrable and IntervalIntegrable are proved, and the SAME n-independent B bounds its norm by B/R^n.")),
                    Paragraph(Text("Conjugation of the actual source branch pairs the two angular semicircles. The imaginary part of the existing upper logarithmic rectangle cancels the real negative-axis edge. Exponential substitution supplies the radial Jacobian; the segment below 1 has zero imaginary part, leaving the bank integral with a plus sign. The inner circle uses the pinned Cauchy derivative formula on the whole closed disk of radius 1/2, including its exact factorial normalization.")),
                    Paragraph(Text("The coefficients are proved real, and their actual Taylor series has HasSum equal to the same reciprocal at every point of the open unit disk. Equality with the original ordinary formal-inverse coefficients remains a separate obligation. Absolute summability with the signed prefix, all fixed positive smoothing orders j and the strict admissible binomial excess remain open. The full Xu--Zhao conjecture is not settled by this coefficient identity."))),
                DescribeRole.Theorem))));
}
