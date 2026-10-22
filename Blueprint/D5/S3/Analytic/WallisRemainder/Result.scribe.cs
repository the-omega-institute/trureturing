using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WallisRemainder;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/mahmoudmortici2026wallisratio");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict monotonicity of three Wallis gamma remainders.",
        H("Wallis gamma remainder functions"), Blocks(
            Describe.Lean(DescribeId.Create("wallis-remainder-strict-monotonicity"),
                DeclarationHandle.Create("D5/S3/Analytic/WallisRemainder/Result.result"),
                H("The three strict monotonicity inequalities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every pair of positive real numbers x<y, the functions defined in Defs satisfy mu(x)<mu(y), chi(x)<chi(y), and theta(y)<theta(x). The logarithm of the Wallis ratio and the inner reciprocal denominator defining mu are nonzero at every positive argument.")),
                    Paragraph(Text("Let S_P and S_Q be the Stieltjes transforms of the positive spectral law and its size-biased law. The mean of P is m=1/24 and its variance is 31/2880. The mean of Q is c=3/10 and its variance is 771/5600. Integration of v/(z+v)=1-z/(z+v) gives z S_P(z)=1-m S_Q(z). The analytic representation of the logarithmic remainder and exact algebra then identify theta(x)=-G_P(x^2), chi(x)=G_Q(x^2), and mu(x)=H_Q(x^2)-m, where G is the normalized Jensen remainder and H(z)=1/S(z)-z.")),
                    Paragraph(Text("Both laws have finite positive variance. Their normalized Jensen remainders increase strictly, and the inverse transform offset of Q increases strictly. Since squaring increases strictly on positive reals, the three stated comparisons follow with their respective signs. Positivity of both transforms and the size-bias identity also prove both nonvanishing assertions for mu."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mahmoud-mortici-2026-wallis-remainder-monotonicity"),
                    ResolutionKind.Proved)))));
}
