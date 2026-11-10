using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattyOddWrapGaussianRootDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The order-nine Perron root fixes the Gaussian crossing and the quantitative alpha bounds used by the finite odd-wrap return counts.",
        H("The Gaussian root, secant, and alpha bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-odd-wrap-gaussian-root-secants"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot.gaussian_secant"),
                H("The Gaussian has an explicit lower secant slope on the relevant ray"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The defined function is gaussian(s)=Real.exp s+Real.exp(-9*s), the analytic model for the normalized quotient return ratio coming from the current finite group count formulas. For real a and b with 2/3<=a and a<=b, the theorem gives gaussian a+(98/75)*(b-a)<=gaussian b. Its exact derivative estimate uses exp(s)>=1+s and exp(-9*s)<=1/25 for every s>=2/3, so the derivative is at least 98/75 on the whole ray; this is a finite secant bound for the return-count crossing, with no asymptotic replacement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-odd-wrap-gaussian-root-strict-mono"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot.gaussian_strictMonoOn"),
                H("The Gaussian is strictly increasing on Ici(2/3)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The secant inequality is strict whenever a<b because its slope 98/75 is positive. Therefore gaussian is StrictMonoOn on Ici(2/3). In the finite group return-count argument this makes the normalized Gaussian comparison have a single crossing on the relevant ray, so the named root can be located and used without introducing an auxiliary monotonicity assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-odd-wrap-gaussian-root-at-s-star"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot.gaussian_s_star"),
                H("The Perron logarithm is the exact Gaussian root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The definition s_star=Real.log(dbonacciPerronRoot 9) reuses the existing order-nine Perron root beta rather than choosing an independent analytic root. The imported identity beta+(beta^-1)^9=2, together with exp(log beta)=beta and exp(-9*log beta)=beta^(-9), gives gaussian s_star=2 exactly. This identifies the crossing used to compare the complete original W19 and W33 return counts with the already frozen d-bonacci data."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-odd-wrap-gaussian-root-lower-location"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot.two_thirds_lt_s_star"),
                H("The positive Gaussian root lies strictly above 2/3"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The same positive root satisfies 2/3<s_star. The proof shows gaussian(s)<2 for every positive s<=2/3 by convexity on the interval from the two endpoint exponentials, while gaussian s_star=2; the positive logarithm root therefore cannot lie in that interval. This places the finite return-count crossing inside the ray where the secant and strict-monotonicity estimates apply."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-odd-wrap-gaussian-root-alpha-lower"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot.alpha_gt_twentyfour_twentyfive"),
                H("The reciprocal root scale gives 24/25<alpha"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The definition alpha=2/(3*s_star) converts the Gaussian crossing into the scale used in the odd-wrap threshold bracket. The strict upper-root argument uses the finite five-term exponential lower bound at 25/36 and the secant inequality to obtain s_star<25/36; combined with positivity, this gives 24/25<alpha. The bound is exact and supplies the rational margin needed in the finite group return-count estimates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-odd-wrap-gaussian-root-alpha-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianRoot.alpha_lt_one"),
                H("The reciprocal root scale is strictly below one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Since the root location theorem gives 2/3<s_star and the denominator 3*s_star is positive, the definition alpha=2/(3*s_star) yields alpha<1. Together with the preceding strict upper-root estimate this records the exact scale 24/25<alpha<1 used when translating Gaussian comparison into the current finite group return threshold."))),
                DescribeRole.Theorem))));
}
