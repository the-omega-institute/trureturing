using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.BurnolGram;

internal sealed class SameWindowSmoothCutoffDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/BurnolGram/SameWindowSmoothCutoff.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smooth an interior box without enlarging the original window, then control the error by the width of its two boundary strips.",
        H("Smooth Approximation in the Same Window"),
        Blocks(
            Describe.Lean(DescribeId.Create("samewindowsmoothcutoff-cutoff"),
                DeclarationHandle.Create(Prefix + "sameWindowCutoff"), H("An interior smooth box"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let h be positive and let a be at least 4h. Average the box of radius a-3h/2 against the existing normalized even smooth seed of radius h/2. Multiplication by the box length removes its normalization. The result is an even smooth compactly supported complex function."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("samewindowsmoothcutoff-trial"),
                DeclarationHandle.Create(Prefix + "sameWindowSmoothTrial"), H("An actual smooth test"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply the interior cutoff by any even infinitely differentiable complex function p. No compact-support hypothesis on p is needed: the cutoff supplies compactness. In particular, this construction applies to every finite even cosine polynomial."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("samewindowsmoothcutoff-budget"),
                DeclarationHandle.Create(Prefix + "sameWindowSmoothTrial_budget"), H("Support, plateau and variation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The smooth test is supported in [-a+h,a-h] and agrees with p on [-a+2h,a-2h]. On this central interval, every translate of the seed support lies inside the averaging box, so the integral equals the seed's full unit mass. The complementary cutoff has norm at most one by integrating over the complementary set. The existing box-average derivative estimate gives a cutoff derivative L1 norm at most two, independently of h."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("samewindowsmoothcutoff-l1-error"),
                DeclarationHandle.Create(Prefix + "sameWindowSmoothTrial_L1_error_le"), H("An explicit boundary-layer error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Suppose the norm of p is at most a nonnegative M on [-a,a]. Compare the smooth test with the zero extension of p from the open interval (-a,a). The error vanishes on the central plateau and outside the original window. On each remaining boundary strip its norm is at most M. The two strips have total length 4h, giving L1 error at most 4Mh. This unweighted estimate alone does not establish convergence in a logarithmically weighted Fourier norm or in the Weil quadratic-form norm."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Keep h>0, 4h<=a, M>=0 and the same smooth even p with |p|<=M on [-a,a]. "
                + "For e=1_{(-a,a)}p-sameWindowSmoothTrial, the support and complementary "
                + "cutoff budget give |e(x)|<=M everywhere. Inside the open window, "
                + "e=(1-chi_h)*p. Outside it, including both original endpoints, the "
                + "smooth trial vanishes because its support lies strictly inside that window.")),
            Paragraph(Text(
                "The target indicator and the actual trial are separately integrable, so e is "
                + "integrable and its squared norm is almost everywhere strongly measurable. "
                + "The integrable majorant M*|e| bounds |e|^2 pointwise. Consequently the "
                + "squared norm is integrable, e belongs to L2, and the existing L1 estimate "
                + "gives integral |e|^2 <= M*integral |e| <= 4M^2h. This also covers M=0 "
                + "and 4h=a. It requires no derivative bound or Fourier identification.")),
            Paragraph(Text(
                "This is a direct application of the existing support and L1 declarations "
                + "with the standard square-integrability criterion. It supplies a physical "
                + "L2 input for bounded-operator perturbation arguments. Construction of the "
                + "actual pole and prime operators, the logarithmic form domain and a signed "
                + "Weil trial require their own mathematical identifications."))), []));
}
