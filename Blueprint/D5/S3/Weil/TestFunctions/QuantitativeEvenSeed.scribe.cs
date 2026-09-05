using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class QuantitativeEvenSeedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/TestFunctions/QuantitativeEvenSeed.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized positive bump with radius h=1/(4(R+1)) has Fourier-Laplace norm at least one half at every node of norm at most R.",
        H("Explicit Nonvanishing Seed Radius"),
        Blocks(
            Describe.Lean(DescribeId.Create("quantitativeevenseed-radiusBump"),
                DeclarationHandle.Create(Prefix + "radiusBump"), H("Specified support radius"),
                StatementSource.FromAuthor(Disp(F.Id("For h>0 use bump radii rIn=h/2 and rOut=h."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The support radius is specified explicitly rather than selected from continuity of a transform."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitativeevenseed-normalizedEvenSeed"),
                DeclarationHandle.Create(Prefix + "normalizedEvenSeed"), H("An actual admissible even seed"),
                StatementSource.FromAuthor(Disp(F.Id("psi_h is the complex-valued normalized bump with specified radii h/2 and h."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuse the Mathlib normalized bump and the existing WeilTestFunction bundle. Smoothness, compactness and evenness are proved fields. Numerical evaluation still needs certified real-function computation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitativeevenseed-normalizedEvenSeed-integral"),
                DeclarationHandle.Create(Prefix + "normalizedEvenSeed_integral"), H("Unit complex mass"),
                StatementSource.FromAuthor(Disp(F.Id("Integral psi_h = 1."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport the existing normed-bump integral theorem through the real-to-complex map."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitativeevenseed-normalizedEvenSeed-norm-integral"),
                DeclarationHandle.Create(Prefix + "normalizedEvenSeed_norm_integral"), H("Unit absolute mass"),
                StatementSource.FromAuthor(Disp(F.Id("Integral |psi_h| = 1."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The underlying bump is nonnegative, so its absolute integral equals its mass."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitativeevenseed-normalizedEvenSeed-tsupport"),
                DeclarationHandle.Create(Prefix + "normalizedEvenSeed_tsupport"), H("Topological support is controlled"),
                StatementSource.FromAuthor(Disp(F.Id("tsupport(psi_h) is contained in [-h,h]."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the exact bump support and take closure in the closed interval. Boundary points are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitativeevenseed-fourierLaplace-sub-one-norm-le"),
                DeclarationHandle.Create(Prefix + "fourierLaplace_sub_one_norm_le"), H("A quantitative nonvanishing neighborhood"),
                StatementSource.FromAuthor(Disp(F.Id("Unit mass and unit L1 mass, support in [-h,h], h>=0 and h|z|<=1 imply |FT(psi)(z)-1|<=2h|z|."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Integrate the pointwise bound |exp(w)-1|<=2|w| for |w|<=1. The support certificate supplies |x|<=h. No unknown continuity radius is chosen."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitativeevenseed-quantitativeSeedRadius"),
                DeclarationHandle.Create(Prefix + "quantitativeSeedRadius"), H("An explicit arithmetic radius"),
                StatementSource.FromAuthor(Disp(F.Id("h(R)=1/(4(R+1))."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A rational bound R produces a rational radius."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitativeevenseed-quantitativeSeedRadius-pos"),
                DeclarationHandle.Create(Prefix + "quantitativeSeedRadius_pos"), H("Radius positivity"),
                StatementSource.FromAuthor(Disp(F.Id("R>=0 implies h(R)>0."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All denominator signs are proved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitativeevenseed-quantitativeEvenSeed-transform-lower"),
                DeclarationHandle.Create(Prefix + "quantitativeEvenSeed_transform_lower"), H("Uniform normalization denominator"),
                StatementSource.FromAuthor(Disp(F.Id("For R>=0 and |z|<=R, |FT(psi_(h(R)))(z)|>=1/2."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The transform differs from one by at most one half, and the reverse triangle inequality gives the denominator lower bound. Higher derivative seminorms are separate quantitative inputs."))), DescribeRole.Theorem)), []));
}
