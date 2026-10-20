using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.StolarskyMean;

internal sealed class ReductionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/StolarskyMean/Reduction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homogeneous Stolarsky profiles, their mixed derivatives, and logarithmic kernel positivity.",
        H("Stolarsky logarithmic coordinates"), Blocks(
            Definition("psi", "The exponential profile", "Evaluate the Stolarsky mean on exp(-t) and exp(t). The definition includes all continuous parameter extensions and the value at zero."),
            Definition("f", "The second derivative defect", "Subtract the profile from its second ordinary real derivative. Derivatives are the total derivative operations supplied by Lean."),
            Theorem("stolarsky_symm", "Symmetry", "The Stolarsky mean is symmetric in its two arguments, at every real parameter and for the total real definition."),
            Theorem("stolarsky_homogeneous", "Positive homogeneity", "For positive a, b, and c, scaling both inputs by c scales the Stolarsky mean by c. This includes the logarithmic and identric branches."),
            Theorem("stolarsky_pos", "Positive entries", "For every parameter at least two, a positive pair has strictly positive Stolarsky mean. Strict monotonicity of real powers gives the sign of the divided difference."),
            Theorem("stolarsky_two", "The arithmetic boundary", "At parameter two, the total Stolarsky mean is the arithmetic mean."),
            Theorem("conditionallyNegative_two", "Conditional negativity at two", "The quadratic form of an arithmetic mean matrix vanishes on every real vector whose coordinates sum to zero."),
            Theorem("inClassA_two", "Class A at two", "Every nonempty positive family has a class A mean matrix at parameter two. Conditional negativity bounds the number of positive eigenvalues, and the positive diagonal supplies one."),
            Definition("profileKernel", "The homogeneous logarithmic kernel", "Multiply the profile at half the difference of the input logarithms by the product of the input square roots."),
            Theorem("stolarsky_eq_profileKernel", "Recovering the mean from its profile", "For positive inputs, every real Stolarsky parameter agrees with the homogeneous logarithmic kernel of its exponential profile."),
            Theorem("logarithmic_pullback_nonneg", "A weighted positive kernel", "If a real function is positive definite after scalar extension to the complex numbers, every finite quadratic form of its logarithmic pullback with the square-root diagonal weights is nonnegative. The argument uses the frozen finite complex Gram definition and real coefficient vectors."))));

    private static DocumentBlock Definition(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("stolarsky-reduction-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("stolarsky-reduction-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
