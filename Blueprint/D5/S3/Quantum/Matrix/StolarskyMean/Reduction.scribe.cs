using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.StolarskyMean;

internal sealed class ReductionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/StolarskyMean/Reduction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homogeneous Stolarsky profiles and logarithmic reconstruction.",
        H("Stolarsky logarithmic coordinates"), Blocks(
            Definition("psi", "The exponential profile", "Evaluate the Stolarsky mean on exp(-t) and exp(t). The definition includes all continuous parameter extensions and the value at zero."),
            Definition("f", "The second derivative defect", "Subtract the profile from its second ordinary real derivative. Derivatives are the total derivative operations supplied by Lean."),
            Theorem("stolarsky_symm", "Symmetry", "The Stolarsky mean is symmetric in its two arguments, at every real parameter and for the total real definition."),
            Theorem("stolarsky_homogeneous", "Positive homogeneity", "For positive a, b, and c, scaling both inputs by c scales the Stolarsky mean by c. This includes the logarithmic and identric branches."),
            Theorem("stolarsky_pos", "Positive entries", "For every parameter at least two, a positive pair has strictly positive Stolarsky mean. Strict monotonicity of real powers gives the sign of the divided difference."),
            Definition("profileKernel", "The homogeneous logarithmic kernel", "Multiply the profile at half the difference of the input logarithms by the product of the input square roots."),
            Theorem("stolarsky_eq_profileKernel", "Recovering the mean from its profile", "For positive inputs, every real Stolarsky parameter agrees with the homogeneous logarithmic kernel of its exponential profile."))));

    private static DocumentBlock Definition(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("stolarsky-reduction-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("stolarsky-reduction-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
