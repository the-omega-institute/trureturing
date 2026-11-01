using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class GaussianCoefficientContinuityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientContinuity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "GaussianCoefficientContinuity", H("GaussianCoefficientContinuity"), Blocks(
            Paragraph(Text("A fixed finite Gaussian occupation coefficient is a finite polynomial in the entries of its kernel.")),
            N("coefficient_continuous","Finite polynomial dependence of ordinary coefficients","Each coefficient of Q_K is a finite linear combination of the kernel entries. The finite antidiagonal product formula shows inductively that every coefficient of Q_K^n is continuous in all entries. Multiplication by 1/n! gives continuity of the actual Gaussian coefficient at every finite occupation. No effective-kernel norm bound is needed.")), []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("gaussiancoefficientcontinuity-" + name.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
