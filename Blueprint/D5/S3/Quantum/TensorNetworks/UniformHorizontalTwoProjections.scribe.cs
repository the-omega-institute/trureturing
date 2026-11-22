using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class UniformHorizontalTwoProjectionsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/UniformHorizontalTwoProjections";
    private const string Title = "Two projected resultants on the Laurent torus";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("uniformhorizontaltwoprojections-eq-monomial-of-projected-dvd-powers"),
                DeclarationHandle.Create(Module + ".eq_monomial_of_projected_dvd_powers"),
                H("The projections determine the support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If both projections of a nonzero bivariate polynomial divide powers of their retained variable, each exponent is constant on the support. The polynomial is a single monomial."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniformhorizontaltwoprojections-height-one-torus-prime-cannot-contain-pair"),
                DeclarationHandle.Create(Module + ".height_one_torus_prime_cannot_contain_pair"),
                H("Two projected Sylvester tests exclude a height-one prime"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A prime of height one containing both images would give a common prime divisor in the polynomial ring. The two nonzero fixed-degree resultants force that divisor to be a monomial, which becomes a unit on the torus."))),
                DescribeRole.Theorem))));
}
