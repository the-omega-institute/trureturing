using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class UniformPerturbationEuclideanDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/UniformPerturbationEuclidean";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Euclidean norm of the scaled coefficients controls near-collision probability.",
        H("Short Affine Bands under Independent Uniform Perturbations"),
        Blocks(
            Paragraph(Text(
                "Let J be finite. Each coordinate x(j) is independently uniform on [−r(j),r(j)] "
                + "with r(j)>0. For real a(j) and b set c(j)=a(j)r(j), and let S>0 be the sum "
                + "of c(j)². For η≥0 write P(η) for the probability of "
                + "|Σ a(j)x(j)+b|≤η. Write B(η)=exp(1/2)√(15π/2)η/√S.")),
            Describe.Lean(
                DescribeId.Create("interval-noise-pi-affine-le-euclidean"),
                DeclarationHandle.Create(Owner + ".intervalNoise_pi_affine_le_euclidean"),
                H("An interval probability bound with Euclidean scaling"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fubini factors the characteristic function of the sum into "
                        + "sinc(c(j)t). When the fourth-power sum is at most S²/2, the "
                        + "reciprocal quadratic envelope with coefficient S/15 controls "
                        + "the modulus. The Gaussian window bound applies at center −b "
                        + "on the law of the same sum, and yields B(η).")),
                    Paragraph(Text(
                        "If the fourth-power condition fails, at least one c(j)² exceeds S/2. "
                        + "Conditioning on the other coordinates gives the interval length ratio "
                        + "η/|c(j)|, bounded by √2η/√S. At zero resolution use the "
                        + "same conditioning argument with any nonzero coefficient. "
                        + "The probability is also bounded by one.")),
                    Paragraph(Text(
                        "This estimate concerns the product law on the admitted intervals. "
                        + "The center shift leaves the coefficient scale unchanged. "
                        + "In a collision test the coefficients are the differences "
                        + "of the degree vectors and the perturbation coordinates are shared."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bound()
    {
        var eta = F.Id("eta");
        return Disp(new Formula.Relation(Call("P", eta), FormulaRelationOperator.LessThanOrEqual,
            Call("min", D(1), Call("B", eta))));
    }
}
