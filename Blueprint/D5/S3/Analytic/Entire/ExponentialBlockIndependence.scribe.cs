using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Entire;

internal sealed class ExponentialBlockIndependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent exponential-polynomial blocks.",
        H("Independent exponential-polynomial blocks"),
        Blocks(Describe.Lean(DescribeId.Create("distinct-entire-exponential-blocks"),
            DeclarationHandle.Create("D5/S3/Analytic/Entire/ExponentialBlockIndependence.block_evaluation_injective"),
            H("Independent exponential-polynomial blocks"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every finite index type and injective family of arbitrary complex exponents, the complex-linear map sending a tuple of polynomials to the sum exp(alpha_i*z)*P_i(z) is injective on the whole complex plane. Polynomial degrees and coefficients are unrestricted.")),
                Paragraph(Text("The actual scalar derivative minus alpha maps an exponential block to the corresponding polynomial derivative. Each block therefore belongs to the generalized eigenspace of the actual entire derivative at alpha. Independence of generalized eigenspaces for distinct eigenvalues proves that no nonzero polynomial block can cancel another exponent block.")),
                Paragraph(Text("A finite exponential-polynomial presentation is regrouped by its actual exponents, with exactly zero polynomial blocks removed. An algebraic left inverse of the injective evaluation map gives block projections on all complex-valued functions. Their weighted-kernel identities select one exponent in either variable, including when the candidate separated factors are arbitrary entire functions. These projections are consumed in the distinct-block rank obstruction."))),
            DescribeRole.Theorem))));
}

