using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianFixedExternalCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalGaussianFixedExternalCoefficient", H("Fixed external coefficients of the original sewn Gaussian"), Blocks(
            Paragraph(Text("The actual mixed occupation summands are differentiated in both external families at their full degrees. Summable Cauchy bounds on each fixed-cutoff source germ justify extraction through the occupation sum. The resulting terms are the literal full native rows, including the full opposite-charge inverse colour transport and exactly one internal factorial. Their source powers are twice the internal energy. Local uniform source differentiation then identifies the finite sewn coefficient with the finite energy layer. The fixed-cutoff normal germ is distinct from the common holomorphic domain used for the explicit sewn cutoff limit. No uniform lower bound for occupation radii is used. Empty supports, rank zero, cutoff zero and energy zero remain included.")),
            N("fullRowTerm", "Actual full sewn row summand", "The damped full row coefficients retain all external degrees and one internal factorial.", DescribeRole.Definition),
            N("rawFullRowTerm", "Undamped original full rows", "The right row uses the complete inverse colour transport of the original opposite-charge mean.", DescribeRole.Definition),
            N("original_fixed_external_sewing_on_germ", "Normally sewn full external occupations", "The two ordinary external extractions pass through the actual normally convergent occupation sum. The resulting uniform majorant belongs only to one positive fixed-cutoff germ.", DescribeRole.Theorem),
            N("original_finiteSewn_coefficient", "Finite sewn ordinary energy coefficient", "After justified external extraction and source differentiation, the coefficient of order twice the energy, divided by its full factorial, is exactly the original native full-row energy layer.", DescribeRole.Theorem)), []));

    private static DocumentBlock N(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("original-fixed-external-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
