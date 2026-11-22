using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class ActualLeechExtensionC2Document : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechExtensionC2.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The product of the fixed and relative twisted quotients surjects onto the actual extension quotient.",
        H("The C2 Quotient Comparison for the Actual Extension"),
        Blocks(
            Paragraph(Text("The inputs are lattice data D, a proof that det(D.G) is a unit, and a proof that the Gram "
                + "matrix is positive definite over the reals. The carrier of the assembled field is the product of "
                + "the fixed lattice sector and the negative twisted parity sector.")),
            Entry("relative-odd-c2", "relativeOddC2", "The relative twisted subspace",
                "Take the complex span of the minus-two coefficients of the actual fixed-source field acting on "
                + "negative twisted states.",
                DescribeRole.Definition),
            Entry("extension-c2", "extensionC2", "The extension C2 subspace",
                "Take the complex span of the minus-two products of arbitrary pairs of states of the assembled carrier.",
                DescribeRole.Definition),
            Entry("extension-c2-comparison", "quotientComparison", "The comparison map",
                "The two sector inclusions followed by the extension quotient map kill the respective C2 subspaces. "
                + "The descended linear maps give a map from the product of the fixed quotient and relative twisted quotient.",
                DescribeRole.Definition),
            Entry("extension-c2-comparison-pair", "quotientComparison_mk", "The comparison on representatives",
                "The pair of quotient classes maps to the extension quotient class of the corresponding paired state."),
            Entry("extension-c2-comparison-surjection", "quotientComparison_surjective", "Surjectivity",
                "Choose a representative of an arbitrary extension quotient class. The quotient classes of its two "
                + "coordinates map to the original class."),
            Entry("leech-extension-c2-comparison-surjection", "leechQuotientComparison_surjective",
                "Surjectivity for the Leech extension",
                "Specialize the comparison to the chosen positive-definite unimodular Leech lattice."),
            Entry("leech-extension-c2-from-relative-finite", "leech_extension_c2_cofinite_of_relative_odd_finite",
                "Finite dimensionality from the relative quotient",
                "For the chosen Leech data, the comparison uses the fixed-sector theorem "
                + "leech_fixed_c2_cofinite. Given finite dimensionality of the negative twisted relative quotient "
                + "over the complex numbers, finite dimensionality of the full extension quotient follows."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
