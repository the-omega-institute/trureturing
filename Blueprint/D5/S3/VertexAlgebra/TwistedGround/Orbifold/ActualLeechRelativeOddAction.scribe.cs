using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class ActualLeechRelativeOddActionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualLeechRelativeOddAction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual fixed-sector C2 quotient acts on the negative twisted relative C2 quotient.",
        H("The Fixed-Sector Action on the Relative Twisted Quotient"),
        Blocks(
            Paragraph(Text("For lattice data D with unit Gram determinant, the negative twisted carrier is the "
                + "parity -1 subspace. Its relative C2 subspace is the complex span of the minus-two modes of "
                + "the corrected fixed-source field applied to negative twisted states.")),
            Entry("fixed-odd-higher-modes", "fixed_odd_mode_mem_relativeOddC2", "Higher negative modes",
                "Every fixed-source mode of index at most minus two sends the negative twisted carrier into "
                + "the relative C2 subspace. Translation reduces each successive mode to the preceding one "
                + "with the source translated and a nonzero scalar inverted."),
            Entry("relative-odd-quotient-action", "relativeOddQuotientAction", "Descent of the minus-one action",
                "The commutator identity gives preservation of the relative C2 subspace. The iterate identity "
                + "shows that fixed-sector C2 generators act trivially on the relative quotient. The resulting "
                + "complex-linear map takes fixed quotient classes to endomorphisms of the relative quotient.",
                DescribeRole.Definition),
            Entry("relative-odd-quotient-action-representatives", "relativeOddQuotientAction_mk",
                "Action on representatives",
                "The class of a fixed state acts on the class of a negative twisted state by taking the class "
                + "of the corrected minus-one mode applied to those representatives."),
            Entry("relative-odd-quotient-action-product", "relativeOddQuotientAction_product",
                "Compatibility with the fixed quotient product",
                "The action of a fixed minus-one product equals the composition of the two actions in product "
                + "order. In the Borcherds iterate, higher negative modes kill every term in the quotient "
                + "except the composition of the two minus-one modes."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
