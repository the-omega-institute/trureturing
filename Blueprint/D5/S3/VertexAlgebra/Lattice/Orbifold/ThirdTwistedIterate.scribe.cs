using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdTwistedIterateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedIterate.";
    private static readonly LibraryNoteRef TwistedProducts =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native lattice current minus-one product has the fractional Virasoro modes under an explicit twisted iterate premise.",
        H("The Third-Cover Comparison from the Twisted Iterate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("third-twisted-iterate-pair-premise"),
                DeclarationHandle.Create(Prefix + "pairIterate"),
                H("Coefficientwise twisted iterate premise"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedProducts),
                Blocks(Paragraph(Text("Use Bakalov and Kac, arXiv:math/0402315v3, equation (3.13), at "
                    + "n = −1 with first frequency grid 1/3. For every integer m and complement polynomial, "
                    + "take the sign-ordered finsum of products of the supplied modes over indices k "
                    + "in residue one with partner index 3m − k. This equals the finsum over j ≥ 0 "
                    + "of Ring.choose (1/3) j "
                    + "times the twisted mode of the native (j−1)-product. The shift z^(-j) "
                    + "selects native index 3(m + 1 − j) in that mode."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-twisted-iterate-fractional-virasoro"),
                DeclarationHandle.Create(Prefix + "fractionalVirasoro_of_twistedIterate"),
                H("Fractional modes of the native quadratic state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedProducts),
                Blocks(Paragraph(Text("Take the two native current states from ConformalGroundTransport.current "
                    + "and assume their complex bilinear Gram pairing is one. The supplied complex-linear map "
                    + "must restrict to the normalized fractional currents on residues one and two "
                    + "respectively, vanish off each of those grids, "
                    + "send the vacuum to the identity at native index −3 and zero elsewhere, "
                    + "and satisfy the coefficientwise iterate on this pair. At index 3(m + 1), "
                    + "the twisted mode of the actual native (−1)-product is fractionalVirasoro(m). "
                    + "The basis products from FullJacobiCurrentTransport.source_current_product extend "
                    + "bilinearly. The iterate retains the native (−1)-product at j = 0 and the vacuum contraction at j = 2. "
                    + "The latter contributes −1/9 at m = 0 on the iterate side."))),
                DescribeRole.Theorem))));
}
