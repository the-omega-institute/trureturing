using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Icosahedral;

internal sealed class ExteriorSquareCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Icosahedral/ExteriorSquareCoordinates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit centered coordinates transport the A5 action to its real exterior square.",
        H("Coordinates for the Icosahedral Exterior Square"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("centered-coordinate-permutation-representation"),
                DeclarationHandle.Create(Prefix + "coordinatePermutationRepresentation"),
                H("The alternating group permutes the five coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The alternating group acts by inverse coordinate permutation on real "
                    + "five-space, preserving the centered hyperplane."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("centered-exterior-square-coordinate-equivalence"),
                DeclarationHandle.Create(Prefix + "exteriorSquareCoordinateEquiv"),
                H("Wedge coordinates transport the exterior-square representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An explicit centered basis and its six wedge pairs identify the second "
                    + "exterior power with real six-space equivariantly."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("hodge-endomorphism-on-wedge-coordinates"),
                DeclarationHandle.Create(Prefix + "hodgeEndomorphism"),
                H("The Hodge matrix defines a real endomorphism"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The repository's existing integral Hodge matrix acts on the transported "
                    + "six-dimensional coordinate space."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("coordinate-exterior-action-matrix"),
                DeclarationHandle.Create(Prefix + "coordinateExteriorSquare_apply"),
                H("The transported exterior action is the explicit real matrix action"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("rho"), Open, F.Id("g"), Close, Sp, Eq, Sp,
                    F.Id("mulVecLin"), Open, F.Id("A"), Open, F.Id("g"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On every wedge basis vector, the transported A5 action agrees with the "
                    + "real cast of the integral matrix of two-by-two minors."))),
                DescribeRole.Lemma
            )),
        []));
}
