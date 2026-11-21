using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class HuangLastCoordinateFoldDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/HuangLastCoordinateFold.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer channels of the last-coordinate Huang fold",
        H("Last-coordinate fold"),
        Blocks(
            Paragraph(Text(
                "The transverse row constraint applies to the 78-point component case in "
                + "Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, "
                + "arXiv:2610.09483v1, Section 7, Problem 2. Divisibility by four constrains "
                + "the signs of singleton layers, while the vanishing row at a positive axial "
                + "dimer supplies the exact equality against which to test those signs. "
                + "https://arxiv.org/html/2610.09483v1#Thmproblem2")),
            Describe.Lean(
                DescribeId.Create("huang-last-coordinate-flip"),
                DeclarationHandle.Create(Prefix + "lastFlip"),
                H("Last-coordinate reflection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a vertex x of Q(n + 1), T(x) flips the last bit of x. Applying T twice returns x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("huang-last-coordinate-transverse-action"),
                DeclarationHandle.Create(Prefix + "transverseAction"),
                H("Transverse Huang row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an integer vector on Q(n + 1), the transverse row B at x sums the "
                    + "signed contributions in the first n directions with the original Huang signs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("huang-last-coordinate-commutation"),
                DeclarationHandle.Create(Prefix + "last_flip_commutes"),
                H("Reflection commutes with the full Huang action"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sign of a direction depends only on the bits strictly before it. "
                    + "The proof follows the sign recursion to show that changing a bit at "
                    + "or after that direction preserves the sign. Since coordinate flips commute, "
                    + "the terms in A(f ∘ T)(x) and (Af)(T(x)) agree direction by direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("huang-last-coordinate-channels"),
                DeclarationHandle.Create(Prefix + "transverseAction_channels"),
                H("Transverse equations for the signed channels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let Af = λf for an integer vector f on Q(n + 1) and let s(x) be the sign of "
                    + "the last edge at x. Reflection preserves the eigenvalue. Set u = f + f ∘ T "
                    + "and v = f − f ∘ T. The involution fixes u and negates v, and both vectors "
                    + "remain integral. Subtracting the last-edge term from each full row gives "
                    + "(Bu)(x) = (λ − s(x))u(x) and (Bv)(x) = (λ + s(x))v(x)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("huang-q9-antisymmetric-row"),
                DeclarationHandle.Create(Prefix + "q9_antisymmetric_row"),
                H("Divisibility and vanishing on the nine-cube"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an integer 3-eigenvector of the unweighted Huang action on Q₉, a positive "
                    + "last edge gives (Bv)(x) = 4v(x), so the antisymmetric transverse row is divisible "
                    + "by four. If the two axial values agree, v(x) = 0 and the row vanishes for either "
                    + "last-edge sign."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang"))
        ]));
}
