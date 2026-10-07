using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OrderedCollisionCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/OrderedCollisionCoordinates.";
    private static readonly LibraryNoteRef LocalityBackground =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit finite order maps retain every pre/post label and prove the coefficientwise fused-residue square.",
        H("Complete adjacent coordinates and fused residue"),
        Blocks(
            Paragraph(Text("The complete orders are pre,z,x,post and pre,x,z,post. The equivalence tau enumerates every "
                + "label other than z; its entry at the pre boundary is x. Recursive additive exponent "
                + "equivalences encode both complete orders and the remaining order, with no finite exponent "
                + "cutoff.")),
            Describe.Lean(
                DescribeId.Create("orderedcollisioncoordinates-first-coefficient-square"),
                DeclarationHandle.Create(Prefix + "first_coefficient_square"),
                H("The first complete expansion agrees on remaining coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("The first exponent equivalence inserts z immediately before the boundary x. The second uses "
                        + "the full exponent equivalence with z after x. Order embeddings and their split inverses "
                        + "prove the actual coefficient-field squares and supported residue maps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orderedcollisioncoordinates-fused-residue-square"),
                DeclarationHandle.Create(Prefix + "fused_residue_square"),
                H("Full remaining expansion commutes with the u-residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("FusedLocalSeries expands the remaining rational coefficient field coefficientwise in its "
                        + "complete Hahn order before selecting the u=-1 coefficient. The equality with coefficientHahn "
                        + "applied to the rational localResidue is a proved coefficientwise seriesMap square, not an "
                        + "endpoint premise."))),
                DescribeRole.Theorem),
            Paragraph(Text("The algebraic proofs reuse mathlib Hahn/Laurent support, finite antidiagonal multiplication, "
                + "fraction-field lifts and polynomial partial fractions. LaurentSeries authors are Aaron "
                + "Anderson, María Inés de Frutos-Fernández and Filippo A. E. Nuccio; HahnSeries author is "
                + "Aaron Anderson; partial fractions authors are Kevin Buzzard, Sidharth Hariharan and Aaron "
                + "Liu. These sources carry Apache 2.0 licenses. Actual HVertexOperator and VertexOperator "
                + "composition are by Scott Carnahan, Apache 2.0. The imported FieldNormalProduct supplier "
                + "attributes its support/Hasse adaptation to ScottCarnahan/vertexAlg revision "
                + "4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0. The locality LibraryNote association "
                + "is background, not a claim that these new rational proofs are supplied by that paper.")),
            Paragraph(Text("Matsuo and Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1 provide "
                + "residue-product locality and reconstruction background. Their reconstruction requires "
                + "additional creative generators and a common translation operator. Carpi and Codogni, "
                + "arXiv:2605.26972v1, Conjecture 14.4 concerns all weights; Proposition 14.3 treats k<24. The "
                + "corrected coefficient is D(h,j)=j!(2h)_j; the faulty printed Equation 46 is unused here. No "
                + "proof of that conjecture, actual Moonshine/PCT, a fused-state energy law, "
                + "CFT/anomaly/fusion, string theory or AdS/CFT is asserted.")))));
}
