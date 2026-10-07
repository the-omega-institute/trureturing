using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OrderedCollisionResiduesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/OrderedCollisionResidues.";
    private static readonly LibraryNoteRef LocalityBackground =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every term of the derived rational normal form satisfies the complete adjacent-order collision.",
        H("Diagonal residues and spectator cancellation"),
        Blocks(
            Paragraph(Text("All maps act on the already divided global rational function. The diagonal and nonadjacent "
                + "spectator terms are proved separately in the full supported orders, and then combined by "
                + "additive residue maps. The same tau boundary condition identifies the actual x label in both "
                + "orders.")),
            Describe.Lean(
                DescribeId.Create("orderedcollisionresidues-actual-spectator-pole-cancel"),
                DeclarationHandle.Create(Prefix + "actual_spectator_pole_cancel"),
                H("Actual nonadjacent labelled poles cancel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("Explicit basis images connect each z-s difference to the supported spectator-pole kernel. "
                        + "The nonadjacent coordinate condition s!=x makes the two residue fibres agree for arbitrary "
                        + "rational spectator coefficients and finite pole powers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orderedcollisionresidues-coefficient-diagonal-collision"),
                DeclarationHandle.Create(Prefix + "coefficient_diagonal_collision"),
                H("The oriented diagonal has its local residue jump"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("The actual global z and x images are computed in both full orders. Their difference is the "
                        + "original oriented diagonal. The contextual Laurent kernel proves every integer power, and "
                        + "scalar multiplication transports arbitrary rational remaining coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("orderedcollisionresidues-polynomial-collision"),
                DeclarationHandle.Create(Prefix + "polynomial_collision"),
                H("The regular polynomial part has zero residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("A nonnegative z-power has no z=-1 coefficient in either complete expansion and no u=-1 "
                        + "coefficient after translation. Polynomial induction proves the same for the entire "
                        + "polynomial part. These results and linearity discharge all normal-form terms without a "
                        + "compatibility assumption."))),
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
