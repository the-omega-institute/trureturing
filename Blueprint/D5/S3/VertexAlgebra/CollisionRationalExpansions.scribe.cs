using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class CollisionRationalExpansionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/CollisionRationalExpansions.";
    private static readonly LibraryNoteRef LocalityBackground =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common labelled rational field embeds injectively into each complete supported order.",
        H("Ordered rational expansions and residue fibres"),
        Blocks(
            Paragraph(Text("Labelled polynomials are finite Laurent polynomials in every label. Additive exponent "
                + "equivalences transport them into the recursive lexicographic Hahn groups without dropping "
                + "spectators. The injective polynomial maps lift to actual fraction-field maps. Coefficients "
                + "are selected from these complete expansions, after division in the global rational field.")),
            Describe.Lean(
                DescribeId.Create("collisionrationalexpansions-orderedpolynomialfor-injective"),
                DeclarationHandle.Create(Prefix + "orderedPolynomialFor_injective"),
                H("Faithful polynomial and rational expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("Any finite permutation sigma gives an injective ordered polynomial map. Its fraction-field "
                        + "extension evaluates the same labelled rational expression in that order. Actual words are "
                        + "supported by their native field composition, rather than by a new support hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("collisionrationalexpansions-pullfiber-mul"),
                DeclarationHandle.Create(Prefix + "pullFiber_mul"),
                H("Supported coefficient fibres and scalar multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("An order-preserving insertion identifies the fixed z-exponent fibre with a supported Hahn "
                        + "series on the remaining coordinates. The support is derived from the original series "
                        + "support. Finite antidiagonal multiplication proves compatibility with remaining-variable "
                        + "scalars."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("collisionrationalexpansions-nonadjacent-spectator-factor-cancel"),
                DeclarationHandle.Create(Prefix + "nonadjacent_spectator_factor_cancel"),
                H("Nonadjacent spectator poles cancel in complete orders"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("Explicit inserted coordinates relate the two adjacent full orders. A spectator coordinate "
                        + "outside the adjacent position gives equal residue contributions in the two orders, including "
                        + "powers and arbitrary supported scalar coefficients. No spectator coefficient is extracted "
                        + "before the full rational expansion."))),
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
