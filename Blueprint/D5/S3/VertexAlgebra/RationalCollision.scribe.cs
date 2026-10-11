using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class RationalCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/RationalCollision.";
    private static readonly LibraryNoteRef LocalityBackground =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete rational collision holds for every integer weight and every remaining labelled exponent.",
        H("Full fixed-denominator rational collision"),
        Blocks(
            Paragraph(Text("Over any field K, take arbitrary finite pre/post blocks, z, tau, x with tau(pre)=x, a finite "
                + "labelled Laurent numerator P whose z exponents are nonnegative, and the exact fixed-label Q "
                + "of order k. Divide P by Q in the common rational field. Expand in the two complete orders "
                + "before selecting the supported z=-1 fibres.")),
            Describe.Lean(
                DescribeId.Create("rationalcollision-full-collision-series"),
                DeclarationHandle.Create(Prefix + "full_collision_series"),
                H("Assemble the collision without a decomposition premise"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("The oriented finite partial-fraction normal form is derived from the actual weighted P/Q. "
                        + "Polynomial residue zero, the all-integer diagonal kernel and spectator cancellation prove "
                        + "each term. Additive residue maps assemble equality of entire supported Hahn series on every "
                        + "remaining label."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rationalcollision-required-proved"),
                DeclarationHandle.Create(Prefix + "required_proved"),
                H("All integer weights and all remaining labelled coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("The theorem discharges the full CollisionStatement with no assumed collision, support "
                        + "certificate or compatibility law. It quantifies r in Int and every function from Remaining z "
                        + "to Int. Negative remaining exponents and arbitrary spectators are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rationalcollision-complete-expansion-collision"),
                DeclarationHandle.Create(Prefix + "complete_expansion_collision"),
                H("Expand the fused local rational before taking residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(
                    Paragraph(Text("The fused-residue square identifies the u=-1 coefficient of the complete remaining expansion "
                        + "with the local rational residue. It equals the difference of the two complete supported z=-1 "
                        + "fibres of (z-x)^r P/Q. This is a rational collision theorem; fusedLocalSeries is not an "
                        + "identified state iterate."))),
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
