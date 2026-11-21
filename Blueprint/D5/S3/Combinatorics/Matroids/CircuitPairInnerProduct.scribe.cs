using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class CircuitPairInnerProductDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/CircuitPairInnerProduct";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The union of two matroid circuits determines how their oriented lifts pair.",
        H("Inner products between matroid circuit summands"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("residual-circuits"),
                DeclarationHandle.Create(Module + ".residual_circuits"),
                H("Circuits in the two contractions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take two distinct finite circuits C and D on a totally ordered carrier. "
                    + "If their union has two more elements than its rank, the difference of D "
                    + "with C is a circuit after contracting C, and the difference of C with D "
                    + "is a circuit after contracting D. Deleting one vertex from each exclusive "
                    + "difference gives an independent spanning set of the union. This transports "
                    + "independence of each single deletion to the appropriate contraction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("circuit-pairing-zero"),
                DeclarationHandle.Create(Module + ".circuitPairing_eq_zero"),
                H("Orthogonality away from union nullity two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let C and D be distinct circuits of a matroid on a finite totally ordered "
                    + "carrier. Lift any augmented integral top cycle of each contraction by "
                    + "joining with the corresponding oriented circuit boundary. If the union "
                    + "of the circuits has nullity other than two, the ambient coordinate "
                    + "inner product of the two lifts is zero. A shared supporting basis would "
                    + "omit one vertex in each exclusive difference. A common omitted vertex "
                    + "would produce two fundamental circuits of the same basis and vertex."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("circuit-pairing-factor"),
                DeclarationHandle.Create(Module + ".circuitPairing_factor"),
                H("Integral pairing through contraction of the union"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For two distinct circuits C and D of a finite ordered matroid, write S "
                        + "for their intersection, P for the difference of C with D, and Q for "
                        + "the difference of D with C. Suppose their union has nullity two. "
                        + "Take augmented integral top cycles in the contractions by C and D. "
                        + "For the first cycle sum its signed restrictions along Q over every "
                        + "choice of a deleted vertex of Q. For the second use P in the same way. "
                        + "Both coordinate families vanish away from bases after contracting the union.")),
                    Paragraph(Text(
                        "The ambient inner product of the lifts equals the inner product of these "
                        + "two families times a fixed sign. Multiply the two signs for sorting "
                        + "S followed by P and S followed by Q, and multiply by minus one to the "
                        + "product of the sizes of P and Q each reduced by one. Shared bases are "
                        + "indexed by the two deleted vertices and a basis in the contraction of "
                        + "the union. The sign accounts for the interchange of the two ordered "
                        + "exclusive parts after the deletions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("circuit-pairing-rank"),
                DeclarationHandle.Create(Module + ".circuitPairing_rank"),
                H("Rank of the rational cross pairing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let two distinct circuits of a finite ordered matroid have union nullity "
                        + "two. Regard their ambient lift pairing as a rational linear map from "
                        + "the augmented top cycles in the first contraction into the dual of "
                        + "the augmented top cycles in the second. Its image dimension equals "
                        + "the rational augmented top-cycle dimension after contracting the union.")),
                    Paragraph(Text(
                        "Each sum of signed restrictions, composed with the corresponding "
                        + "residual-circuit lift, multiplies by the size of that circuit. "
                        + "The two sums are therefore surjective over the rationals. "
                        + "The coordinate dot product on the common target has trivial radical."))),
                DescribeRole.Theorem))));
}
