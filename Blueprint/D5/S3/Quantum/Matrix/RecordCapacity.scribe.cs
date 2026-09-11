using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class RecordCapacityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/RecordCapacity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonzero equivariant idempotent resolutions have bounded size: the commutant "
            + "dimension always bounds them, and a supplied matrix-block decomposition "
            + "improves this to the sum of the block sizes.",
        H("Conditional Record Capacity"),
        Blocks(
            Paragraph(Text(
                "A common finite complex matrix action U and equivariance of all records "
                    + "are explicit physical inputs. The statements do not impose a bound "
                    + "on arbitrary record structures. Self-adjoint records are included: "
                    + "the counting argument needs only nonzero idempotents summing to identity. "
                    + "No irreducible decomposition is inferred from the physical setup.")),
            Result("range-budget", "sum_range_finrank_of_idempotent_sum",
                "The ranges exhaust the dimension budget",
                "The trace of each idempotent is its range dimension. Summing and using "
                    + "the identity resolution gives the dimension of the carrier. "
                    + "The scalar field may be any field of characteristic zero.", true),
            Result("carrier-bound", "card_le_finrank_of_idempotent_sum",
                "Each nonzero record consumes a dimension",
                "A zero range dimension would make the trace and hence the idempotent "
                    + "zero. Summing the positive integer range dimensions bounds the count."),
            Result("algebra-bound", "algebra_card_le_finrank",
                "The dimension of a complex algebra bounds its resolutions",
                "Left multiplication represents the algebra faithfully on itself. "
                    + "The preceding count therefore applies in its complex dimension."),
            Result("commutant-bound", "equivariant_record_card_le_commutant_finrank",
                "The commutant bounds equivariant records",
                "Equivariance places each record in the actual centralizer of the common "
                    + "action. Its left regular action gives the bound by its complex dimension. "
                    + "This is weaker than the multiplicity-sum law in general."),
            Result("block-bound", "matrix_blocks_card_le_sum",
                "Matrix blocks give the sum of their sizes",
                "The product of matrix algebras acts faithfully by block diagonal matrices "
                    + "on a carrier whose dimension is the sum of the block sizes. "
                    + "The count applies on this smaller carrier."),
            Result("equivariant-block-bound", "equivariant_record_card_le_sum",
                "A supplied commutant decomposition gives the sharp bound",
                "The algebra equivalence is an explicit hypothesis linking the actual "
                    + "commutant to the stated blocks. Transport each record through it "
                    + "and apply the block count. Identifying these sizes with multiplicities "
                    + "of a separately specified irrep decomposition is not formalized here."),
            Result("semisimple-capacity", "semisimple_commutant_has_record_capacity",
                "Semisimplicity supplies one bound for all resolutions",
                "The upstream Wedderburn–Artin theorem supplies block sizes for a "
                    + "semisimple commutant. Those same sizes bound every finite nonzero "
                    + "equivariant orthogonal resolution. Semisimplicity is an assumption."))));

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, bool literature = false) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.WithoutFormula(),
            literature
                ? AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/mathlib2026recordcapacity"))
                : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
