using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalReindexCodesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Birth-local first-reservation codes and cofinal hole colors", H("Birth-local reservation coding"), Blocks(
            Paragraph(Text("Tags consist of all ordinary labels and precisely the delayed triples valid on one whole birth pack. The code uses the fixed ordinal reservation bijection and this birth alone. It does not consult a later history state. Ordinary zero remains zero; every other tag uses its first syntactically valid reservation. The second reservation supplies cofinal colors for the labels omitted by the code image.")),
            Describe.Lean(DescribeId.Create("task-syntax-injective"),
                DeclarationHandle.Create(Owner + "taskSyntax_injective"), H("Distinct tags have distinct task syntax"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Ordinary labels and intrinsically valid delayed triples have distinct fixed task reservations. The validity proof in a delayed tag does not distinguish tags with the same triple."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("occurs-cofinal"),
                DeclarationHandle.Create(Owner + "occurs_cofinal"), H("Every tag has cofinal valid reservations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For any fixed birth row, intrinsic tag and ordinal bound, a later reservation has that tag and meets all ordinary or delayed domain inequalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("code-zero"),
                DeclarationHandle.Create(Owner + "code_zero"), H("Ordinary zero retains zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The distinguished ordinary label zero has code zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("code-occurs"),
                DeclarationHandle.Create(Owner + "code_occurs"), H("Nonzero codes are valid occurrences"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every tag other than ordinary zero is coded by a reservation of its exact syntax satisfying the original stage domain conditions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("row-le-code"),
                DeclarationHandle.Create(Owner + "row_le_code"), H("The birth row precedes every nonzero code"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A nonzero tag code is at least its birth row, hence has positive ordinal value."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("target-le-code"),
                DeclarationHandle.Create(Owner + "target_le_code"), H("Original measure labels precede their codes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For an ordinary tag the original measure label is its ordinary label. For a delayed tag it is the target label. Each is at most the new code."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("code-le-occurrence"),
                DeclarationHandle.Create(Owner + "code_le_occurrence"), H("The first code precedes every occurrence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every syntactically matching valid reservation lies at or above the code. Ordinary zero satisfies the same bound because its code is zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("code-eq-zero-iff"),
                DeclarationHandle.Create(Owner + "code_eq_zero_iff"), H("Only ordinary zero has code zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Positive birth-row bounds separate every other tag code from zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("code-injective"),
                DeclarationHandle.Create(Owner + "code_injective"), H("Tag coding is injective"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Equality of two nonzero codes forces equality of the unique task syntax reserved there. The zero case is separated by the birth-row bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("double-reservation-cofinal"),
                DeclarationHandle.Create(Owner + "double_reservation_cofinal"), H("Two nested reservation tasks are cofinal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Given two tasks and any bound, there is a later stage whose first reservation task is the outer task and whose residual ordinal has the inner task. The nested inverse reservation map is injective; a bound would inject all countable ordinals into a countable initial segment."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordinary-index-le"),
                DeclarationHandle.Create(Owner + "ordinaryIndex_le"), H("Colored ordinary indices stay within the stage"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("An ordinary zero event uses its second reservation color only when that color lies within the stage and is zero or outside the code image. Other ordinary labels use their first codes. Every valid ordinary occurrence therefore receives an index at most its stage."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hole-cofinal"),
                DeclarationHandle.Create(Owner + "hole_cofinal"), H("Every hole and zero occurs cofinally"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every label outside the code image, and also for zero, there are cofinally many valid ordinary zero reservations above both the row and the label whose ordinary index equals that label. The two nested reservation tasks prescribe the row event and its color independently."))), DescribeRole.Theorem))));
}
