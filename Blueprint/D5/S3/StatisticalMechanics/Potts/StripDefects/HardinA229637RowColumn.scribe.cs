using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefects;

internal sealed class HardinA229637RowColumnDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229637RowColumn.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229637");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first column of A229637 vanishes, and its first row is C(k−1,2)2^(k−4) with a sharp "
            + "order-three recurrence.",
        H("A229637: the first column and the first row"),
        Blocks(
            Describe.Lean(DescribeId.Create("a229637-horizontal-bonds"),
                DeclarationHandle.Create(Prefix + "horiz"),
                H("Horizontal bonds of a row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "horiz k is the set of column pairs (j, j+1) of a row of width k; a pair whose "
                    + "two cells carry the same colour is a horizontal mistake."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a229637-between-bonds"),
                DeclarationHandle.Create(Prefix + "betw"),
                H("Diagonal and antidiagonal bonds between rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "betw k is the set of column pairs (j, j+1) and (j+1, j) joining a cell of a row "
                    + "to the diagonal and antidiagonal cells of the next row."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a229637-table"),
                DeclarationHandle.Create(Prefix + "T"),
                H("The table T(n,k)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "T(n,k) counts the n × k arrays over {0,1,2} whose defect count, with the "
                    + "horizontal bonds inside rows and the diagonal and antidiagonal bonds "
                    + "between consecutive rows, is exactly 2, and whose colours are introduced "
                    + "in row-major order. It uses the same defect and canonical predicates as "
                    + "the width-5 column A229634."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a229637-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The first column and the first row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The claim collects: T(n,1) = 0 for every n; T(1,1) = T(1,2) = 0 and T(1,3) = 1; "
                    + "T(1,k) = C(k−1,2)·2^(k−4) for k ≥ 4; the recurrence "
                    + "T(1,k) = 6T(1,k−1) − 12T(1,k−2) + 8T(1,k−3) for k ≥ 7, with residual −4 at "
                    + "k = 6; and no recurrence of order at most two with rational coefficients "
                    + "holds for all large k. OEIS records the column and row recurrences as "
                    + "empirical and identifies the row with A052482(k−2); the residual at k = 6 "
                    + "and the exclusion of order-two recurrences are added here."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a229637-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Proof of the first column and row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A single column has no horizontal, diagonal or antidiagonal neighbours, so "
                    + "no array has a mistake and T(n,1) = 0. A single row is a word starting "
                    + "with 0 in which each colour first appears after the previous one, and its "
                    + "mistakes are its equal adjacent letters. Appending a letter to such a word "
                    + "w gives one extension repeating the last letter and, among the other "
                    + "colours, two admissible ones unless w is constant, when only the colour 1 "
                    + "is admissible. So the number c(L,m) of such words of length L with m "
                    + "equal adjacencies obeys c(L+2,m) + [L = m] = c(L+1,m−1) + 2c(L+1,m), "
                    + "giving c(L,0) = 2^(L−2), c(L,1) = (L−1)2^(L−3) and "
                    + "c(L,2) = C(L−1,2)·2^(L−4). The recurrence and the residual follow from "
                    + "the closed form. An order-two recurrence would make "
                    + "4(k−1)(k−2) − 2c₁(k−2)(k−3) − c₂(k−3)(k−4) vanish at three consecutive "
                    + "k, and the combination of these equations whose quadratic and linear parts "
                    + "cancel gives 8 = 0."))),
                DescribeRole.Theorem))));
}
