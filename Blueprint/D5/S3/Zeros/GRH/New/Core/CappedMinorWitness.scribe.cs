using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Core;

internal sealed class CappedMinorWitnessDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Zeros/GRH/New/Core/CappedMinorWitness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral column factorization and low-rank corrections",
        H("Integral column factorization and low-rank corrections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-minor-integral-column-factorization"),
                DeclarationHandle.Create(Module + "exists_maximal_minor_factorization"),
                H("A full minor generates the column module"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over a valuation domain, a matrix with a nonzero full column minor admits "
                    + "an integral factorization through one selected full minor. The universal determinant "
                    + "divisibility applies to each Cramer numerator. Cancelling the nonzero determinant "
                    + "gives the integral coordinates of all columns."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("capped-minor-divides-low-rank-correction-budget"),
                DeclarationHandle.Create(Module + "exists_capped_minor_dvd_of_low_rank_correction"),
                H("A capped full minor from a low-rank correction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose that A times X plus B times C equals a times a square matrix with unit "
                    + "determinant. If B has r columns and A has c rows and columns, a nonzero full minor "
                    + "of the horizontal concatenation of A and z times the identity has determinant "
                    + "dividing a to the power c times z to the power r. Here z is nonzero. "
                    + "A triangular block elimination computes the corresponding determinant, and the "
                    + "integral factorization of the concatenation exhibits the selected determinant as a divisor."))),
                DescribeRole.Theorem))));
}
