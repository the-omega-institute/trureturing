using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class CoefficientNewtonSumsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial Newton interface foundations: uniqueness, Vieta, and counted roots.",
        H("Coefficient Newton Foundations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("newton-recursion-unique"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Moments/CoefficientNewtonSums.newton_sum_unique"),
                H("Uniqueness of the coefficient recursion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Strong induction identifies any sequence satisfying the initial value "
                    + "and the Newton recurrence with the recursively defined sequence, "
                    + "over an arbitrary commutative ring. Identification with polynomial "
                    + "root sums and the Hermite parity block identity remain unproved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("vieta-zero-tail"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Moments/CoefficientNewtonSums.descending_coeff_eq_root_esymm"),
                H("Vieta including the zero coefficient tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a monic polynomial of the stated degree, a root list whose multiset "
                    + "equals the polynomial roots determines every descending coefficient. "
                    + "The equality includes coefficients beyond the degree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("counted-complex-root-list"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Moments/CoefficientNewtonSums.exists_root_enumeration"),
                H("Enumeration retains multiplicities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The list is obtained from the polynomial root multiset, with length "
                    + "equal to the degree because complex polynomials split. No distinct-root "
                    + "set replaces the multiset. Complete Hermite and truncated Hankel matrices "
                    + "have separate structure types. No FFC positivity assertion is made."))),
                DescribeRole.Theorem))));
}
