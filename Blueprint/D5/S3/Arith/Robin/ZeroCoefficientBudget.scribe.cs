using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ZeroCoefficientBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ZeroCoefficientBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prescribed zero mass controls height multiplicities and the complete real response.",
        H("Absolute coefficient and height budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-coefficient-budget"),
                DeclarationHandle.Create(Prefix + "zero_coefficient_budget"),
                H("Summability, finite height counts, and real exponential growth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho index a countable family in the open critical strip, with multiplicity. "
                        + "Assume a permutation of the indices sends rho to its complex conjugate, "
                        + "every imaginary part has absolute value greater than 10, and the unordered "
                        + "sum of a_i=1/(rho_i*(1-rho_i)) is C=2+EulerGamma-log(4*pi).")),
                    Paragraph(Text(
                        "The coefficients are absolutely summable. Writing eta_i=Im(rho_i), "
                        + "their pointwise bounds are eta_i^(-2)<=2*Re(a_i) and |a_i|<=eta_i^(-2). "
                        + "Consequently sum eta_i^(-2)<=2*C<2 and sum |a_i|<2. "
                        + "For each T>0, the set of zero occurrences with |eta_i|<=T is finite "
                        + "and has cardinality at most 2*T^2.")),
                    Paragraph(Text(
                        "For every real y, Hc(y)=sum a_i*exp(rho_i*y) converges absolutely, "
                        + "is real, and equals the complex embedding of H(y)=Re(Hc(y)). "
                        + "The complete response satisfies |H(y)|<=2*exp(max(y,0)). "
                        + "All counts are counts of indices, so coincident zero values retain their multiplicity.")),
                    Paragraph(Text(
                        "The coefficient estimates follow from p=b*(1-b) in (0,1/4] and "
                        + "|rho*(1-rho)|^2=eta^4+eta^2*(1-2*p)+p^2. "
                        + "The prescribed mass then bounds the nonnegative inverse-height series. "
                        + "A summable positive constant on a height truncation forces that truncation to be finite. "
                        + "Conjugation invariance proves reality of the series. Mathlib supplies the "
                        + "EulerGamma<2/3, exp(1)<3, and pi>3 estimates used to bound C."))),
                DescribeRole.Theorem))));
}
