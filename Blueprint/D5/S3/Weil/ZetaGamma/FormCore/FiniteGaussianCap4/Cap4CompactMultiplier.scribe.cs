using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4;

internal sealed class Cap4CompactMultiplierDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4CompactMultiplier.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed compact multiplier bounds",
        H("Signed compact multiplier bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cap4-compact-debit-bound"),
                DeclarationHandle.Create(Owner + "compactDebit_abs_le_four"),
                H("Uniform control of the signed correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Define C(x)=(x/pi)^(5/2)-4*(x/pi)^(-7/2) for x>pi, and zero otherwise. Define B(x)=x^2/10-C(x) for 0<x<6, and zero otherwise. For every real x, |B(x)|<=4, including both endpoints and negative x.")),
                    Paragraph(Text("The proof bounds sqrt(x/pi) and its reciprocal power on the annulus 1<=x/pi<=2, together with 9<=pi^2<=10. It controls both signs of B; no sampled or unsigned substitute is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cap4-global-multiplier-domination"),
                DeclarationHandle.Create(Owner + "capWeight_ge_quadratic_minus_compact"),
                H("Domination on the whole nonnegative half-line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real x>=0, x^2/10-B(x)<=C(x). Inside the correction interval this is exact. At x=0 the definitions give equality; for x>=6 a separate power comparison proves the inequality without compact truncation of the domain.")),
                    Paragraph(Text("These are repository-derived pointwise analytic estimates using existing real-power and pi bounds. They supply multiplier control only; the physical source graph, matrix enclosures, and final quotient require separate proofs."))),
                DescribeRole.Theorem))));
}
