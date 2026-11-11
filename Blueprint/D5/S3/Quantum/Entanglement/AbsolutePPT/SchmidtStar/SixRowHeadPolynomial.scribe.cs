using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar;
internal sealed class SixRowHeadPolynomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integer polynomial is the exact residual after two squaring steps in the K6 head estimate. Homogeneous Bernstein rows evaluate nonnegatively when their natural-number coefficients and six interval coordinates are nonnegative. The constraint bound excludes only boxes on which the feasibility polynomial is strictly negative.", H("SixRowHeadPolynomial"), Blocks(
            Paragraph(Text("The integer polynomial is the exact residual after two squaring steps in the K6 head estimate. Homogeneous Bernstein rows evaluate nonnegatively when their natural-number coefficients and six interval coordinates are nonnegative. The constraint bound excludes only boxes on which the feasibility polynomial is strictly negative.")),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadpolynomial-p"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.P"),
                H("P"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def P (z k h : ℝ) : ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadpolynomial-numerator"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.numerator"),
                H("numerator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def numerator (z k h : ℝ) : ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadpolynomial-numerator-identity"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.numerator_identity"),
                H("numerator identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem numerator_identity (z k h : ℝ) : numerator z k h = 16*k*z^4*P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadpolynomial-row"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.row"),
                H("row"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def row (cs : List ℝ) (x y : ℝ) : ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadpolynomial-tensor"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.tensor"),
                H("tensor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def tensor (cs : List (List (List ℕ))) (z Z k K h H : ℝ) : ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadpolynomial-tensor-nonneg"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.tensor_nonneg"),
                H("tensor nonneg"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem tensor_nonneg (cs : List (List (List ℕ))) (z Z k K h H : ℝ) (hz : 0 ≤ z) (hZ : 0 ≤ Z) (hk : 0 ≤ k) (hK : 0 ≤ K) (hh : 0 ≤ h) (hH : 0 ≤ H) : 0 ≤ tensor cs z Z k K h H"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadpolynomial-constraint"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.constraint"),
                H("constraint"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def constraint (z k h : ℝ) : ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadpolynomial-constraint-upper"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial.constraint_upper"),
                H("constraint upper"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem constraint_upper (z k h a b c : ℝ) (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1) (hk : 0 ≤ k) (hkb : k ≤ b) (hh : 0 ≤ h) (hhc : h ≤ c) : constraint z k h ≤ constraint a b c"))), DescribeRole.Theorem)
        )));
}
