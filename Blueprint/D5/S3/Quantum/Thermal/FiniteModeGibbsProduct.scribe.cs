using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class FiniteModeGibbsProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct unbounded occupation numbers for any finite list of modes and derive the infinite partition product and nuclear Gibbs expansion.",
        H("Finite Mode Gibbs Product on Infinite Occupation Space"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("totalweight-cons"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/FiniteModeGibbsProduct.totalWeight_cons"),
                H("totalWeight cons"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Factorization is proved from the actual additive energy and the exponential addition identity."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-modes-hassum"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/FiniteModeGibbsProduct.finite_modes_hasSum"),
                H("finite modes hasSum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction over the list of positive frequencies uses absolute summability to justify products of infinite sums. Each occupation number remains unbounded."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-modes-absolute-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/FiniteModeGibbsProduct.finite_modes_absolute_sum"),
                H("finite modes absolute sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derived positive Gibbs weights are absolutely summable as complex coefficients."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finitemodegibbs-nuclear"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/FiniteModeGibbsProduct.finiteModeGibbs_nuclear"),
                H("finiteModeGibbs nuclear"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The summands are actual bounded rank-one operators on the full occupation Hilbert space; both their sum and absolute operator-norm summability are established in the source."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finitemodegibbs-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/FiniteModeGibbsProduct.finiteModeGibbs_trace"),
                H("finiteModeGibbs trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The canonical occupation-basis trace equals the product of one-mode partition functions. A general metaplectic conjugation to a differential operator is not claimed."))), DescribeRole.Theorem))));
}
