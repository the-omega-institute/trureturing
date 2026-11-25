using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class OrderedSlaterSaturatingBasisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank test for attaining the ordered Slater purity-drop bound.",
        H("Existence of an attaining column basis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordered-marginal-exists-saturating-basis"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fermionic/OrderedSlaterSaturatingBasis.orderedMarginal_exists_saturating_basis_iff"),
                H("Rank criterion for an attaining column basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Balance one retained pair while holding every other endpoint probability fixed. " +
                    "At each of the two amplitude assignments, form the ordered occupation cut " +
                    "matrix. Its purity is the real trace of the square of its Gram matrix. " +
                    "Assume the before purity minus the after purity is positive. A column basis " +
                    "attains the bound when this difference equals the selected squared bias times " +
                    "the product of the other biased retained squared biases and the basis-column " +
                    "one-bit difference masses. Restrict the alternation matrix " +
                    "to the selected and other balanced retained rows and the nondeterministic " +
                    "discarded columns. The target has a one on the selected row and zero on all " +
                    "other rows. For an attaining basis to exist, every other nondeterministic " +
                    "biased retained row must lie in the selected row plus the span of the other " +
                    "balanced retained rows. The remaining requirement is that the rank of the " +
                    "balanced discarded columns, plus the number " +
                    "of nonbalanced discarded columns whose deletion excludes the target from the " +
                    "span, equals the full column rank. The deletion test detects precisely the " +
                    "coordinates forced to be one on the feasible fiber. Every such nonbalanced " +
                    "column adds one dimension to the span of the balanced columns and the other " +
                    "eligible columns. One attaining basis consists of a basis of the balanced " +
                    "discarded columns together with all the indispensable nonbalanced columns."))),
                DescribeRole.Theorem))));
}
