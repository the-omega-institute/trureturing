using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SixthOrderProductBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SixthOrderProductBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite product perturbation estimates used in sixth-order moment comparison.",
        H("Sixth-order product bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scalar-product-difference"), DeclarationHandle.Create(Prefix + "scalar_prod_diff_bound"),
                H("A cubic product perturbation bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let s contain exactly three indices. If both scalar families have absolute value at most a nonnegative B on s, "
                    + "and their pointwise differences have absolute value at most one, then the difference of their products has absolute value at most 3 B squared. "
                    + "A telescoping identity has three terms, each bounded by B squared."))),
                DescribeRole.Theorem))));
}
