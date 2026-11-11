using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class CentredProductExpansionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Alternating subset expansion of centred finite products in a commutative ring.",
        H("Centred product expansion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prod-sub-one-expansion"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredProductExpansion.prod_sub_one_expansion"),
                H("Alternating subset expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any finite set D in an index type with decidable equality and any function F "
                    + "into a commutative ring, the product of F(d)-1 over D equals the sum over "
                    + "subsets J of D of (-1)^(|D|-|J|) times the product of F(d) over J. "
                    + "Mathlib's Finset.prod_add expands the factors; the complementary subset "
                    + "has cardinality |D|-|J|. This identity applies to prime correlations, "
                    + "Boolean-cube coordinate functions and finite-sieve variables."))),
                DescribeRole.Theorem))));
}
