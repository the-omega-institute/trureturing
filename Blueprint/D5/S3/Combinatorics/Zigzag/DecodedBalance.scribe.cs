using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class DecodedBalanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/DecodedBalance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "List-level imbalance and label injectivity show that zero-charge paths yield balanced choices without identifying distinct signed sectors.",
        H("Recovering Balance and Labels"),
        Blocks(
            Describe.Lean(DescribeId.Create("choice-imbalance-is-form-flow"),
                DeclarationHandle.Create(Prefix + "imbalance_eq_formsFlow"),
                H("Choice imbalance equals ordered form flow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The choice function is read as its exact ordered list of labels. A finite-sum reindexing matches its per-vertex out-minus-in imbalance with formsFlow beginning at class two, so the path flow theorem speaks about the source's actual balance predicate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-path-label-injectivity"),
                DeclarationHandle.Create(Prefix + "evenPathForms_injective"),
                H("Even labels uniquely determine a path"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The first label recovers the signed start and each later low/high pair recovers the indexed transition, including coincident endpoint pairs. Recursive tail injectivity reconstructs the even antipodal terminal. This proves a property of labelled paths, not merely of the weighted transfer graph."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-path-label-injectivity"),
                DeclarationHandle.Create(Prefix + "oddPathForms_injective"),
                H("Odd labels uniquely determine a path"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The same reconstruction uses the odd singleton terminal, whose table differs from the even pair. The separate theorem prevents an even-boundary argument from silently standing in for the odd inverse."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-charge-even-map"),
                DeclarationHandle.Create(Prefix + "evenZeroPathChoices_injective"),
                H("The even zero-charge map is injective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "A zero-charge path maps to a Balanced choice because its boundary flow vanishes at every nonzero residue. Equal choices give equal form lists, and the distinct sector starts plus path-label injectivity give equal paths. Odd zero-charge paths have the analogous separately proved map and injectivity."))),
                DescribeRole.Theorem)), []));
}
