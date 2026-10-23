using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class CompactnessDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/KyFanGap/Compactness.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compactness of weighted symmetric sign models.",
        H("Weighted symmetric sign models"), Blocks(
            Describe.Lean(DescribeId.Create("kyfan-model-defect"),
                DeclarationHandle.Create(Owner + "modelDefect"),
                H("Two joint defects"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonnegative probability vector p and a real symmetric matrix S determine two nonnegative quantities. The first is the sum of p(a)p(b)(S(a,b)^2-1)^2 over pairs of nodes. The second is the sum of p(a)(sum_b S(a,b)p(b)-c)^2 over nodes. Their sum measures simultaneous failure of the sign and constant weighted row-sum constraints, using the same matrix and the same weights."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kyfan-model-defect-gap"),
                DeclarationHandle.Create(Owner + "exists_model_defect_gap"),
                H("A positive defect gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix a finite order R, an entry bound M, and a nonsquare natural number k. There is a positive lower bound for the joint defect at c=1/sqrt(k) among all nonnegative weights of sum one and all symmetric R by R matrices with entries of absolute value at most M. If the lower bound failed, a convergent subsequence in the product of finite closed boxes would give a zero-defect limit. Nonnegative terms then vanish separately. On the positive-weight support the limiting entries are minus one or one, and all weighted row sums equal c. Reindexing this support gives a symmetric rational matrix and weights of sum one, contradicting the nonsquare row-sum obstruction. Zero weights are permitted throughout and removed only from the limiting model."))),
                DescribeRole.Theorem))));
}
