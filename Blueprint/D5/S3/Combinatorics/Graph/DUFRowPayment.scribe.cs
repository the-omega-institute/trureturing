using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFRowPaymentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Payment for marked triangle rows",
        H("Payment for marked triangle rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/DUFRowPayment.result"),
                H("Payment for marked triangle rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For an actual valid row r, let I(r) be its internal group and let w(e) be the reciprocal weight of a member e. Its nonnegative deficit is delta(r)=max(2|I(r)| minus the sum of w(e) over I(r),0). At a graph vertex x, the deletion debt is 1/6 minus the sum, over its neighbors y, of 1/(2(degree(y)+1)). These quantities use the actual local graph and the actual marked row.")),
                    Paragraph(Text("If r has exactly one mark b, then its internal group has two members and its recipient is outside that group. The recipient is an actual triple of H. Its assigned vertex is mixed, and the row deficit is at most the maximum of that vertex debt and zero. Moreover, positive row deficit implies positive vertex debt, and the deficit is then at most the debt itself. No lower bound on the recipient weight is assumed.")),
                    Paragraph(Text("The endpoint estimate is obtained from the singleton-leaf reciprocal inequality after transporting the actual row geometry into its local graph. The two internal endpoints have weights at least 23/12 plus the respective common-link reciprocal terms. Their sum bounds the raw two-member deficit by precisely the assigned recipient debt. Taking positive parts gives the stated deficit comparison.")),
                    Paragraph(Text("If r has at least two marks, both the row and its internal group have total weight at least six, and the deficit is zero. Two distinct marks identify a central member with two singleton-color leaves and weight at least 13/6. Each of the other two actual members has weight at least 23/12. The three estimates sum to six. All statements require DUF and actual validity of the row; no codegree bound or ambient size bound is imposed."))),
                DescribeRole.Theorem))));
}
