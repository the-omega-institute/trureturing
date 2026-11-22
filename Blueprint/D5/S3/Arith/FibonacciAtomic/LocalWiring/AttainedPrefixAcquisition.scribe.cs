using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LocalWiring;

internal sealed class AttainedPrefixAcquisitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/LocalWiring/AttainedPrefixAcquisition.";
    private static Formula N => F.Id("N");
    private static Formula M => new Formula.Subscript(F.Id("M"), F.Id("addr"));
    private static Formula Joint => Seq(
        F.Id("Q"), Eq, F.Id("m"), Comma, Quad, Sp, F.Id("U"), Eq, N, Comma, Quad, Sp,
        F.Id("W"), Leq, Sp, F.Id("m"), Open, N, Minus, D(1), Close, Comma, Quad, Sp,
        M, Leq, Sp, N, Minus, D(1));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A source-blind native program actually earns its mature bits and ends with " +
        "a correct installed generator and the three requested forms of readiness.",
        H("Native mature-prefix acquisition"),
        Blocks(Describe.Lean(
            DescribeId.Create("gpo-attained-prefix-acquisition"),
            DeclarationHandle.Create(Prefix + "attained_prefix_acquisition"),
            H("Joint read and update coordinates of the attained program"),
            StatementSource.FromAuthor(Disp(Joint)),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public target m is 2d for binary recurrence order at most d, " +
                    "2K−1 for nonempty unary Moore carrier of size at most K, and r for " +
                    "the supplied entire row of length r with unknown seed. For m>0, " +
                    "N is the least n≥3 with F_n−1≥m; for m=0, N=2, the law is already " +
                    "zero and Q, W and the maximum are all zero. The zero law is known " +
                    "before that cut; the comparison here is for mature cuts.")),
                Paragraph(Text(
                    "At each eligible cut the program replays the old labelled tree " +
                    "from the word already earned, traverses its beta leaves in physical " +
                    "left-first order, and requests their literal parent-aa addresses " +
                    "on the actual updated root. The answer equals the older birth bit, " +
                    "not a newly hidden orientation. The final batch is limited to the " +
                    "remaining quota. Update acknowledgements, literal addresses and " +
                    "Read replies agree with the actual native observer run.")),
                Paragraph(Text(
                    "The weights are exact: W is the sum of the full parent-aa lengths " +
                    "and the maximum is the largest such length, or zero if no address " +
                    "was requested. These are measured on the same trace, with exactly " +
                    "the first m ordered births read, not on separately optimized runs.")),
                Paragraph(Text(
                    "Actual service effects alternate with source-free local phases for " +
                    "traversal, writing literals, retaining replies, finite first-match " +
                    "synthesis or fixed-row initialization, and reconstruction. The " +
                    "terminal register contains the installed generator, current labelled " +
                    "tree, its consumed-bit cursor and the exact next-cut and future " +
                    "answers. Predicted unread values are not paid Read replies. Local " +
                    "blocks record finite computation without a primitive work bound, " +
                    "and no physical installation or minimum-Read claim is made."))),
            DescribeRole.Theorem))));
}
