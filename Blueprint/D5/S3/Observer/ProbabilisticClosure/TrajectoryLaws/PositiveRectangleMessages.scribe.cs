using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class PositiveRectangleMessagesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform guards from positive rectangular support", H("Uniform guards from positive rectangular support"),
        Blocks(
            Describe.Lean(DescribeId.Create("sandwich"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.sandwich"),
                H("The protected matrix mass with farther messages"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite rectangular matrix T from I to J, a middle matrix B from J to I, and arbitrary messages alpha on I and beta on J, sandwich is the sum over j,i of (sum_k alpha(k)T(k,j)) B(j,i) (sum_l T(i,l)beta(l)). It is the scalar alpha T B T beta."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-posterior-guard"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.uniform_posterior_guard"),
                H("Every nonnegative farther message shares one strict guard"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary nonempty finite I,J, strictly positive T, and two entrywise nonnegative middle matrices with strictly positive total masses, there exists one epsilon with 0<epsilon<=1/4 such that every pair of nonnegative farther messages with positive total protected mass gives a center-one ratio between epsilon and 1-epsilon. The same epsilon works for every farther row and column. Positive finite entry minima and finite upper bounds control both copies of T. There is no rank-one assumption and no normalization of zero-total atoms."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rectangle"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.Rectangle"),
                H("Exact positive rectangular support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Rectangle(T) carries nonempty finite row and column supports, strictly positive entries at every included pair, and zero entries outside their Cartesian product. It imposes no restriction on rank."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supported-message-guard"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/PositiveRectangleMessages.supported_message_guard"),
                H("A guard on the original state coordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite original state type, exact Rectangle(T), two nonnegative middle matrices, and a common nonnegative initial row giving positive protected masses for both center symbols, one epsilon in (0,1/4] bounds the center posterior away from zero and one for every nonnegative farther row and column with positive total mass. The proof restricts all sums exactly to the declared support subtypes, obtains positive middle support sums from the actual protected masses, and applies uniform_posterior_guard. All original outside-support zeros remain in the full scalar formula."))), DescribeRole.Theorem))));
}
