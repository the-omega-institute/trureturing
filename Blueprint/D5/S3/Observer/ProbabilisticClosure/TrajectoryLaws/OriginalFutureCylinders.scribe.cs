using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class OriginalFutureCylindersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original cylinders at a future-output cut", H("Original cylinders at a future-output cut"),
        Blocks(
            Paragraph(Text("The joinHidden, join_left, join_right and path_concat declarations expose the existing concatenation construction and its unchanged proofs. OriginalRectangleOccurrence consumes them to retain a prescribed hidden route before summing the later visible word.")),
            Paragraph(Text("PathSpace H carries the original integer hidden and output coordinates. future(t,z)(k) is X(t+k), for every natural k. past(t,z)(k) is the pair (H(t-k-1),X(t-k-1)). These are the complete future-output and strictly earlier marked half-lines. state(t,z) is H(t), so X(t) belongs to the future and H(t) is the conditioning boundary. All maps use the original emitted-bit clock.")),
            Describe.Lean(DescribeId.Create("past-future-mass"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureCylinders.past_future_mass"),
                H("Actual finite factorization at every integer boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix any finite hidden alphabet with measurable singletons, any original Presentation theta, and any probability J satisfying its proved original cylinders. For every integer t, natural lengths m and n, hidden word h of length m+1, past output word w of length m and future output word v of length n, the J real mass of cylinder(t-m,m,h,w) intersected with the visible v cylinder starting at t equals lambda(h(0)) times pathMass(M,m,h,w) times futureMass(M,h(m),n,v). The past cylinder includes H(t), while its last output is X(t-1). Length zero, zero weights and arbitrary stochastic successor mixtures are included.")),
                    Paragraph(Text("Append every possible future hidden tail to the fixed past hidden word. The resulting full original marked cylinders form a disjoint union of the event being measured. Their path products split at H(t); summing the future hidden tails uses OriginalMarkedLaw.sum_path_tails. This establishes the finite factorization from the actual original cylinder law."))), DescribeRole.Theorem))));
}
