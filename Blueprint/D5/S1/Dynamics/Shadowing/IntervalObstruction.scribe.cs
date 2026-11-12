using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class IntervalObstructionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef IntervalSource =
        LibraryNoteRef.Create("D5/L/Dynamics/gangloff2023various");
    private const string Owner = "D5/S1/Dynamics/Shadowing/IntervalObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every continuous nondegenerate compact real-interval selfmap fails finite positive expansivity.",
        H("IntervalObstruction"), Blocks(
        Describe.Lean(DescribeId.Create("interval-witnesses"), DeclarationHandle.Create(Owner + "interval_bowen_witnesses"),
            H("Arbitrarily many distinct all-time close witnesses"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(IntervalSource),
            Blocks(Paragraph(Text("For every real a < b, every continuous f : Icc a b -> Icc a b, every epsilon > 0 and every natural N, there are a center x and an injective family y : Fin (N+1) -> Icc a b such that dist(f^t(x), f^t(y_i)) < epsilon for every i and every natural t. Neither onto dynamics nor a monotonicity hypothesis is required. This is the arbitrary closed-interval, finite-family formulation of the known interval obstruction in Theorem 3.8 of the cited source; the repository supplies a direct Lean proof. The witnesses are consumed by the circle argument."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("interval-obstruction"), DeclarationHandle.Create(Owner + "interval_not_finitelyPositiveExpansive"),
            H("The interval obstruction"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(IntervalSource),
            Blocks(Paragraph(Text("Every continuous selfmap of the actual nondegenerate compact interval fails FinitelyPositiveExpansive. This is the known interval obstruction in Theorem 3.8 of the cited source, proved directly here for arbitrary real endpoints and used as a supplier in the circle theorem. Overlapping macroscopic iterate images yield an invariant interval if every iterate is injective; orientation gluing, finite fibres and monotone trapping rule that case out. Otherwise exact disjoint fold pullbacks double coalescing histories. Equality at a common terminal time controls the entire infinite tail, while the construction controls every earlier time including zero and the terminal time. The argument produces 2^N distinct histories against the same uniform N. The subtype extension preserves the original dynamics and all-time Bowen condition."))), DescribeRole.Theorem))));
}
