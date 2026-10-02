using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ZeckendorfResidualCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/ZeckendorfResidualCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded complete residual representatives.",
        H("Bounded complete residual representatives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorfresidualcover-tile"),
                DeclarationHandle.Create(Prefix + "tile"),
                H("Iterated source tile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a : Bool × Bool, tile 0 a = [a] and tile (H + 1) a = (mu a).flatMap (tile H). These are iterates of the same decorated source substitution."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfresidualcover-sourceprefix"),
                DeclarationHandle.Create(Prefix + "sourcePrefix"),
                H("Numerical source prefix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For n : ℕ, sourcePrefix n = (List.range n).map q, the first n letters of the actual decorated numerical source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfresidualcover-1"),
                DeclarationHandle.Create(Prefix + "all_state_cover"),
                H("Bounded complete residual representatives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete statement is `theorem all_state_cover (H c : ℕ) (hH : 14 ≤ H) (hc : c ≤ Nat.fib H) (w : List (Fin 2)) (hw : NoAdjacentOnes w) : ∃ v : List (Fin 2), NoAdjacentOnes v ∧ v.length = H + 7 ∧ residual c w = residual c v`.")),
                    Paragraph(Text("Every legal padded prefix has the same complete Option residual as a legal word of length H+7 whenever c≤F_H and H≥14. Iterated numerical substitution tiles realize every adjacent source pair in a finite prefix."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfRawWindow"))]));
}
