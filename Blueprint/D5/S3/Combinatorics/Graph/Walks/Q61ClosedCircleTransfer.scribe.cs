using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class Q61ClosedCircleTransferDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer";
    private const string Digest =
        "Exact closed-circle transfers via tight three-state min-plus matrix words.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, Digest, "evidence-not-specified-by-formal-manifest",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Data.Int.Interval"),
            Anchor.ParseCanonical("mathlib/module/Mathlib.Data.Nat.Prime.Basic"),
            Anchor.ParseCanonical("mathlib/module/Mathlib.LinearAlgebra.Matrix.Notation"),
            Anchor.ParseCanonical("mathlib/module/Mathlib.NumberTheory.Real.Irrational"),
            Anchor.ParseCanonical("mathlib/module/Mathlib.Topology.Instances.AddCircle.Real")),
        H("Closed two-circle register transfers"),
        Blocks(
            Paragraph(Text("The ordinary proof of undecidable exact attainment at value zero in theory PR 54 uses these transfers as local steps in the full machine graph. The marked-return payoff argument in q61-return-reward-response.txt uses the completed transfers after the literal reset to P. Lean coverage here is the local passage. https://github.com/the-omega-institute/trureturing-source-theories/pull/54")),
            Describe.Lean(
                DescribeId.Create("exact-two-loop-transfer"),
                DeclarationHandle.Create(Module + ".run_word_iff"),
                H("The two-loop passage forces the input and output"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Encode integers on the unit circle using the injective orbit of √2 − 1. For arbitrary circle inputs, the row with loop counts k and j completes exactly when the input encodes (bk + r, 0), j = ak, and the output encodes (ak + s, 0)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("closed-lifts-realize-circle-step"),
                DeclarationHandle.Create(Module + ".exists_branch"),
                H("Finite branches realize every closed lift of a permitted step"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any closed source and target lifts of a permitted circle step, a branch uses bounded integer wraps and selects the source lift 0 or 1 independently at each tested coordinate. Its closed rectangular guard contains the source and its translation reaches the chosen target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-compiled-passage"),
                DeclarationHandle.Create(Module + ".compiled_passage_iff"),
                H("Tight matrix words implement the exact residue transfer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each branch matrix has nonpositive total score gain, with equality exactly on its guard. From any real three-state score in the translated square, a compiled passage has zero total gain and the stated projected endpoint exactly when the input encodes (n, 0) for positive n with (n − 1) mod b = r − 1, and the endpoint encodes (a⌊(n − 1)/b⌋ + s, 0). Here 1 ≤ r ≤ b."))),
                DescribeRole.Theorem))));
}
