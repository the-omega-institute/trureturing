using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class ZeckendorfResidualMachineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/ZeckendorfResidualMachine.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite partial machines.",
        H("Actual finite partial machines"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorfresidualmachine-sourcebase"),
                DeclarationHandle.Create(Prefix + "sourceBase"),
                H("Exact padded word domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("sourceBase : BaseAutomaton (Fin 2) Bool starts at false. Reading zero moves to some false; reading one moves to some true from false and to none from true. This records the previous-one flag and leaves every input containing 11 undefined."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfresidualmachine-residualstate"),
                DeclarationHandle.Create(Prefix + "ResidualState"),
                H("Actual live residual image"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For c : ℕ, ResidualState c is {r : List (Fin 2) → Option Bool // ∃ w, NoAdjacentOnes w ∧ residual c w = r}. Only complete residuals of legal prefixes occur; every state has an actual prefix and the omitted sink is absent."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfresidualmachine-admissible"),
                DeclarationHandle.Create(Prefix + "Admissible"),
                H("Reachable partial MSD machines"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For c k : ℕ, Admissible c k means ∃ P : BaseAutomaton (Fin 2) (Fin k), ∃ output : Fin k → Bool, P.step P.start 0 = some P.start ∧ (∀ w, (P.run w).map output = residual c [] w) ∧ (∀ s, ∃ w, P.run w = some s). All k states, including the initial state, are reachable and counted. The all-word Option equation requires correct output on every valid padded word and undefined execution on every invalid word. The empty word and every all-zero word output parity c."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfresidualmachine-minimumstates"),
                DeclarationHandle.Create(Prefix + "minimumStates"),
                H("Minimum live state count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For c : ℕ, minimumStates c = sInf {k | Admissible c k}. Finite residual realization makes this set nonempty. Since it is a set of natural numbers, its infimum is attained; an admissible machine has a start state, so the minimum is positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zeckendorfresidualmachine-1"),
                DeclarationHandle.Create(Prefix + "finite_residual_realization"),
                H("Actual finite partial machines"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete statement is `theorem finite_residual_realization (c : ℕ) : Finite (ResidualState c) ∧ Admissible c (Nat.card (ResidualState c))`.")),
                    Paragraph(Text("The actual residual image is finite for every shift. Its cardinality is realized by a reachable Boolean partial machine whose counted start loops on zero. Execution is defined exactly on all legal padded no11 words, including the empty word. The minimum ranges over ordinary partial transition systems with these complete source equations."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/ZeckendorfResidualCover"))]));
}
