using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GangulyCircuitAccess;

internal sealed class GangulyRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/ganguly2026stabilizersecretsharing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A seven-vertex simple graph refutes the inclusion in Ganguly’s Section VI Problem 2.",
        H("A circuit-authorized set that cannot recover the secret"),
        Blocks(
            Node("recovery-reconstructs", "reconstructs", "Recovery by one CPTP map",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "There exists one completely positive trace-preserving map from matrices on the retained basis to the logical qubit matrices. For every logical complex matrix ρ, applying this map to the reduced encoding of ρ yields ρ. The CStarMatrix conversions only change the Lean carrier."),
            Node("recovery-claim", "claim", "Universal inclusion of circuit access in recovery access",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "Ganguly, Section VI, Problem 2, asks whether for simple graphs Γ the condition that Γᶜⁱʳᶜ_{L(Γ),d} is a quantum access structure implies Γᶜⁱʳᶜ_{L(Γ),d} ⊆ Γʳᵉᶜ_d. The Lean assertion quantifies over all natural vertex counts, simple graphs on Fin(n) with decidable adjacency, and dealers. Under the quantum access antecedent it requires recovery for every circuit-authorized A using the dealer-slice encoding."),
            Node("recovery-witness-no-common-recovery", "witness_no_common_recovery", "No function recovers both inputs",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "There is no function from retained complex matrices to qubit matrices that sends the retained reduction of the positive logical input to the positive input and the retained reduction of the negative logical input to the negative input. The two arguments of the function coincide and the two demanded values differ."),
            Node("recovery-result", "result", "Refutation of the universal inclusion",
                StatementSource.FromAuthor(Disp(new Formula.Not(new Formula.Symbol(FormulaIdentifier.Create("claim"))))), DescribeRole.Theorem,
                "The universal inclusion is false. For the seven-vertex graph the circuit family is a quantum access structure and contains {2, 5, 6} at dealer 4. The encoding is the isometry into the shortened code established by the witness correspondence with Proposition 8. A completely positive trace-preserving recovery map would give a function recovering both logical pure inputs from their common retained matrix."))));

    private static DocumentBlock Node(string id, string name, string title, StatementSource statement,
        DescribeRole role, string prose) => Describe.Lean(
        DescribeId.Create("ganguly-circuit-access-" + id), DeclarationHandle.Create(Prefix + name),
        H(title), statement, AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
