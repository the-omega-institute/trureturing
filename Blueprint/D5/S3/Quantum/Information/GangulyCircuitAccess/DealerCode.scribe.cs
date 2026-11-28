using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GangulyCircuitAccess;

internal sealed class GangulyDealerCodeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GangulyCircuitAccess/DealerCode.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/ganguly2026stabilizersecretsharing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized graph-state slices give an isometry onto the common fixed space of the shortened lift.",
        H("The dealer-shortened stabilizer code for the witness"),
        Blocks(
            Node("dealercode-witnessplayers", "WitnessPlayers", "Player configurations",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "The player basis is the product of the discarded and retained configuration types, in that order."),
            Node("dealercode-graphpauli", "graphPauli", "Lift of the binary adjacency labels",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "For x and z in Bits(7), apply the translation ψ(z+x) and multiply by the sign with binary exponent q(x) + (Mx)·z. Here q is the quadratic graph phase. This is the Pauli with label (x,Mx), in output phase order Z(Mx)X(x), multiplied by the sign of q(x)."),
            Node("dealercode-witnessgraphstate", "witnessGraphState", "Graph-state amplitudes",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "At z in Bits(7), take the graph sign divided by the square root of 128, in the complex numbers."),
            Node("dealercode-shortenedpauli", "shortenedPauli", "Player operator of a shortened label",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "Apply the graph Pauli to the player wave function pulled back by restriction to player coordinates, and evaluate at the joint configuration with dealer bit zero. The shortening uses labels x with x(4) = (Mx)(4) = 0."),
            Node("dealercode-witnessshortenedcode", "witnessShortenedCode", "The shortened fixed space",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "The code consists of all player vectors fixed by every shortened Pauli whose two dealer coordinates vanish."),
            Node("dealercode-witness-proposition8", "witness_proposition8", "Witness correspondence with Proposition 8(2\u20133)",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "The lifted operators compose by addition of their binary labels. A full vector fixed by every lift is exactly a scalar multiple of the graph state. For every label with both dealer coordinates zero and every player vector, the lifted operator on that vector is independent of the dealer bit and agrees with the shortened player operator. Every joint graph-state amplitude is the corresponding slice entry divided by √2. The dealer marginal has entries obtained by summing each amplitude times the conjugate amplitude at the other dealer bit over all player configurations, and equals I/2. The slice matrix satisfies V†V = I and its image equals the whole shortened fixed space. Multiplying a player amplitude by its zero-dealer graph sign makes it constant on each of the two dealer-parity classes. Both classes occur by dealer surjectivity. The two columns span the resulting functions, with relative sign +1 on one class and −1 on the other."))));

    private static DocumentBlock Node(string id, string name, string title, StatementSource statement,
        DescribeRole role, string prose) => Describe.Lean(
        DescribeId.Create("ganguly-circuit-access-" + id), DeclarationHandle.Create(Prefix + name),
        H(title), statement, AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
