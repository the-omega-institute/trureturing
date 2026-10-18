using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class FiniteFairBitDenominatorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitDenominator.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FiniteFairBitDenominator", H("One determinant for actual fair-tape exit laws"), Blocks(
            Paragraph(Text("All permitted entrances generate one common carrier U of positively reachable internal states. N counts continuation alternatives and C counts complete exit-label alternatives. A deterministic alternative contributes two; each fair alternative contributes one, even when successors coincide. Their real casts are exactly twice the actual primitive T and R masses. Analytical label coordinates do not enlarge U.")),
            Paragraph(Text("The actual ENNReal tape-event masses are finite because tapeLaw is a probability measure. The actual renewal identity is transferred to reals by finite-mass sum and addition identities. No rationality, normalization, inverse or desired-law equality is assumed. The operational reachable escape theorem trims unreachable columns and supplies one strict real escape block; the substochastic supplier makes I minus T nonsingular. Casting A equals 2(I minus T), where A is 2I minus N, transfers nonsingularity to its integer determinant.")),
            Paragraph(Text("The integer adjugate identity gives det(A) times the actual exit mass equal to an integer coordinate of adj(A)C. Absolute values give natural integer numerators for d equal to the absolute integer determinant. This one positive d clears every complete exit coordinate at every reachable state and every permitted entrance. Immediate exit rows are literal zero/one event masses. Empty U has determinant one. No absorbing label vertices are charged.")),
            Paragraph(Text("Every real row of A has l1 norm at most four. The existing Matrix.det_mul_transpose_self_le_prod, applied after finite reindexing, bounds the squared determinant by the product of row squared lengths. Thus d is at most four to card U. A CompleteCodec for the original installed program and its admitted micro snapshots bounds the entire common carrier by two to B; the same determinant is at most four to two to B. The codec result is reused at its original source.")),
            Paragraph(Text("This certificate concerns the actual first-exit events of the displayed original deterministic/fair alternatives. Applying it to all original native installations still requires A1 native adequacy and A4 primitive trace, label and complete-return correspondence. The sample Command interpreter is not a universal compiler. A first semantic event can precede physical return and can be erased. Native labels must follow actual receipts, program counter, mode and cursor uniformly over pending histories and entrances. No NativeLawCorrect or arbitrary source-law equality discharges these obligations.")),
            Paragraph(Text("The four-service application, actual eta, P_alpha, P_beta and q_alpha, the original native realization, paid fetching and installation peaks belong to the remaining assignment. The two same-update and positive-history compatibility assumptions are separate. Clearing q and P by d does not assert that d clears their product H; that product can need d squared.")),
            Node("statement-0", "actual_exit_denominator"),
            Node("statement-1", "charged_exit_denominator"))));
    private static DocumentBlock.Describe Node(string id, string name) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The compiled statement includes its complete displayed premises."))),
            DescribeRole.Theorem);
}
