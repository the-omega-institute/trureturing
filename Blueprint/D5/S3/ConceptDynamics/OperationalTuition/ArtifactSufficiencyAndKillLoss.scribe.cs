using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.OperationalTuition;

internal sealed class ArtifactSufficiencyAndKillLossDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/OperationalTuition/ArtifactSufficiencyAndKillLoss."
            + "artifact_sufficient_iff_every_kill_zero_byte_loss";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Persistent artifact sufficiency exactly characterizes zero required-byte loss under "
            + "every external kill in the finite toy transition system.",
        H("Artifact Sufficiency and Kill Loss"),
        Blocks(Describe.Lean(
            DescribeId.Create("artifact-sufficiency-iff-every-kill-has-zero-byte-loss"),
            DeclarationHandle.Create(Declaration),
            H("Artifact sufficiency is equivalent to zero byte loss for every kill"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A toy state separately records required bytes, persistent artifact bytes, "
                        + "volatile session bytes, and checkpoint age. A finite event list is "
                        + "executed by foldl; work creates required session bytes, while a "
                        + "checkpoint persists the session and resets its age.")),
                Paragraph(Text(
                    "Process-group clearing and session interruption are distinct finite kill "
                        + "actions with the same persistence boundary: both erase the session and "
                        + "leave the artifact unchanged. Byte loss is required information absent "
                        + "from the resulting recoverable bytes.")),
                Paragraph(Text(
                    "Artifact sufficiency and zero post-kill loss are independently defined as "
                        + "finite-set inclusion and transition-system loss. Their equivalence uses "
                        + "finite-set difference. Insufficiency explicitly yields a session kill "
                        + "with nonempty loss, and clock loss equals checkpoint age."))),
            DescribeRole.Theorem))));

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula bytes = F.Id("Byte");
        Formula trajectory = F.Id("tau");
        Formula kill = F.Id("k");
        Formula state = Call("finalState", trajectory);
        Formula sufficient = Call("ArtifactSufficient", state);
        Formula loss = Call("byteLoss", state, kill);
        Formula zeroForEveryKill = Seq(
            Forall, Sp, kill, Colon, Sp, F.Id("KillAction"), Comma, Sp,
            loss, Sp, Eq, Sp, Emptyset);
        Formula equivalence = Seq(
            sufficient, Sp, Iff, Sp, zeroForEveryKill);
        Formula reverseWitness = Seq(
            Neg, Sp, sufficient, Sp, Rightarrow, Sp,
            Exists, Sp, kill, Colon, Sp, F.Id("KillAction"), Comma, Sp,
            Call("Nonempty", loss));
        Formula clockBound = Seq(
            Forall, Sp, kill, Colon, Sp, F.Id("KillAction"), Comma, Sp,
            Call("clockLoss", state, kill), Sp, Eq, Sp,
            Call("checkpointAge", state));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, bytes, Colon, Sp,
                Operatorname, Grp(F.Id("Type")), Comma),
            Seq(Grp(), Typeclass("DecidableEq", bytes), Comma),
            Seq(
                trajectory, Colon, Sp, Call("ToyTrajectory", bytes), Comma),
            Seq(Open, equivalence, Close, Sp, Land),
            Seq(Grp(), Open, reverseWitness, Close, Sp, Land),
            Seq(Grp(), Open, clockBound, Close, Dot),
        ]));
    }
}
