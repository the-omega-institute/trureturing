using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.OperationalTuition;

internal sealed class PreregisteredArtifactAcceptanceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/OperationalTuition/PreregisteredArtifactAcceptance."
            + "missing_envelope_acceptance_iff_preregistered_and_inheritable";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A missing routing envelope permits independent artifact acceptance exactly when a "
            + "fixed criterion was recorded before production, and that witness survives seat death.",
        H("Preregistered Artifact Acceptance"),
        Blocks(Describe.Lean(
            DescribeId.Create("missing-envelope-acceptance-iff-preregistered-and-inheritable"),
            DeclarationHandle.Create(Declaration),
            H("Missing-envelope acceptance is preregistered and inheritable"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite delivery keeps the optional routing envelope separate from a frozen "
                        + "toy artifact trajectory. The distinguished artifact checkpoint follows "
                        + "the complete finite prefix used by the independent verifier.")),
                Paragraph(Text(
                    "The executable judgment scans only that prefix. Its forward direction extracts "
                        + "a concrete registered criterion whose fixed Boolean verifier accepts the "
                        + "computed final artifact state; the reverse direction runs that witness.")),
                Paragraph(Text(
                    "Seat death clears the envelope and liveness flag but preserves the artifact and "
                        + "pre-artifact prefix. Consequently the same finite witness establishes "
                        + "postmortem acceptance without trusting a self-reported status."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/OperationalTuition/ArtifactSufficiencyAndKillLoss"))]));

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula criteria = F.Id("C");
        Formula bytes = F.Id("B");
        Formula verifier = F.Id("v");
        Formula delivery = F.Id("d");
        Formula inherited = Call("inheritAfterSeatDeath", delivery);
        Formula witness = Call(
            "Nonempty",
            Call("PreregisteredAcceptanceWitness", verifier, delivery));
        Formula absentAcceptance = Seq(
            Call("missingEnvelopeAcceptance", verifier, delivery), Sp, Eq, Sp, F.Id("true"));
        Formula characterization = Seq(
            absentAcceptance, Sp, Iff, Sp,
            Open,
            Call("EnvelopeMissing", delivery), Sp, Land, Sp, witness,
            Close);
        Formula inheritedAcceptance = Seq(
            witness, Sp, Rightarrow, Sp,
            Call("missingEnvelopeAcceptance", verifier, inherited),
            Sp, Eq, Sp, F.Id("true"));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, criteria, Comma, Sp, bytes, Colon, Sp,
                Operatorname, Grp(F.Id("Type")), Comma),
            Seq(
                Grp(), Typeclass("DecidableEq", criteria), Comma, Sp,
                Typeclass("DecidableEq", bytes), Comma),
            Seq(
                verifier, Colon, Sp, criteria, Sp, Rightarrow, Sp,
                Call("ToyState", bytes), Sp, Rightarrow, Sp, F.Id("Bool"), Comma),
            Seq(
                delivery, Colon, Sp, Call("DeliveryRecord", criteria, bytes), Comma),
            Seq(Open, characterization, Close, Sp, Land),
            Seq(Grp(), Open, inheritedAcceptance, Close, Dot),
        ]));
    }
}
