using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.OperationalTuition;

internal sealed class FirstClaimProtocolNonduplicationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/OperationalTuition/FirstClaimProtocolNonduplication."
            + "t4_atomic_visibility_nonduplication_and_collision_rate_monotone";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite T4-compliant atomic claim traces confine concurrent implementation to visibility "
            + "windows, and their expected collision rate is monotone in trace delay.",
        H("First-Claim Protocol Nonduplication"),
        Blocks(Describe.Lean(
            DescribeId.Create(
                "t4-atomic-visibility-nonduplication-and-collision-rate-monotone"),
            DeclarationHandle.Create(Declaration),
            H("Atomic T4 traces prevent outside-window duplication"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The finite event list records implementation attempts, yield readouts, and "
                        + "reclaim readouts. Activity is a Boolean interval test, while exact atomic "
                        + "visibility begins at claim time plus the declared delay.")),
                Paragraph(Text(
                    "T4 compliance is structure evidence. A visible active holder forces another "
                        + "operator inactive and records the affected readout; reclaim attempts must "
                        + "follow the declared stall threshold and carry a matching trace.")),
                Paragraph(Text(
                    "Therefore simultaneous implementation can occur only before both claims become "
                        + "visible. Counting finite ordered claim pairs inside the delay window and "
                        + "normalizing by the fixed pair population makes collision rate monotone "
                        + "when trace delay increases."))),
            DescribeRole.Theorem))));

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula operators = F.Id("O");
        Formula trajectory = F.Id("t");
        Formula protocol = Call("toFiniteProtocol", trajectory);
        Formula confinement = Call(
            "ConcurrencyConfinedToVisibilityWindow",
            protocol);
        Formula rateMonotone = Call(
            "Monotone",
            Call("collisionRate", protocol));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, operators, Colon, Sp,
                Operatorname, Grp(F.Id("Type")), Comma),
            Seq(Grp(), Typeclass("DecidableEq", operators), Comma),
            Seq(
                trajectory, Colon, Sp,
                Call("T4CompliantTrajectory", operators), Comma),
            Seq(confinement, Sp, Land),
            Seq(Grp(), rateMonotone, Dot),
        ]));
    }
}
