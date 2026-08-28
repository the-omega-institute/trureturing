using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid.Connectivity;

internal sealed class SameFiberPathOrbitCriterionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inside one visible solenoid fiber, path components are integer real-flow orbits.",
        H("Same-Fiber Path Orbit Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("same-fiber-path-orbit-criterion"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/Connectivity/SameFiberPathOrbitCriterion."
                        + "same_fiber_path_orbit_criterion"),
                H("Joined points in one fiber differ by integer flow time"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the repository's universal solenoid, with its canonical "
                            + "visible projection, real flow, and Mathlib path-joining relation.")),
                    Paragraph(Text(
                        "The imported path-orbit classification first gives an arbitrary real "
                            + "flow time. Equality of visible projections makes that time zero "
                            + "in the period-one additive circle.")),
                    Paragraph(Text(
                        "The pinned additive-circle kernel theorem identifies such times with "
                            + "integers. Conversely, every integer-time translation is already a "
                            + "real-flow translation and therefore supplies a joining path."))),
                DescribeRole.Proposition))));

    private static Formula TheoremFormula()
    {
        Formula solenoid = F.Id("UniversalSolenoid");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula n = F.Id("n");

        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, solenoid, Comma, Sp,
            Call("projection", x), Sp, Eq, Sp, Call("projection", y), Sp,
            Rightarrow, Sp, Open,
            Call("Joined", x, y), Sp, Leftrightarrow, Sp,
            Exists, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
            y, Sp, Eq, Sp, Call("realFlow", n), Sp, Plus, Sp, x,
            Close, Dot));
    }
}
