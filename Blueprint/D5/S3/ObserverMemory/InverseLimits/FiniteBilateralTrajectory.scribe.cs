using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class FiniteBilateralTrajectoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bilateral trajectories of a finite system are uniquely based at periodic points.",
        H("Finite Bilateral Trajectories"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-systems-have-unique-bilateral-periodic-trajectories"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/FiniteBilateralTrajectory."
                        + "finite_bilateral_trajectory"),
                H("Finite systems have unique bilateral periodic trajectories"),
                StatementSource.FromAuthor(TrajectoryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be finite and F a self-map. A bilateral trajectory is represented "
                            + "by its backward half x, satisfying F(x(n+1))=x(n); its forward half "
                            + "is then generated uniquely by F. A bilateral periodic trajectory "
                            + "is the subtype for which every represented state is periodic.")),
                    Paragraph(Text(
                        "The exact repository coordinate-periodicity theorem proves the first "
                            + "conjunct and shows that every compatible trajectory belongs to that "
                            + "subtype. The exact coordinate-zero bijection supplies one trajectory "
                            + "through each periodic point and proves its uniqueness.")),
                    Paragraph(Text(
                        "The imported repository results apply the pinned-Mathlib declarations "
                            + "Function.bijOn_periodicPts, Function.IsPeriodicPt.eq_of_apply_eq, "
                            + "and Fintype.exists_ne_map_eq_of_card_lt. Repository and pinned-"
                            + "Mathlib searches found no theorem packaging both displayed clauses."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TrajectoryFormula()
    {
        Formula carrier = F.Id("Y");
        Formula update = F.Id("F");
        Formula orbit = F.Id("x");
        Formula time = F.Id("n");
        Formula point = F.Id("y");
        Formula trajectory = F.Id("b");
        Formula backwardOrbits = Apply(F.Id("B"), update);
        Formula periodicCore = Apply(F.Id("P"), update);
        Formula periodicTrajectories = Apply(Subscript(F.Id("B"), F.Id("per")), update);
        Formula finite = Seq(
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, carrier, CloseBracket);

        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp, finite, Comma, Esc,
            update, Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, Esc,
            Open, Forall, Sp, orbit, Sp, InMacro, Sp, backwardOrbits, Comma, Sp,
            Forall, Sp, time, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Subscript(orbit, time), Sp, InMacro, Sp, periodicCore, Close, Sp, Land, Esc,
            Open, Forall, Sp, point, Sp, InMacro, Sp, periodicCore, Comma, Esc,
            Exists, Bang, Sp, trajectory, Colon, Sp, periodicTrajectories, Comma, Esc,
            Subscript(trajectory, D(0)), Sp, Eq, Sp, point, Close, Dot));
    }
}
