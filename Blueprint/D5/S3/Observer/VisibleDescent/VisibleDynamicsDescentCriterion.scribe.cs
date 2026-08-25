using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.VisibleDescent;

internal sealed class VisibleDynamicsDescentCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/VisibleDescent/VisibleDynamicsDescentCriterion."
            + "visible_dynamics_descends_iff_cross_block_zero";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Visible bounded dynamics closes exactly when hidden-to-visible flow vanishes.",
        H("Visible Dynamics Descent Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("visible-dynamics-descent-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Visible descent is equivalent to a zero cross block"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let P be orthogonal projection onto a visible subspace V of a Hilbert "
                        + "space, and let Q be projection onto its orthogonal complement.")),
                Paragraph(Text(
                    "A bounded linear flow T factors through P as a bounded evolution on V "
                        + "exactly when the hidden-to-visible block PTQ is zero."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula space = F.Id("H");
        Formula visible = F.Id("V");
        Formula projection = F.Id("P");
        Formula hiddenProjection = F.Id("Q");
        Formula dynamics = F.Id("T");
        Formula descent = F.Id("Tbar");
        Formula projectionDynamics = Seq(projection, Sp, Circ, Sp, dynamics);
        Formula commutes = Seq(
            projectionDynamics, Sp, Eq, Sp,
            descent, Sp, Circ, Sp, projection);
        Formula existsDescent = Seq(
            Exists, Sp, descent, Colon, Sp, visible, Sp, To, Sp, visible,
            Comma, Sp, commutes);
        Formula crossBlock = Seq(
            projection, Sp, Circ, Sp, dynamics, Sp, Circ, Sp, hiddenProjection,
            Sp, Eq, Sp, D(0));
        Formula setup = Call(
            "HilbertSetup", scalar, space, visible, projection,
            hiddenProjection, dynamics);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Comma, Sp, visible, Comma, Sp,
            projection, Comma, Sp, hiddenProjection, Comma, Sp, dynamics, Comma,
            RowBreak, Grp(),
            setup, Sp, Rightarrow,
            RowBreak, Grp(),
            Open, existsDescent, Close, Sp, Iff, Sp, crossBlock, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
