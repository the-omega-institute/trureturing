using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.TimeProjection;

internal sealed class FiniteTimeProjectionRestrictionLawsDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionRestrictionLaws."
            + "finite_time_projection_expansion_and_restriction_laws";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite time projections expand into bounded readout equality and restrict exactly along horizon inclusion.",
        H("Finite Time Projection Restriction Laws"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-time-projection-expansion-and-restriction-laws"),
            DeclarationHandle.Create(Declaration),
            H("Projection expansion, horizon restriction, and the zero-horizon law"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Equality of two projections through N is equivalent to equality of "
                        + "their iterated readouts at every natural time k no later than N.")),
                Paragraph(Text(
                    "The restriction map preserves the value of every finite index when "
                        + "embedding Fin(N+1) into Fin(M+1). Consequently a longer projection "
                        + "restricts definitionally to the shorter projection, while horizon "
                        + "zero returns the current readout."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula transition = F.Id("tau");
        Formula shorter = F.Id("N");
        Formula longer = F.Id("M");
        Formula inclusion = F.Id("h");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula time = F.Id("k");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula shortLeft = Call("timeProjection", readout, transition, shorter, left);
        Formula shortRight = Call("timeProjection", readout, transition, shorter, right);
        Formula longLeft = Call("timeProjection", readout, transition, longer, left);
        Formula leftAtTime = Seq(
            readout, Open,
            Call("timeIter", transition, time, left), Close);
        Formula rightAtTime = Seq(
            readout, Open,
            Call("timeIter", transition, time, right), Close);
        Formula expansion = Seq(
            Open, shortLeft, Sp, Eq, Sp, shortRight, Sp, Iff, RowBreak, Grp(),
            Forall, Sp, time, Colon, Sp, naturals, Comma, Sp,
            time, Sp, Leq, Sp, shorter, Sp, Rightarrow, Sp,
            leftAtTime, Sp, Eq, Sp, rightAtTime, Close);
        Formula restriction = Seq(
            Call("restrictTime", inclusion, longLeft), Sp, Eq, Sp, shortLeft);
        Formula zeroHorizon = Seq(
            Call("timeProjection", readout, transition, D(0), left, D(0)),
            Sp, Eq, Sp, readout, Open, left, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, Sp,
            transition, Colon, Sp, state, Sp, To, Sp, state, Comma,
            RowBreak, Grp(),
            shorter, Comma, Sp, longer, Colon, Sp, naturals, Comma, Sp,
            inclusion, Colon, Sp, shorter, Sp, Leq, Sp, longer, Comma, Sp,
            left, Comma, Sp, right, Colon, Sp, state, Comma,
            RowBreak, Grp(),
            expansion, Sp, Land, RowBreak, Grp(),
            restriction, Sp, Land, RowBreak, Grp(),
            zeroHorizon, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
