using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValueScale;

internal sealed class StrictMonotoneObjectiveArgmaxAlignmentDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DecisionValueScale/StrictMonotoneObjectiveArgmaxAlignment."
            + "strict_monotone_factorization_preserves_argmax";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly increasing objective factorization preserves every feasible argmax set.",
        H("Strict Monotone Objective Argmax Alignment"),
        Blocks(Describe.Lean(
            DescribeId.Create("strict-monotone-factorization-preserves-argmax"),
            DeclarationHandle.Create(Declaration),
            H("Strictly increasing factorization preserves feasible maximizers"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The agent and principal objectives are real-valued functions on the same "
                        + "state-action carrier and are optimized over the same feasible set.")),
                Paragraph(Text(
                    "A strictly increasing transform preserves and reflects every weak order "
                        + "comparison, so each feasible candidate is maximal for one objective "
                        + "exactly when it is maximal for the other."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula Maximizers(
        Formula feasible,
        Formula objective,
        Formula candidate,
        Formula alternative) =>
        Seq(
            OpenBrace, candidate, Sp, Mid, Sp,
            candidate, Sp, InMacro, Sp, feasible, Sp, Land, Sp,
            Forall, Sp, alternative, Sp, InMacro, Sp, feasible, Comma, Sp,
            Apply(objective, alternative), Sp, Leq, Sp,
            Apply(objective, candidate), CloseBrace);

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("Z");
        Formula feasible = F.Id("S");
        Formula agent = Sub(F.Id("O"), F.Id("A"));
        Formula principal = Sub(F.Id("O"), F.Id("P"));
        Formula transform = F.Id("g");
        Formula candidate = F.Id("z");
        Formula alternative = F.Id("w");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, F.Id("Type"), Comma, Sp,
            feasible, Colon, Sp, Call("Set", carrier), Comma, Sp,
            agent, Comma, Sp, principal, Colon, Sp,
            carrier, Sp, To, Sp, reals, Comma, Sp,
            transform, Colon, Sp, reals, Sp, To, Sp, reals, Comma, RowBreak, Grp(),
            Call("StrictMono", transform), Sp, Land, Sp,
            principal, Sp, Eq, Sp, Compose(transform, agent), RowBreak, Grp(),
            Rightarrow, Sp,
            Maximizers(feasible, agent, candidate, alternative), Sp, Eq, Sp,
            Maximizers(feasible, principal, candidate, alternative), Dot));
    }
}
