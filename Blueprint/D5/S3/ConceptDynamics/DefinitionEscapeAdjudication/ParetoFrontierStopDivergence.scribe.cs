using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class ParetoFrontierStopDivergenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/"
            + "ParetoFrontierStopDivergence."
            + "pareto_frontier_requires_sourced_orientation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One Pareto frontier yields opposite stop decisions under two complete sourced orientations.",
        H("Pareto Frontier Does Not Determine Stop"),
        Blocks(Describe.Lean(
            DescribeId.Create("pareto-frontier-requires-sourced-orientation"),
            DeclarationHandle.Create(Declaration),
            H("A sourced orientation is necessary to derive the stop target"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier is Fin 2. Candidates and feasible actions are both the full "
                        + "carrier, action zero is current, and the five natural-valued "
                        + "coordinates give actions zero and one one strict benefit each.")),
                Paragraph(Text(
                    "Both orientations admit every action and keep every action in scope. "
                        + "The stay orientation is equality with false source and version; "
                        + "the advance orientation is index order with true source and version.")),
                Paragraph(Text(
                    "The first displayed conjunct is the full three-part finite certificate: "
                        + "no Pareto dominator, a stay-oriented stop, and no advance-oriented "
                        + "stop. The second conjunct separately records the requested failure "
                        + "of implication from the Pareto frontier to the advance stop.")),
                Paragraph(Text(
                    "The theorem reuses the frozen five-coordinate Pareto relation and the "
                        + "canonical governance decision set. Repository, pinned-Mathlib, and "
                        + "third-party Lean searches found no existing stop certificate."))),
            DescribeRole.Theorem))));

    private static Formula Stop(
        Formula admissible,
        Formula scope,
        Formula orientation,
        Formula decision) =>
        Call(
            "AdjudicationStopTargetOnDecisionSet",
            admissible,
            scope,
            orientation,
            decision);

    private static Formula TheoremFormula()
    {
        Formula value = Seq(F.Id("v"), Underscore, D(2));
        Formula decision = Seq(F.Id("D"), Underscore, D(2));
        Formula admissible = Seq(F.Id("AdmTarget"), Underscore, D(2));
        Formula scope = Seq(F.Id("InScope"), Underscore, D(2));
        Formula stay = Seq(F.Id("O"), Underscore, Grp(F.Id("stay")));
        Formula advance = Seq(F.Id("O"), Underscore, Grp(F.Id("advance")));
        Formula frontier = Call("NoDominatingCandidate", value, decision);
        Formula stayStop = Stop(admissible, scope, stay, decision);
        Formula advanceStop = Stop(admissible, scope, advance, decision);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open,
            frontier, Sp, Land, RowBreak, Grp(),
            stayStop, Sp, Land, RowBreak, Grp(),
            Neg, Sp, advanceStop,
            Close, Sp, Land, RowBreak, Grp(),
            Neg, Sp, Open,
            frontier, Sp, Rightarrow, Sp, advanceStop,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
