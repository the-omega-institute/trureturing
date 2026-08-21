using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class RedundantAppealDefectPersistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Record-determined appeal evidence cannot repair a target defect.",
        H("Redundant Appeal and Defect Persistence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("redundant-appeal-cannot-repair-structural-defect"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence."
                        + "redundant_appeal_cannot_repair_structural_defect"),
                H("Record-determined appeal evidence cannot repair a defect"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The original case record C, permitted appeal evidence A, and authorized "
                            + "target T are independent readouts on the same case carrier. "
                            + "Refinement is the frozen family factorization order.")),
                    Paragraph(Text(
                        "The appeal interface is constructed as the paired readout C join A. The "
                            + "target defect is the set of case pairs identified by a readout but "
                            + "distinguished by T; full appeal capability means T factors through "
                            + "the paired interface.")),
                    Paragraph(Text(
                        "When A factors through C, the join universal property gives mutual "
                            + "refinement of C join A and C. Applying the appeal factor to equal "
                            + "record values proves that their indistinguishability relations are "
                            + "equal, so the appeal adds no case distinctions.")),
                    Paragraph(Text(
                        "Any original target-defect pair therefore remains a defect pair after the "
                            + "appeal join. Such a pair contradicts every proposed target factor, "
                            + "showing that re-review of the same coarse record does not supply full "
                            + "appeal capability.")),
                    Paragraph(Text(
                        "Repository search found no theorem packaging all four public clauses. "
                            + "The proof directly imports and applies the frozen concept-family "
                            + "primitives and Mathlib equality transport."))),
                DescribeRole.Theorem))));

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

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula recordType = Subscript(F.Id("B"), F.Id("C"));
        Formula appealType = Subscript(F.Id("B"), F.Id("A"));
        Formula outcome = F.Id("Y");
        Formula record = F.Id("C");
        Formula appeal = F.Id("A");
        Formula target = F.Id("T");
        Formula joined = Call("join", record, appeal);
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula left = F.Id("Q");
        Formula right = F.Id("R");
        Formula factor = F.Id("f");
        Formula refines = Call("Refines", left, right);
        Formula defect = Call("Defect", record, target);
        Formula joinedDefect = Call("Defect", joined, target);
        Formula conceptTypeRecord = Seq(source, Sp, To, Sp, recordType);
        Formula conceptTypeAppeal = Seq(source, Sp, To, Sp, appealType);
        Formula conceptTypeTarget = Seq(source, Sp, To, Sp, outcome);
        Formula refinesDefinition = Seq(
            refines, Sp, Iff, Sp, Exists, Sp, factor, Comma, Sp,
            left, Sp, Eq, Sp, Call("compose", factor, right));
        Formula joinDefinition = Seq(
            Apply(joined, x), Sp, Eq, Sp,
            Open, Apply(record, x), Comma, Sp, Apply(appeal, x), Close);
        Formula defectDefinition = Seq(
            Call("Defect", left, target), Sp, Eq, Sp, OpenBrace,
            Open, x, Comma, Sp, y, Close, Sp, Mid, Sp,
            Apply(left, x), Sp, Eq, Sp, Apply(left, y), Sp, Land, Sp,
            Apply(target, x), Sp, Neq, Sp, Apply(target, y), CloseBrace);
        Formula sameDistinctions = Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Sp,
            Apply(joined, x), Sp, Eq, Sp, Apply(joined, y), Sp,
            Iff, Sp, Apply(record, x), Sp, Eq, Sp, Apply(record, y));
        Formula defectClause = Seq(
            defect, Sp, Neq, Sp, Emptyset, Sp, Rightarrow, Sp,
            Open, joinedDefect, Sp, Neq, Sp, Emptyset, Sp, Land, Sp,
            Neg, Call("Refines", target, joined), Close);

        return Disp(Seq(
            record, Colon, Sp, conceptTypeRecord, Comma, Sp,
            appeal, Colon, Sp, conceptTypeAppeal, Comma, Sp,
            target, Colon, Sp, conceptTypeTarget, Comma, RowBreak, Grp(),
            refinesDefinition, Comma, RowBreak, Grp(),
            joinDefinition, Comma, RowBreak, Grp(),
            defectDefinition, Comma, RowBreak, Grp(),
            Call("Refines", appeal, record), Sp, Rightarrow, RowBreak, Grp(),
            Open, Call("ConceptEquivalent", joined, record), Close,
            Sp, Land, RowBreak, Grp(),
            Open, sameDistinctions, Close, Sp, Land, RowBreak, Grp(),
            Open, defectClause, Close, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
