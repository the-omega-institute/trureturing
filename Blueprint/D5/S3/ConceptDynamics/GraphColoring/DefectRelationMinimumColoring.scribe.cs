using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class DefectRelationMinimumColoringDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/GraphColoring/DefectRelationMinimumColoring."
            + "minimum_repair_labels_eq_chromatic_eq_fiber_diversity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical defect-relation coloring computes the exact finite repair-label count.",
        H("Defect Relation Minimum Coloring"),
        Blocks(Describe.Lean(
            DescribeId.Create("defect-relation-minimum-coloring"),
            DeclarationHandle.Create(Declaration),
            H("Minimum repair labels equal chromatic number and fiber diversity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state carrier is finite. The concept and target codomains need not "
                        + "be finite because the fiber maximum is taken over the canonical "
                        + "effective image of the concept readout.")),
                Paragraph(Text(
                    "The graph adapter reads the family's canonical target-defect relation: "
                        + "two states are adjacent exactly when the concept identifies them "
                        + "and the target distinguishes them.")),
                Paragraph(Text(
                    "A finite repair label is feasible exactly when it is a proper coloring. "
                        + "The least feasible count is therefore both the graph's chromatic "
                        + "number and the largest target diversity in one concept fiber."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula record = F.Id("C");
        Formula target = F.Id("T");
        Formula labelCount = F.Id("m");
        Formula universe = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula graph = Call("defectGraph", record, target);
        Formula feasible = Call("RepairLabelFeasible", record, target, labelCount);
        Formula colorable = Call("Colorable", graph, labelCount);
        Formula minimum = Call("minimumRepairLabels", record, target);
        Formula chromatic = Call("chromaticNumber", graph);
        Formula diversity = Call("effectiveWorstFiberDiversity", record, target);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, conceptType, Comma, Sp, targetType,
            Colon, Sp, universe, Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, state, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            record, Colon, Sp, state, Sp, To, Sp, conceptType, Comma, Sp,
            target, Colon, Sp, state, Sp, To, Sp, targetType, Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, labelCount, Sp, InMacro, Sp, naturals, Comma, Sp,
            feasible, Sp, Iff, Sp, colorable, Close, Sp, Land,
            RowBreak, Grp(),
            Open, minimum, Sp, Eq, Sp, chromatic, Close, Sp, Land,
            RowBreak, Grp(),
            Open, chromatic, Sp, Eq, Sp, diversity, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
