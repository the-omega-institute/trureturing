using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class MultiTargetDefectGraphColoringDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/GraphColoring/MultiTargetDefectGraphColoring."
            + "joint_target_defect_graph_and_minimum_labels";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint-target defect graphs are component unions, with chromatic minimum repair.",
        H("Multi-Target Defect Graph Coloring"),
        Blocks(Describe.Lean(
            DescribeId.Create("joint-target-defect-graph-and-minimum-labels"),
            DeclarationHandle.Create(Declaration),
            H("Joint defect graph union and minimum repair labels"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a finite state carrier, the canonical defect graph of a dependent "
                        + "joint target is the indexed supremum of the component defect "
                        + "graphs.")),
                Paragraph(Text(
                    "The same graph equality identifies the least number of finite repair "
                        + "labels with the chromatic number of that indexed supremum."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula DependentTargetType(
        Formula index,
        Formula indexType,
        Formula targetFamily) =>
        Seq(
            Open, Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Call("Concept", F.Id("X"), Apply(targetFamily, index)), Close);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula indexType = F.Id("Index");
        Formula currentOutput = F.Id("Current");
        Formula targetFamily = F.Id("Target");
        Formula index = F.Id("index");
        Formula current = F.Id("current");
        Formula targets = F.Id("targets");
        Formula universe = Seq(Operatorname, Grp(F.Id("Type")));
        Formula jointGraph = Call(
            "defectGraph", current, Call("jointTarget", targets));
        Formula componentUnion = Call(
            "iSup",
            Seq(index, Colon, Sp, indexType),
            Call("defectGraph", current, Apply(targets, index)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, indexType, Comma, Sp, currentOutput,
            Colon, Sp, universe, Comma, RowBreak, Grp(),
            targetFamily, Colon, Sp, indexType, Sp, To, Sp, universe, Comma,
            RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Fintype")),
            Open, state, Close, CloseBracket, Comma, RowBreak, Grp(),
            current, Colon, Sp, Call("Concept", state, currentOutput), Comma,
            RowBreak, Grp(),
            targets, Colon, Sp,
            DependentTargetType(index, indexType, targetFamily), Comma,
            RowBreak, Grp(),
            Open, jointGraph, Sp, Eq, Sp, componentUnion, Close, Sp, Land,
            RowBreak, Grp(),
            Open,
            Call("minimumRepairLabels", current, Call("jointTarget", targets)),
            Sp, Eq, Sp, Call("chromaticNumber", componentUnion),
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
