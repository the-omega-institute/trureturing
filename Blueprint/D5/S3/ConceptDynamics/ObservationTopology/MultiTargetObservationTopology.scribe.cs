using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class MultiTargetObservationTopologyDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/ObservationTopology/MultiTargetObservationTopology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint-target continuity and separation deficits decompose into component targets.",
        H("Multi-Target Observation Topology"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-target-continuity-is-componentwise"),
                DeclarationHandle.Create(
                    Prefix + "jointTarget_continuous_iff_components"),
                H("Joint-target continuity is exactly componentwise continuity"),
                StatementSource.FromAuthor(ContinuityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A dependent joint target records every indexed target value at "
                            + "once. Continuity from the readout partition therefore forces "
                            + "each coordinate target to be continuous.")),
                    Paragraph(Text(
                        "Conversely, componentwise continuity makes every target constant "
                            + "on each readout fiber. Function extensionality then makes the "
                            + "whole dependent tuple constant on that fiber.")),
                    Paragraph(Text(
                        "Both sides use the bottom topology on the relevant target carrier; "
                            + "no finiteness or inhabitedness condition on the index is "
                            + "asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-target-deficit-is-component-union"),
                DeclarationHandle.Create(
                    Prefix + "jointTarget_separationDeficit_eq_iUnion"),
                H("The joint-target deficit is the union of component deficits"),
                StatementSource.FromAuthor(DeficitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A pair lies in the joint separation deficit when the current "
                            + "readout identifies it but the dependent target tuple "
                            + "distinguishes it.")),
                    Paragraph(Text(
                        "Two dependent tuples differ exactly when some indexed coordinate "
                            + "differs. The same pair therefore lies in at least one "
                            + "component separation deficit.")),
                    Paragraph(Text(
                        "Extensionality yields equality with the indexed union, not merely "
                            + "one inclusion."))),
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

    private static Formula DependentCarrierType(
        Formula index,
        Formula indexType,
        Formula targetFamily) =>
        Seq(
            Open, Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Apply(targetFamily, index), Close);

    private static Formula ContinuityFormula()
    {
        Formula state = F.Id("X");
        Formula indexType = F.Id("Index");
        Formula coordinate = F.Id("Coordinate");
        Formula targetFamily = F.Id("Target");
        Formula index = F.Id("index");
        Formula readout = F.Id("readout");
        Formula targets = F.Id("targets");
        Formula jointContinuity = Call(
            "Continuous",
            Call("partitionTopology", readout),
            Call(
                "bottomTopology",
                DependentCarrierType(index, indexType, targetFamily)),
            Call("jointTarget", targets));
        Formula componentContinuity = Seq(
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Call(
                "Continuous",
                Call("partitionTopology", readout),
                Call("bottomTopology", Apply(targetFamily, index)),
                Apply(targets, index)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, readout, Colon, Sp, Call("Concept", state, coordinate),
            Comma, RowBreak, Grp(),
            targets, Colon, Sp,
            DependentTargetType(index, indexType, targetFamily), Comma,
            RowBreak, Grp(),
            jointContinuity, Sp, Iff, Sp,
            Open, componentContinuity, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula DeficitFormula()
    {
        Formula state = F.Id("X");
        Formula indexType = F.Id("Index");
        Formula currentOutput = F.Id("Current");
        Formula targetFamily = F.Id("Target");
        Formula index = F.Id("index");
        Formula current = F.Id("current");
        Formula targets = F.Id("targets");
        Formula componentUnion = Call(
            "iUnion",
            Seq(index, Colon, Sp, indexType),
            Call("separationDeficit", current, Apply(targets, index)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, current, Colon, Sp,
            Call("Concept", state, currentOutput), Comma, RowBreak, Grp(),
            targets, Colon, Sp,
            DependentTargetType(index, indexType, targetFamily), Comma,
            RowBreak, Grp(),
            Call("separationDeficit", current, Call("jointTarget", targets)),
            Sp, Eq, Sp, componentUnion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
