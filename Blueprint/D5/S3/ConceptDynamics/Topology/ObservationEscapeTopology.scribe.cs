using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class ObservationEscapeTopologyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Topology/ObservationEscapeTopology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel refinement and productive separation include empty-source primitive escape.",
        H("Observation Escape Topology"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("primitive-escape-is-strict-partition-refinement"),
                DeclarationHandle.Create(
                    Prefix + "primitiveEscape_iff_strict_partition_refinement"),
                H("Primitive escape is strict partition refinement"),
                StatementSource.FromAuthor(PrimitiveEscapeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The complete family readout records every old definition, while "
                            + "the extended readout pairs those coordinates with the "
                            + "candidate value.")),
                    Paragraph(Text(
                        "Primitive escape is equivalent to strict refinement from the old "
                            + "partition topology to the extended one, with Mathlib's "
                            + "reversed order on topologies displayed explicitly.")),
                    Paragraph(Text(
                        "No inhabited-source hypothesis is required. On an empty source, "
                            + "both primitive escape and strict refinement are false, so the "
                            + "biconditional remains valid without asserting an escape."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("productive-separation-is-a-topological-target-split"),
                DeclarationHandle.Create(
                    Prefix + "productiveSeparation_iff_topological_target_split"),
                H("Productive separation is a topological target split"),
                StatementSource.FromAuthor(ProductiveSeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A productive separation is witnessed by two source states that the "
                            + "current readout cannot separate but the target can.")),
                    Paragraph(Text(
                        "The same states remain inseparable under the joint readout of the "
                            + "complete old family, while the candidate partition topology "
                            + "separates them.")),
                    Paragraph(Text(
                        "The biconditional packages exactly these four inseparability and "
                            + "separation clauses. It adds no inhabitedness, finiteness, or "
                            + "continuity hypothesis."))),
                DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Concept(Formula state, Formula output) =>
        Call("Concept", state, output);

    private static Formula PartitionTopology(Formula readout) =>
        Call("partitionTopology", readout);

    private static Formula Inseparable(
        Formula topology,
        Formula left,
        Formula right) =>
        Call("Inseparable", topology, left, right);

    private static Formula PrimitiveEscapeFormula()
    {
        Formula state = F.Id("X");
        Formula inputOutput = F.Id("InputOutput");
        Formula output = F.Id("Output");
        Formula family = F.Id("Gamma");
        Formula candidate = F.Id("candidate");
        Formula oldTopology = PartitionTopology(Call("familyReadout", family));
        Formula extendedTopology = PartitionTopology(
            Call("extendedFamilyReadout", family, candidate));
        Formula conclusion = Seq(
            Call("PrimitiveEscape", family, candidate), Sp, Iff, Sp,
            extendedTopology, Sp, Lt, Sp, oldTopology);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(
                Seq(state, Comma, Sp, inputOutput, Comma, Sp, output),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(family, Call("Set", Concept(state, inputOutput))),
            Comma, RowBreak, Grp(),
            Typed(candidate, Concept(state, output)), Comma, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ProductiveSeparationFormula()
    {
        Formula state = F.Id("X");
        Formula currentOutput = F.Id("Current");
        Formula inputOutput = F.Id("InputOutput");
        Formula targetOutput = F.Id("Target");
        Formula candidateOutput = F.Id("Output");
        Formula family = F.Id("Gamma");
        Formula current = F.Id("current");
        Formula target = F.Id("target");
        Formula candidate = F.Id("candidate");
        Formula left = F.Id("left");
        Formula right = F.Id("right");
        Formula witnesses = Seq(
            Exists, Sp,
            Typed(Seq(left, Comma, Sp, right), state), Comma, Sp,
            Inseparable(PartitionTopology(current), left, right),
            Sp, Land, RowBreak, Grp(),
            Neg, Sp, Inseparable(PartitionTopology(target), left, right),
            Sp, Land, RowBreak, Grp(),
            Inseparable(
                PartitionTopology(Call("familyReadout", family)),
                left,
                right),
            Sp, Land, RowBreak, Grp(),
            Neg, Sp, Inseparable(PartitionTopology(candidate), left, right));
        Formula conclusion = Seq(
            Call("ProductiveSeparation", family, current, target, candidate),
            Sp, Iff, RowBreak, Grp(),
            Open, witnesses, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(
                Seq(
                    state, Comma, Sp,
                    currentOutput, Comma, Sp,
                    inputOutput, Comma, Sp,
                    targetOutput, Comma, Sp,
                    candidateOutput),
                TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(family, Call("Set", Concept(state, inputOutput))),
            Comma, RowBreak, Grp(),
            Typed(current, Concept(state, currentOutput)), Comma, RowBreak, Grp(),
            Typed(target, Concept(state, targetOutput)), Comma, RowBreak, Grp(),
            Typed(candidate, Concept(state, candidateOutput)), Comma, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
