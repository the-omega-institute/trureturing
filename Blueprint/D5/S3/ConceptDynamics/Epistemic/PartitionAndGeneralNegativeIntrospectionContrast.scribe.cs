using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class PartitionAndGeneralNegativeIntrospectionContrastDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Epistemic/PartitionAndGeneralNegativeIntrospectionContrast."
            + "partition_and_general_negative_introspection_contrast";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partition knowledge satisfies negative introspection, but general topological "
            + "knowledge need not.",
        H("Partition and General Negative-Introspection Contrast"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partition-and-general-negative-introspection-contrast"),
                DeclarationHandle.Create(Declaration),
                H("Negative introspection holds for partitions but fails in general"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary state and coordinate types, the readout and predicate are "
                            + "independent source primitives. The knowledge set and topology are "
                            + "constructed from the readout exactly as in the frozen family module.")),
                    Paragraph(Text(
                        "The first public conjunct states that knowledge failure is open in the "
                            + "readout-partition topology and is known throughout the failing "
                            + "readout fiber.")),
                    Paragraph(Text(
                        "The second public conjunct is an explicit countermodel for unrestricted "
                            + "topological knowledge. In Mathlib's Sierpinski topology on Prop, "
                            + "the interior of the singleton true predicate is that singleton, "
                            + "while false is not interior to its complement."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula Interior(Formula topology, Formula predicate) =>
        Seq(Operatorname, Grp(F.Id("Int")), Underscore, Grp(topology), Open, predicate, Close);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula coordinateType = F.Id("B");
        Formula readout = F.Id("C");
        Formula predicate = F.Id("P");
        Formula state = F.Id("x");
        Formula knowledge = Apply("K", readout, predicate);
        Formula failure = Seq(stateType, Sp, Setminus, Sp, knowledge);
        Formula knowsFailure = Apply("K", readout, failure);
        Formula partitionTopology = Seq(Tau, Underscore, Grp(readout));
        Formula openFailure = Seq(
            Operatorname, Grp(F.Id("IsOpen")), Underscore, Grp(partitionTopology),
            Open, failure, Close);

        Formula propositions = F.Id("Prop");
        Formula sierpinski = Seq(Tau, Underscore, Grp(F.Id("S")));
        Formula truePredicate = Seq(OpenBrace, F.Id("true"), CloseBrace);
        Formula interior = Interior(sierpinski, truePredicate);
        Formula interiorFailure = Interior(
            sierpinski, Seq(propositions, Sp, Setminus, Sp, interior));
        Formula contrast = Seq(
            Neg, Open, Forall, Sp, state, InMacro, Sp, propositions, Comma, Sp,
            Neg, Open, state, InMacro, Sp, interior, Close, Sp, Rightarrow, Sp,
            state, InMacro, Sp, interiorFailure, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, Forall, Sp, stateType, Comma, Sp, coordinateType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            readout, Colon, Sp, stateType, Sp, To, Sp, coordinateType, Comma, Sp,
            predicate, Subset, Sp, stateType, Comma, RowBreak, Grp(),
            openFailure, Sp, Land, RowBreak, Grp(),
            Forall, Sp, state, InMacro, Sp, stateType, Comma, Sp,
            Neg, Open, state, InMacro, Sp, knowledge, Close, Sp, Rightarrow, Sp,
            state, InMacro, Sp, knowsFailure, Close, RowBreak, Grp(),
            Land, Sp, contrast, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
