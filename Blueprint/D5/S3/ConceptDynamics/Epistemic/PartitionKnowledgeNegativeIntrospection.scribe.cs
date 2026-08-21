using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class PartitionKnowledgeNegativeIntrospectionDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Knowledge defined on readout fibers recognizes its own failure.",
        H("Partition Knowledge Negative Introspection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fiber-knowledge"),
                DeclarationHandle.Create(DeclarationPrefix + "fiberKnowledge"),
                H("Fiberwise knowledge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A predicate is known at a state when it holds at every state with the "
                        + "same readout value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("partition-topology"),
                DeclarationHandle.Create(DeclarationPrefix + "partitionTopology"),
                H("Readout partition topology"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The readout partition topology is induced from the discrete topology on "
                        + "the coordinate type, so its open sets are unions of readout fibers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("partition-knowledge-negative-introspection"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "partition_knowledge_negative_introspection"),
                H("Open failure and negative introspection"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary state and coordinate types, the readout and predicate are "
                            + "independent source primitives. Fiberwise knowledge and the partition "
                            + "topology are constructed from that readout.")),
                    Paragraph(Text(
                        "The public statement records both source clauses: the complement of the "
                            + "knowledge set is open, and every state where knowledge fails knows "
                            + "that failure throughout its whole readout fiber.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies openness for induced discrete topologies. Negative "
                            + "introspection follows by transporting one failed fiber condition to "
                            + "every state with the same readout."))),
                DescribeRole.Theorem))));

    private static Formula Knowledge(Formula readout, Formula predicate) =>
        Seq(F.Id("K"), Underscore, Grp(readout), Open, predicate, Close);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula coordinateType = F.Id("B");
        Formula readout = F.Id("C");
        Formula predicate = F.Id("P");
        Formula state = F.Id("x");
        Formula knowledge = Knowledge(readout, predicate);
        Formula failure = Seq(stateType, Sp, Setminus, Sp, knowledge);
        Formula knowsFailure = Knowledge(readout, failure);
        Formula partitionTopology = Seq(Tau, Underscore, Grp(readout));
        Formula openFailure = Seq(
            Operatorname, Grp(F.Id("IsOpen")), Underscore, Grp(partitionTopology),
            Open, failure, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, coordinateType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            readout, Colon, Sp, stateType, Sp, To, Sp, coordinateType, Comma, Sp,
            predicate, Subset, Sp, stateType, Comma, RowBreak, Grp(),
            openFailure, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, state, InMacro, Sp, stateType, Comma, Sp,
            Neg, Open, state, InMacro, Sp, knowledge, Close, Sp, Rightarrow, Sp,
            state, InMacro, Sp, knowsFailure, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
