using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class SemanticClosureTopologyInvarianceDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semantic closure adds recoverable readouts without changing family observation "
            + "topology.",
        H("Semantic Closure Topology Invariance"),
        Blocks(Describe.Lean(
            DescribeId.Create("definition-closure-preserves-partition-topology"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/ObservationTopology/"
                    + "SemanticClosureTopologyInvariance."
                    + "partitionTopology_definitionClosure_eq"),
            H("Definition closure leaves family partition topology unchanged"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The family readout evaluates every definition in the supplied family at "
                        + "once. Its kernel records pairs on which all family members agree.")),
                Paragraph(Text(
                    "DefinitionClosure adds exactly the readouts recoverable from the old "
                        + "family. The imported kernel theorem shows that these additions do "
                        + "not change the joint kernel.")),
                Paragraph(Text(
                    "Readouts with the same kernel induce the same partition topology. Hence "
                        + "the closed family and original family have equal observation "
                        + "topologies, not merely comparable ones."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("Output");
        Formula family = F.Id("Gamma");
        Formula closedReadout = Call(
            "familyReadout",
            Call("DefinitionClosure", family));

        return Disp(Seq(
            Forall, Sp, family, Colon, Sp,
            Call("Set", Call("Concept", state, output)), Comma, Sp,
            Call("partitionTopology", closedReadout), Sp, Eq, Sp,
            Call("partitionTopology", Call("familyReadout", family)), Dot));
    }
}
