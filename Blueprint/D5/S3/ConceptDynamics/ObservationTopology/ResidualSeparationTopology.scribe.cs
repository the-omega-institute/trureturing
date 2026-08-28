using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class ResidualSeparationTopologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A target defect is exactly a topological separation deficit.",
        H("Residual Separation Topology"),
        Blocks(Describe.Lean(
            DescribeId.Create("defect-relation-is-separation-deficit"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/ObservationTopology/ResidualSeparationTopology."
                    + "defectRelation_eq_separationDeficit"),
            H("The target defect relation equals the separation deficit"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A target defect is a pair of states identified by the current readout "
                        + "but distinguished by the target.")),
                Paragraph(Text(
                    "Partition-topology inseparability is exactly equality of the "
                        + "corresponding readout. Current equality is therefore current "
                        + "inseparability, while target inequality is failure of target "
                        + "inseparability.")),
                Paragraph(Text(
                    "Extensionality identifies the two sets of pairs. The theorem is an exact "
                        + "set equality and introduces no additional topological condition."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula currentOutput = F.Id("Current");
        Formula targetOutput = F.Id("Target");
        Formula current = F.Id("current");
        Formula target = F.Id("target");

        return Disp(Seq(
            Forall, Sp, current, Colon, Sp,
            Call("Concept", state, currentOutput), Comma, Sp,
            target, Colon, Sp, Call("Concept", state, targetOutput), Comma, Sp,
            Call("defectRelation", current, target), Sp, Eq, Sp,
            Call("separationDeficit", current, target), Dot));
    }
}
