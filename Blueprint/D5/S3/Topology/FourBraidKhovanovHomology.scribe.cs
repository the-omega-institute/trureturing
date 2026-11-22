using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FourBraidKhovanovHomologyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/FourBraidKhovanovHomology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral cohomology from a chain contraction",
        H("Integral cohomology from a chain contraction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-braid-cohomology-equivalence"),
                DeclarationHandle.Create(Owner + "cohomologyEquiv"),
                H("A contraction identifies cycles modulo boundaries"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The middle cohomology of an integral three-term complex is the actual kernel "
                    + "of the outgoing map modulo the restricted image of the incoming map. "
                    + "Projection onto the residual free group descends because it annihilates "
                    + "boundaries. Inclusion sends each residual vector to a cycle. Their first "
                    + "composition is the identity on residual vectors. On a cycle, the chain "
                    + "homotopy identifies the second composition with the original vector modulo "
                    + "boundaries. This is an integral linear equivalence."))),
                DescribeRole.Theorem))));
}
