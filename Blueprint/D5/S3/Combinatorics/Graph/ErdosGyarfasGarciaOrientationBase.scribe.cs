using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ErdosGyarfasGarciaOrientationBaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationBase.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared parametric affine replacement infrastructure for Garcia orientation certificates.",
        H("Parametric Garcia affine replacement infrastructure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("garcia-affine-replacement"),
                DeclarationHandle.Create(Prefix + "refutes_of_certificates"),
                H("Certificate words force a 64-cycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a prime p, multiplier a, and two fourteen-letter words over the three edge types, assume each word closes with fourteen distinct prefix products, has the stated incident-type partition, and has unused-type histograms (6,4,4) and (2,6,6). For every orientation sigma and every compatible family of port bijections tau, the literal H15 replacement of the affine Cayley graph contains a simple cycle of length 64.")),
                    Paragraph(Text("The shared construction defines AGL(1,p), t, g, r, the Cayley base, the H15 gadget and its explicit paths. The finite certificate assumptions feed the general translated-visit averaging theorem; ten eligible cycle vertices use the three-edge paths and the remaining four use five-edge paths. The disjoint-block expansion theorem then gives length 14 + 10*3 + 4*5 = 64."))),
                DescribeRole.Theorem))));
}
