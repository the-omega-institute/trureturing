using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class DihedralCentralConstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/DihedralCentralConstruction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "DihedralCentralConstruction in the actual loopless sum graphs.",
        H("Retained constructions and exact corrected examples"),
        Blocks(
            Describe.Lean(DescribeId.Create("connection-normal"),
                DeclarationHandle.Create(Prefix + "connection_normal"), H("Normality for every inverse-closed transversal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The selected rotations are Z outside the central half-turn subgroup together with the half-turn, and the selected reflections form either parity class. Inverse closure and h+h=0 prove full conjugation invariance."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("total"),
                DeclarationHandle.Create(Prefix + "total"), H("The full retained central-half-turn total construction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every n, every half-turn h with h+h=0 and h nonzero, every inverse-closed actual additive transversal Z of {0,h}, and every parity character sending h to 1, the source connection admits {1,r(h)} as a total code. Both reflection classes and either internal representative of Z are retained. At n=4*k+2, h=2*k+1 and the source parity character satisfy these hypotheses for every k>=1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("perfectconnection-normal"),
                DeclarationHandle.Create(Prefix + "perfectConnection_normal"), H("Normality of the exact perfect-code connection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Removing the half-turn subgroup leaves exactly the source reflection class and Z outside that subgroup."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("perfect"),
                DeclarationHandle.Create(Prefix + "perfect"), H("The full retained central-half-turn perfect construction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The same full parameter domain yields the source perfect code before the central half-turn is added. Outside the subgroup the total-code neighbor remains; inside it, only the vertex itself is in the closed neighborhood. These sufficient constructions do not supply the refuted exhaustive classification."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal"))]));
}
