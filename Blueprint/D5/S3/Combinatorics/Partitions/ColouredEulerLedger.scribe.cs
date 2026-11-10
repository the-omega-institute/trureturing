using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;
internal sealed class ColouredEulerLedgerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/ColouredEulerLedger.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite coloured partitions and integer Euler coefficients", H("Finite coloured partitions and integer Euler coefficients"), Blocks(
            Paragraph(Text("For a part size d appearing with multiplicity m, a multiset of m elements of Fin(colors(d)) records colours of indistinguishable occurrences. A sigma type over ordinary partitions and a dependent product over occurring part sizes give an actual finite carrier. Its cardinality is computed independently from the Euler-series definition, including empty colour sets and degree zero.")),
            Node("ColouredPartition", "ColouredPartition", "The carrier is a finite sigma of finite products of symmetric powers. Finite cardinality is actual type cardinality, not a symbol assigned to the desired coefficient.", DescribeRole.Definition),
            Node("coloured_coefficient", "coloured coefficient", "Fintype cardinality gives the product of multichoose values for every partition. Mathlib identifies this weighted partition generating function with its infinite product. The shared local-factor reconstruction and the actual HasProd theorem of the existing Euler series identify the two coefficient functions.", DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("colouredeulerledger-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
