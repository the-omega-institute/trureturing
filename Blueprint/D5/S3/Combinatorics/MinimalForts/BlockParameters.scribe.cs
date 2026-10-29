using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class BlockParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/BlockParameters.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Feasible sequences in every residue", H("Feasible sequences in every residue"),
        Blocks(
            Node("rate", "The growth base", "rate", "The real growth base is exactly three halves.", DescribeRole.Definition),
            Node("negative-increment", "Complete-block increment", "negativeIncrement", "The actual increment is the natural logarithm of two thirds.", DescribeRole.Definition),
            Node("positive-increment", "Octahedral increment", "positiveIncrement", "The actual increment is the natural logarithm of four thirds.", DescribeRole.Definition),
            Node("slope", "Target slope", "slope", "The target slope equals six times log(3/2) minus log(9). The inequalities 9<(3/2)^6<12 place it strictly between zero and the positive increment.", DescribeRole.Definition),
            Node("offset", "Residue correction", "offset", "For r in Fin 6, including all six residues zero through five, the real correction is (r+3)log(3/2)-log(r+2).", DescribeRole.Definition),
            Node("residue-sequences", "Feasible sequences in every residue", "residue_sequences", "There exist natural-valued x,y,z indexed by r in Fin 6 and every natural k, with x(r,k)+y(r,k)+z(r,k)=k at every index. For each residue the signed error x log(2/3)+z log(4/3)-k slope-offset(r) tends to zero along the entire natural sequence. No residue or finite prefix is discarded from the domain. This follows by applying the feasible-simplex approximation to the actual irrational logarithmic ratio and interior slope.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
