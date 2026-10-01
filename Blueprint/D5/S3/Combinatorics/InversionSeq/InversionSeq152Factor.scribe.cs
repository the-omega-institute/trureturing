using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152FactorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152Factor.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lists of Dyck paths factor a Dyck path at its initial ascent or final descent.",
        H("Factorizations at the Initial Ascent and Final Descent"),
        Blocks(
            Node("inversionseq-inversionseq152factor-ascent-word", "Assembly at the initial ascent", "ascentWord",
                "Starting with the empty Dyck path, read a list of factors from left to right. At each factor, surround the current path with an up step and a down step, then concatenate the factor. This defines the path assembled at its initial ascent.", DescribeRole.Definition),
            Node("inversionseq-inversionseq152factor-descent-word", "Assembly at the final descent", "descentWord",
                "Starting with the empty Dyck path, read a list of factors from right to left. At each factor, concatenate that factor with the current path surrounded by an up step and a down step. This defines the path assembled at its final descent.", DescribeRole.Definition),
            Node("inversionseq-inversionseq152factor-ascent-factors", "Factors along the initial ascent", "ascentFactors",
                "The empty Dyck path has no ascent factors. For a nonempty Dyck path, factor the portion enclosed by its first matching up and down steps recursively, then append the remaining exterior portion as the last factor.", DescribeRole.Definition),
            Node("inversionseq-inversionseq152factor-run-factorization", "Two bijective run factorizations", "runFactorization",
                "Both assemblies are bijections from lists of Dyck paths to Dyck paths. With k factors, the ascent assembly consists of k up steps followed by each factor preceded by a down step, and its initial ascent has length k. The descent assembly consists of each factor followed by an up step, then k down steps, and its final descent has length k. In both cases the semilength is k plus the sum of factor semilengths. The ascent lengths of the ascent assembly are its initial ascent, when nonempty, followed by all ascent lengths of the factors. The inverse of ascent assembly is recursive ascent factorization; the inverse of descent assembly reflects the path, takes its ascent factors, reverses their order and reflects each factor.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
