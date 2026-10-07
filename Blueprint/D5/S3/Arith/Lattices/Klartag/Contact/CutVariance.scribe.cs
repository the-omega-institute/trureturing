using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Contact;

internal sealed class CutVarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Contact/CutVariance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contact profile counts and accumulated projection dimension.",
        H("Cut Variance"),
        Blocks(
            Paragraph(Text("Contact profile counts and accumulated projection dimension. The results below relate cut variance to the stochastic ellipsoid construction.")),
            Node("claim-1", "goodPathCut_var", "good Path Cut var",
                "The stopped log determinant variance, contact failure probability and expected shortfall satisfy a joint probability budget. This ensures a path with the required determinant and contact bounds at the cut.", DescribeRole.Theorem),
            Node("claim-2", "stateTriple_of_cut_var", "state Triple of cut var",
                "The cut probability budget yields a positive definite terminal state with the specified determinant lower bound and controlled active contacts.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
