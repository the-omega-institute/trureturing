using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class RotationWindowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/RotationWindow.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform approximation by irrational rotation.",
        H("Uniform approximation by irrational rotation"),
        Blocks(
            Node("uniform-real-window", "Uniform real integer lifts", "uniform_real_window", "For every positive real period p and real increment b with irrational b divided by p, and every positive real error epsilon, one common natural threshold M works for every N at least M and every real target T. There are integers x and z with N at most x at most three N and absolute value of x b plus z p minus T smaller than epsilon. Dense integer rotations supply an open cover of the compact circle; a finite subcover bounds all required integer indices. Translation moves the symmetric bounded indices into the prescribed positive window. Nearest-integer rounding lifts the metric back to real units.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
