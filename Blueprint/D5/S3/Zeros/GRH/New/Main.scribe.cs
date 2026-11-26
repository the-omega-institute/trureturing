using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New;

internal sealed class MainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Main", H("Main"),
        Blocks(
            Paragraph(Text("The inequality (⋆) from Theorems A to C; the one-sided bound; GRH. Zeros lie on the critical line, given non-vanishing right of one half.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Main.zeta_zeros_on_line"),
                H("zeta_zeros_on_line"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Assume h: no Dirichlet L-function vanishes in Re s > 1/2 (the pole at s = 1 excepted). Then the Riemann hypothesis holds: every zero s ≠ 1 of ζ other than −2, −4, … has Re s = 1/2.")))))));
}
