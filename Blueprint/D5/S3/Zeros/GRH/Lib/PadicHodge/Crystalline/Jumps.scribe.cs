using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline;

internal sealed class JumpsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jumps", H("Jumps"),
        Blocks(
            Paragraph(Text("Diagonal Galois action on B tensor T written in matrix coordinates. Crystalline cocycles: functoriality, coboundaries, cocycle rule, saturation. Hodge–Tate weights under base change, twists, duals, subobjects, restriction of scalars.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/Jumps.sum_jump_eq_jump_overZp"),
                H("sum_jump_eq_jump_overZp"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For j of open image, R a domain finite free over Z_p, T finite free over R and potentially crystalline: jump multiplicities over Z_p are Σ_γ jump_γ(u), and weight-u maps f with f(ζt) = w f(t) span a C_p-space of dimension at most Σ_{γ(ζ)=w} jump_γ(u).")))))));
}
