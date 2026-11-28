using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.WachGamma;

internal sealed class KisinModuleDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kisin Module Defs", H("Kisin Module Defs"),
        Blocks(
            Paragraph(Text("the Artin–Schreier–Witt resolution over the tilt. This file treats only the φ−1 step of Herr's complex, on Witt vectors of the tilt of C_p modulo p^m, and not the Γ-step. Source: L. Herr, Sur la cohomologie galoisienne des corps p-adiques, Bull. SMF 126 (1998) 563–600.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/KisinModuleDefs.smallPart_spec"),
                H("smallPart_spec"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let S be the image of W(𝔪^♭) in M=W(C^♭)⊗ℤ/p^m(1). Then p^m kills M, φ−1 is onto, φd−d∈S implies d∈ℤ/p^m(1)+S, S∩ℤ/p^m(1)=0; and for ρ trivial modulo p^m near 1, L: W(C^♭)⊗ρ→M linear and any v, L(hv−v)∈S for h near 1.")))))));
}
