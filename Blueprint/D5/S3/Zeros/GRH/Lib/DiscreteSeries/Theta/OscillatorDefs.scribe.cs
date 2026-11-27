using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta;

internal sealed class OscillatorDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Oscillator Defs", H("Oscillator Defs"),
        Blocks(
            Paragraph(Text("Oscillator actions on Fock polynomials, matched parameters, joint harmonics.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Theta/OscillatorDefs.swap_oscRows_E"),
                H("swap_oscRows_E"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("In the column action (row action of the swap of T), E_ab acts by −s·Σ_r B_(r,a) A_(r,b) + γ'δ_ab, with A, B the operators raiseOp, lowerOp for the signs of the variables, s = 1 if ε'_a = ε'_b, else σ.")))))));
}
