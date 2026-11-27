using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Fock;

internal sealed class RealDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real Data", H("Real Data"),
        Blocks(
            Paragraph(Text("Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known result; see Lib.Weil.Fock.OscillatorPair).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Fock/RealData.theta_integrated"),
                H("theta_integrated"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For v in the Fock space and f in 𝒮(V), θ(v ⊗ f) = ∫ v(y) f̃(y) dy, with f̃(x) = θ(ϱ(x)f), y over real vectors in Fock coordinates with the measure realMeasure.")))))));
}
