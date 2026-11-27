using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class DoubleLiftValueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Double Lift Value", H("Double Lift Value"),
        Blocks(
            Paragraph(Text("Two unfolding steps equal a double theta lift of the evaluated datum.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/DoubleLiftValue.integral_constTermAtT_mul"),
                H("integral_constTermAtT_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a pair D there is one constant z such that, for generic P on U(V), the integral over [B] × [B'] of P(gt) times the two constant terms at T, T' equals z∫_{[U(X)]} P(gt) ∫_{[U(X')]} θ(Ω(g, r, D.embX k) ev ϱ(T*, T')(f ⊗ f')), ev the zero term along ArrowPair.splitting.")))))));
}
