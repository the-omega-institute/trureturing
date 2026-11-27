using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.TwistedHecke;

internal sealed class TwistingDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twisting Data", H("Twisting Data"),
        Blocks(
            Paragraph(Text("Frobenius-twisted circle of letters: action, depth, excess, weight conditions, basic properties.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/TwistedHecke/TwistingData.polyAction_polyOfCoeffs"),
                H("polyAction_polyOfCoeffs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a coefficient vector F, g sends ∑_β F(β) x^β to ∑_β (ρ(g)F)(β) x^β: the matrix ρ(g) = TwistingData.letterRep n g represents the action on forms of degree n in each letter.")))))));
}
