using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Shintani;

internal sealed class ShintaniLiftingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shintani Lifting", H("Shintani Lifting"),
        Blocks(
            Paragraph(Text("Occurrence of a parabolically induced character detected on the parabolic (Frobenius reciprocity). Lifted Green character times Steinberg is induced from the base-changed torus. Shintani lifting in prime degree of Green's characters with squarefree labels.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Shintani/ShintaniLifting.shintani_lift_labelChar"),
                H("shintani_lift_labelChar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Shintani lifting: let k'/k be an extension of finite fields of prime degree, T injective and c a label over k. Then Ξ_c lifts by characters (Lift ℕ) to Ξ_c formed over k'.")))))));
}
