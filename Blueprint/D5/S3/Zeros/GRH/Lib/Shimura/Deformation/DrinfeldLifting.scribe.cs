using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Deformation;

internal sealed class DrinfeldLiftingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Drinfeld Lifting", H("Drinfeld Lifting"),
        Blocks(
            Paragraph(Text("Linear functions on w-torsion with zero differential span at most n-1 dimensions. Absolute Frobenius of a scheme; pull-back of line bundles is a power. Drinfeld's lifting lemma for first-order deformations of the abelian object.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Deformation/DrinfeldLifting.drinfeld_lift"),
                H("drinfeld_lift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Drinfeld's lifting lemma. Let x, x' deform x₀ over k[ε], and let c in O_E kill all infinitesimal points of A_x'. Then some homomorphism F: A_x → A_x' reduces to c, and F(y) = c·y' whenever y and y' agree modulo ε.")))))));
}
