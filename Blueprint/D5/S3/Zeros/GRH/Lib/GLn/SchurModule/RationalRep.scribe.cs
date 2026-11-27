using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.SchurModule;

internal sealed class RationalRepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational Rep", H("Rational Rep"),
        Blocks(
            Paragraph(Text("Rational representation of a product of GL_n on Weyl's lattice, twisted by determinants.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/SchurModule/RationalRep.weylRep"),
                H("weylRep"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The monoid homomorphism from ∏_τ GL(n_τ,R) to square matrices sending g to ∏_τ det(g_τ)^{e_τ} times the Schur matrix of g, for integers e_τ.")))))));
}
