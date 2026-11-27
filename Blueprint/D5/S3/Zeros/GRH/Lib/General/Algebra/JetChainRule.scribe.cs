using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class JetChainRuleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jet Chain Rule", H("Jet Chain Rule"),
        Blocks(
            Paragraph(Text("General lemmas of commutative and general algebra (textbook or folklore).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/JetChainRule.jet_subst_linearSeries"),
                H("jet_subst_linearSeries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Chain rule for a linear substitution: for a matrix M, the jet along P of F(Mz) equals the jet of F along the polynomial P(Mᵀx).")))))));
}
