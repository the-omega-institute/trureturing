using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Duality;

internal sealed class ContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contraction", H("Contraction"),
        Blocks(
            Paragraph(Text("A degree-two Ext class between flat functors tensors naturally with every functor. Leray–Hirsch map on Ext groups: degree truncation, long exact ladders, local to global. Coefficient theories on test rings, closed supports, pushforward from zero loci, slices. Semilinear contraction on exterior algebras and its derivation rule.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Duality/Contraction.comp_oneLocConst_surjective"),
                H("comp_oneLocConst_surjective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a coefficient M, pull-back along oneLocConst from total Ext(L, M) to total Ext(ℤ, M) is surjective, where L(c) is the group of locally constant functions Spec g(c) → ℤ/ℓ.")))))));
}
