using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Analysis;

internal sealed class FundamentalDomainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fundamental Domain", H("Fundamental Domain"),
        Blocks(
            Paragraph(Text("Fourier inversion and uniqueness on a compact abelian quotient, via Stone-Weierstrass. Mean over compact quotient equals fundamental-domain average; unfolding of sums over a lattice. Bounded fundamental domain for a number field in adeles, with its volume.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Analysis/FundamentalDomain.exists_fundDomain_prod"),
                H("exists_fundDomain_prod"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let j = (j₁, j₂): I → V×W be additive on the number field I, j₁ the Minkowski embedding up to a measure-preserving isomorphism, j₂⁻¹(O) = J, W = j₂(I) + O. Then F×O is a strict fundamental domain for some bounded measurable F of volume N(J)2^(−r₂)√|disc I|.")))))));
}
