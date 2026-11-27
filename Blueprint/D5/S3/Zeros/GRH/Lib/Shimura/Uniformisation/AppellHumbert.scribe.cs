using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Uniformisation;

internal sealed class AppellHumbertDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Appell Humbert", H("Appell Humbert"),
        Blocks(
            Paragraph(Text("complex uniformisation of PEL abelian varieties, Appell–Humbert and finite class number. Here the signature is (1,n-1) at one place and definite elsewhere. The torus comes from the exponential of a compact commutative complex Lie group, and Appell–Humbert is proved only for a very ample class obeying the parallelogram law. Source: J. S. Milne, Introduction to Shimura Varieties (2005/2017), Theorem 8.17 and Lemma 5.12; R. Kottwitz, Points on some Shimura varieties over finite fields, J. AMS 5 (1992) §8; G. Shimura, On analytic families of polarized abelian varieties and automorphic functions, Ann. Math. 78 (1963); A. Borel, Some finiteness properties of adele groups over number fields, Publ. IHES 16 (1963); D. Mumford, Abelian Varieties §§1–2; L. Breen, Fonctions thêta et théorème du cube, LNM 980 (1983).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Uniformisation/AppellHumbert.appell_humbert"),
                H("appell_humbert"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Appell–Humbert theorem: if V/L ≅ A(ℂ) is a uniformisation and N a projective embedding of A whose class is symmetric and satisfies the parallelogram law Pic.ParallelogramLaw, the coordinates of N are theta functions for L of some type (B, χ) with positive Riemann form.")))))));
}
