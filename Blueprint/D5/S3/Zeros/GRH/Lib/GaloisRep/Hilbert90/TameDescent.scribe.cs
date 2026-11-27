using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Hilbert90;

internal sealed class TameDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tame Descent", H("Tame Descent"),
        Blocks(
            Paragraph(Text("Hilbert 90 for GL_n and norm surjectivity on units, for a cyclic action at congruence level. The results are stated over Artinian, finite or profinite rings, and also for finite ideles. The action need only be free away from an invariant element m and have an element of trace one modulo m, and the cocycles, coboundaries and units are congruent to 1 modulo m. Source: A. Speiser 1919; J.-P. Serre, Corps locaux, 1962, Ch. X §1 Prop. 3 and Ch. V §2; S. Chase, D. Harrison, A. Rosenberg, Galois theory and Galois cohomology of commutative rings, Mem. AMS 52, 1965; for the norm on O[γ], P. Scholze, The Langlands-Kottwitz approach for some simple Shimura varieties, 2013, Lemma 2.2.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Hilbert90/TameDescent.exists_norm"),
                H("exists_norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If R is finite or profinite, σ^p = 1 with p > 0 and σ is tame at m, every σ-fixed unit x ≡ 1 mod m is the norm zσ(z)⋯σ^{p−1}(z) of a unit z with z, z⁻¹ ≡ 1 mod m.")))))));
}
