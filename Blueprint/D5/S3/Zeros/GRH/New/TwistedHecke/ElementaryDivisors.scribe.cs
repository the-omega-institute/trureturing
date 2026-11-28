using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.TwistedHecke;

internal sealed class ElementaryDivisorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elementary Divisors", H("Elementary Divisors"),
        Blocks(
            Paragraph(Text("Twisted Hecke operator has small elementary divisors; approximate projector; Smith form of ends.")),
            Describe.Lean(
                DescribeId.Create("twisted-hecke-pairing-capped-full-minor"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/TwistedHecke/ElementaryDivisors.of_pairing_capped_minor"),
                H("A capped full minor from the pairing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The residue-space dimension bounds the number of retained Smith indices. "
                    + "The corresponding correction factors through those indices, so the block determinant "
                    + "construction gives a nonzero full column minor of the capped pairing matrix. "
                    + "Its determinant divides the scalar pairing budget."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/TwistedHecke/ElementaryDivisors.hasType_twisted_hecke"),
                H("hasType_twisted_hecke"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Elementary divisors of the twisted Hecke operator (AF)(c) = ∑_b (u_e ⊗ (ρ(g_e) p^{depth} ρ(γ_b))ᵀ) F(src e), e = (c,b), the γ_b representing the cosets 𝒫γ of the parahoric. Assume p is a non-unit, HeckeSizes, and e ↦ (src e, 𝒫g_eᵀ) injective. If Yf = fA, then Y has type (z + κm + y)|X||I| at m on im f (HasType: Y preserves M = im f, and YM + p^m M has index dividing p^l for some l at most this number).")))))));
}
