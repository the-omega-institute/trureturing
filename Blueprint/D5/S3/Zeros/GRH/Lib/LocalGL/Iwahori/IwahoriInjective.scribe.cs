using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Iwahori;

internal sealed class IwahoriInjectiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Iwahori Injective", H("Iwahori Injective"),
        Blocks(
            Paragraph(Text("Conjugation of parahorics by monomial matrices; quadratic relation of the Iwahori Hecke algebra. Some strictly dominant U-operator is injective; values of exponents on monomial translates.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/IwahoriInjective.apply_monomial_translate"),
                H("apply_monomial_translate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let (ξ, l) be an exponent, y fixed by a group containing the elements of the parahoric of c with diagonal ≡ 1 mod ϖ. Then l(ρ(t)ρ(σ)y) = ξ(t) l(ρ(σ)y) if σb < σa implies |t_{σb}| ≤ |t_{σa}|, or c(a) ≤ c(b) and |ϖt_{σb}| ≤ |t_{σa}|.")))))));
}
