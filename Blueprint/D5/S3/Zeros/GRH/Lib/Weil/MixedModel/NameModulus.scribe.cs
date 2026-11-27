using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class NameModulusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Name Modulus", H("Name Modulus"),
        Blocks(
            Paragraph(Text("Moduli prime to their conjugate; theta kernel of a polynomial and function modulo m. Reduction of integral adeles modulo m, lifted functions, primitive additive character modulo m.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/NameModulus.name_char_eq_translate_projOn"),
                H("name_char_eq_translate_projOn"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let S be the places dividing 𝔪, u in Ô^n, Ψ(x) = ψ′(∑ xᵢuᵢ) modulo 𝔪, ψ′ = Modulus.primAddChar. Then Ψ⊗f = ϱ(αb̄)P^S f for all f, where b is the part above S of 𝗆⁻¹u, 𝗆 = Modulus.generator.")))))));
}
