using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class TriangleLevelExponentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle Level Exponent", H("Triangle Level Exponent"),
        Blocks(
            Paragraph(Text("Integrality of the lift; integral group-ring element interpolating tame twists of L-values. Normalised squared norm of a character's theta lift is constant times Hecke L-value. Exchange constant for a twist rewritten through L-value ratios and conductor norms. Spaces and characters of the triangle of lifts.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/TriangleLevelExponent.lValueProd_eq"),
                H("lValueProd_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Π be lValueProd, (ν, z) a pair, ϑ tame of modulus Q, s = ±1. Then Π(z) for (νϑ^s)⁻¹ away from the chosen places and Q is N(Q)^{z²} times Π(z) for ν⁻¹ away from the chosen places times ∏_{1≤z'≤z} ρ_{z'}², ρ_{z'} the L-value ratio Data.Pair.ratio.")))))));
}
