using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class HeckeStringDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hecke String", H("Hecke String"),
        Blocks(
            Paragraph(Text("Weak lifts: Hecke polynomial is the string times a factor integral after normalising.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/HeckeString.eventually_heckePoly_eq_string_mul"),
                H("eventually_heckePoly_eq_string_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let the normalised representation u of an eigenform have integral characteristic polynomials, all with root 1. At generic geometric Frobenii σ (mostFrobenii): if char u(σ) ≡ S·∏_{i<n−r}(X − cyc(σ)^{−i}) with ‖S(1)‖ ≥ 1, the rescaled Hecke polynomial is ∏_{i<n−r}(X − q^i)·T, and ιT divides an integral e with e(1) = 1.")))))));
}
