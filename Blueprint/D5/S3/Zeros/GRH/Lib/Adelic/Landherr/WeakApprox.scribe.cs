using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Landherr;

internal sealed class WeakApproxDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak Approx", H("Weak Approx"),
        Blocks(
            Paragraph(Text("Weak approximation for unitary groups over CM fields by a Cayley-type transform.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Landherr/WeakApprox.weak_approximation"),
                H("weak_approximation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Weak approximation for U(J): for a finite set S of finite places, a neighbourhood O of 1 in G and g in G, some rational γ has γg = hu with u in O and h in G_f trivial at S.")))))));
}
