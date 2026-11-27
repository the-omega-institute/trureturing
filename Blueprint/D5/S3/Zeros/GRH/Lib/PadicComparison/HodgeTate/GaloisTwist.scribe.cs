using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.HodgeTate;

internal sealed class GaloisTwistDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Galois Twist", H("Galois Twist"),
        Blocks(
            Paragraph(Text("For smooth spaces, forgetting first-order lifts of points preserves cohomology. Galois twist of p-adic tests scales μ by the cyclotomic character, preserves contraction class.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/GaloisTwist.pairRestrictBijective"),
                H("pairRestrictBijective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a field k mapping to Q̄_p, if every field-valued point of X lies in a chart with étale coordinates, then ℤ[X] satisfies PairRestrictBijective.")))))));
}
