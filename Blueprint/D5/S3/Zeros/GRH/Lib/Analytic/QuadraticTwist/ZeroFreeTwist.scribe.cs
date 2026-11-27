using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Analytic.QuadraticTwist;

internal sealed class ZeroFreeTwistDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero Free Twist", H("Zero Free Twist"),
        Blocks(
            Paragraph(Text("Some prime in a class has quadratic twists zero-free on a half-strip; three lines.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Analytic/QuadraticTwist/ZeroFreeTwist.exists_entireL_quadTwist_ne_zero"),
                H("exists_entireL_quadTwist_ne_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let β > 1/2, y real, and a a unit mod N whose primes are ≡ 7 mod 8 and prime to N. For some prime d ≡ a, no L̃(s, ξ·(·/d)), ξ mod N, vanishes on re s ≥ β, |im s| ≤ y; L̃ is entireL.")))))));
}
