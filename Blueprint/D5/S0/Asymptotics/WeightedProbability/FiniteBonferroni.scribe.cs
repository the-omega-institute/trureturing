using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class FiniteBonferroniDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Galambos1977 =
        LibraryNoteRef.Create("D5/L/Diagonal/galambos1977bonferroni");

    public DocumentDefinition Create()
    {
        var a = F.Id("a");
        var ap = Seq(a, Apos);
        var b = F.Id("b");
        var y = F.Id("y");
        var qby = Seq(F.Id("q"), Underscore, Grp(b), Open, y, Close);
        var capture = Call("captureProbability", F.Id("q"), F.Id("f"), a);
        var pair = Call("pairCaptureProbability", F.Id("q"), F.Id("f"), a, ap);
        var escape = Call("escapeProbability", F.Id("q"), F.Id("f"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Nonnegative normalized finite capture events satisfy the first- and second-order escape bounds.",
            H("Finite Bonferroni Escape Bounds"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("two-sided-weighted-escape-bounds"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni."
                        + "escape_bonferroni_bounds"),
                    H("Two-sided weighted escape bounds"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open,
                        Forall, Sp, b, Comma, Sp, y, Comma, Esc,
                        D(0), Leq, Sp, qby,
                        Sp, Land, Sp,
                        Forall, Sp, b, Comma, Esc,
                        Sum, Underscore, Grp(y), Sp, qby, Sp, Eq, Sp, D(1), Close,
                        Sp, Rightarrow, Sp,
                        D(1), Minus, Sum, Underscore, Grp(a), Sp, capture,
                        Sp, Leq, Sp, escape, Sp, Leq, Sp,
                        D(1), Minus, Sum, Underscore, Grp(a), Sp, capture, Plus,
                        Sum, Underscore, Grp(a, Lt, ap), Sp, pair, Dot))),
                    AssessedProvenance.FromLiterature(Galambos1977),
                    Blocks(
                        Paragraph(Text(
                            "The pointwise union and second-order Bonferroni inequalities are multiplied by nonnegative sample weights and summed.")),
                        Paragraph(Text(
                            "The strict order writes each unordered pair exactly once."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/FiniteProductPairCapture")),
            ]));
    }
}
