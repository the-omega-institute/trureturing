using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.Bonferroni;

internal sealed class TruncationBoundsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Galambos1977 =
        LibraryNoteRef.Create("D5/L/Diagonal/galambos1977bonferroni");

    public DocumentDefinition Create()
    {
        var address = F.Id("A");
        var b = F.Id("b");
        var f = F.Id("f");
        var m = F.Id("m");
        var q = F.Id("q");
        var r = F.Id("r");
        var set = F.Id("T");
        var y = F.Id("y");
        var qby = Seq(q, Underscore, Grp(b), Open, y, Close);
        var setRange = Grp(set, Subseteq, Sp, address, Comma, Sp,
            Lvert, Sp, set, Sp, Rvert, Eq, Sp, r);
        var degreeRange = Grp(D(0), Leq, Sp, r, Leq, Sp, m);
        var setMass = Call("setCaptureProbability", q, f, set);
        var truncation = Seq(
            Sum, Underscore, degreeRange, Sp,
            Open, Minus, D(1), Close, Caret, r, Sp,
            Sum, Underscore, setRange, Sp, setMass);
        var escape = Call("escapeProbability", q, f);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Every finite Bonferroni truncation bounds weighted escape in the direction determined by its parity.",
            H("Arbitrary-Order Bonferroni Truncation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("arbitrary-order-escape-bonferroni-truncation"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/Bonferroni/TruncationBounds."
                        + "escape_bonferroni_truncation"),
                    H("Alternating truncations bracket escape"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open, Forall, Sp, b, Comma, Sp, y, Comma, Esc,
                        D(0), Leq, Sp, qby, Close, Sp, Rightarrow, Sp,
                        Open,
                        Call("Even", m), Sp, Rightarrow, Sp,
                        escape, Sp, Leq, Sp, truncation,
                        Close, Sp, Land, Sp, Open,
                        Call("Odd", m), Sp, Rightarrow, Sp,
                        truncation, Sp, Leq, Sp, escape,
                        Close, Dot))),
                    AssessedProvenance.FromLiterature(Galambos1977),
                    Blocks(
                        Paragraph(Text(
                            "For each sample, the capture count converts the cardinality-r intersection sum into a binomial coefficient. Mathlib's exact partial alternating-binomial identity leaves a nonnegative binomial coefficient with sign determined by m.")),
                        Paragraph(Text(
                            "Nonnegative sample weights preserve the pointwise inequality. No marginal-normalisation hypothesis is needed, so the theorem also applies to nonnegative finite weights whose total mass is not one."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/BinomialMomentIdentity")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni")),
            ]));
    }
}
