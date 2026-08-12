using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class BronzeLadderLegDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bronze ladder obeys a Cassini determinant law and lies on the Pell conic 13x^2 - y^2 = pm 4.",
        H("The Cassini and Leg Identities of the Bronze Ladder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bronze-ladder-cassini-and-leg-identities"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/BronzeLadderLeg.bronze_leg"),
                H("The leg identity of the bronze ladder"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("p"), Underscore, D(0), Eq, D(1), Comma, Sp,
                    F.Id("p"), Underscore, D(1), Eq, D(3), Comma, Sp,
                    F.Id("p"), Underscore, Grp(F.Id("n"), Plus, D(2)), Eq,
                    D(3), F.Id("p"), Underscore, Grp(F.Id("n"), Plus, D(1)), Plus,
                    F.Id("p"), Underscore, F.Id("n"), Comma, RowBreak,
                    F.Id("p"), Underscore, F.Id("n"), Sp,
                    F.Id("p"), Underscore, Grp(F.Id("n"), Plus, D(2)), Minus,
                    F.Id("p"), Underscore, Grp(F.Id("n"), Plus, D(1)), Caret, D(2), Eq,
                    Open, Minus, D(1), Close, Caret, F.Id("n"), Comma, RowBreak,
                    D(1), D(3), F.Id("p"), Underscore, Grp(F.Id("n"), Plus, D(1)), Caret, D(2), Minus,
                    Open, D(3), F.Id("p"), Underscore, Grp(F.Id("n"), Plus, D(1)), Plus,
                    D(2), F.Id("p"), Underscore, F.Id("n"), Close, Caret, D(2), Eq,
                    D(4), Open, Minus, D(1), Close, Caret, Grp(F.Id("n"), Plus, D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The bronze ladder p is the integer sequence p 0 = 1, p 1 = 3, "
                        + "p (n+2) = 3 p(n+1) + p n, whose k-th term is the top-left entry of the k-th "
                        + "power of the crossing matrix [[3,1],[1,0]] of trace 3 and determinant -1 — "
                        + "the square-root-of-13 analogue of the Fibonacci and Pell ladders.")),
                    Paragraph(Text(
                        "Two identities hold for every n. The Cassini identity "
                        + "p n * p(n+2) - p(n+1)^2 = (-1)^n has right side (det T)^n = (-1)^n for the "
                        + "crossing matrix of determinant -1 (the left side is det of T^(n+2)); it is "
                        + "proved by induction. The leg identity evaluates the indefinite binary form "
                        + "13 x^2 - y^2 at the ladder point (x,y) = (p(n+1), 3 p(n+1) + 2 p n) and "
                        + "returns 4 (-1)^(n+1), so every ladder point lies on the Pell conic "
                        + "13 x^2 - y^2 = +-4; that value is minus four times the Cassini value (-1)^n, "
                        + "hence a one-line consequence of it.")),
                    Paragraph(Text(
                        "Only the ladder's arithmetic core — the Cassini determinant law and this leg "
                        + "identity — is recorded here. The geometric crossing (1,2,3^k) = M T^k, the "
                        + "spectral four-accumulation limit of the crossing angles, and the wider "
                        + "narrative clauses of the source are not covered by these statements."))),
                DescribeRole.Theorem))));
}
