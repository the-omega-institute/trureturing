using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedMellinInteriorDocument : IScribeDocumentDefinition
{
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula NodeX(Formula k) => Ratio(k, F.Id("n"));
    private static Formula Sample(Formula shift, Formula x) => Call("sample", Beta, shift, x);
    private static Formula Pow(Formula x, Formula p) => Seq(Open, x, Close, Caret, Grp(p));
    private static Formula Abs(Formula x) => Seq(Left, Lvert, x, Right, Rvert);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit error estimate compares regularized Mellin samples with their unshifted integral.",
        H("Regular blocks of the Mellin mesh"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-mellin-sample"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedMellinInterior.sample"),
                H("Paired regularized power sample"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sample(F.Id("a"), F.Id("s")), Eq,
                    Pow(F.Id("s"), Seq(Minus, Ratio(D(3), D(2)))), Cdot, Open,
                    Pow(Seq(F.Id("a"), Plus, D(1), Plus, F.Id("s")), Seq(Minus, Beta)), Plus,
                    Pow(Seq(F.Id("a"), Plus, Abs(Seq(D(1), Minus, F.Id("s")))), Seq(Minus, Beta)), Minus,
                    D(2), Cdot, Pow(Seq(F.Id("a"), Plus, D(1)), Seq(Minus, Beta)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The parameters beta, a, and s are real. The opposite directions are paired about one before subtraction of the two central values."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("regular-mesh-interior-error"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/OccupiedMellinInterior.normalized_lattice_interior_error"),
                H("Exact lattice comparison on either regular component"),
                StatementSource.FromAuthor(Disp(Seq(
                    Abs(Seq(
                        Int, Underscore, Grp(F.Id("u")), Caret, Grp(F.Id("v")),
                        Sample(D(0), F.Id("s")), Thin, F.Id("ds"), Minus,
                        Ratio(D(1), F.Id("n")), Sum, Underscore,
                        Grp(F.Id("i"), InMacro, Sp, Call("range", F.Id("N"))),
                        Sample(Ratio(D(2), F.Id("n")), NodeX(Seq(F.Id("L"), Plus, F.Id("i")))))),
                    Le, Ratio(Seq(D(1, 6), Cdot, Pow(DeltaLower, Seq(Minus, Ratio(D(1, 7), D(4))))), F.Id("n"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let n, L, and N be natural numbers with n positive, and put u=L/n and v=(L+N)/n in the reals. "
                        + "Assume 0 <= beta <= 3/4, 0 < delta <= 1, delta <= u, and N/n <= 1/delta. "
                        + "Require either v <= 1-delta or 1+delta <= u. The sum runs over 0 <= i < N, and is empty when N=0.")),
                    Paragraph(Text(
                        "On a regular component, the paired derivative is uniformly bounded by a constant times delta to the power -13/4. "
                        + "The mean-value estimate bounds each unshifted left-sampled cell, and a separate comparison in the shift parameter "
                        + "controls replacing zero shift by the exact value 2/n. The interval length bound gives the displayed error."))),
                DescribeRole.Theorem))));
}
