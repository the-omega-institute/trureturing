using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedActualPowerGeneratorDocument : IScribeDocumentDefinition
{
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Parens(Formula x) => Seq(Left, Open, x, Right, Close);
    private static Formula Pow(Formula x, Formula p) => Seq(x, Caret, Grp(p));
    private static Formula Abs(Formula x) => Seq(Left, Lvert, Sp, x, Right, Rvert);
    private static Formula A => F.Id("A");
    private static Formula C => F.Id("C");
    private static Formula I => F.Id("i");
    private static Formula N => F.Id("n");
    private static Formula U => F.Id("u");
    private static Formula Z => F.Id("z");
    private static Formula Half => Ratio(D(1), D(2));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Profile => Seq(F.Id("p"), Underscore, Grp(Beta));
    private static Formula Generator(Formula u, Formula z) => Seq(
        Mathcal, Grp(F.Id("D")), Underscore, Grp(Kappa), Parens(Seq(u, Comma, z)));
    private static Formula At(Formula x) => Seq(U, Open, x, Close);
    private static Formula Rate => Seq(C, Cdot, Sp, Pow(N, Seq(Minus, Ratio(D(1), D(8, 0)))));
    private static Formula Scaled => Seq(Pow(N, Seq(Beta, Plus, Half)), Cdot, Sp, Generator(Profile, N));

    private static Formula Estimate() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Exists, Sp, A, Comma, C, InMacro, Sp, Reals, Comma, Sp, D(0), Lt, A, Sp, Land, Sp,
        D(0), Le, Sp, C, Sp, Land, RowBreak, Grp(),
        Open, Forall, Sp, Beta, InMacro, Sp, Reals, Comma, Sp, N, InMacro, Sp, Naturals, Comma, RowBreak, Grp(),
        Half, Le, Beta, Le, Ratio(D(3), D(4)), Sp, Land, Sp, Pow(D(4), D(2, 0)), Le, Sp, N,
        Longrightarrow, RowBreak, Grp(),
        Abs(Seq(Scaled, Minus, A, Cdot, Sp, F.Id("J"), Open, Beta, Close)), Le, Sp, Rate,
        Sp, Land, RowBreak, Grp(),
        A, Cdot, Sp, F.Id("c"), Cdot, Sp, Parens(Seq(Beta, Minus, Half)), Minus, Rate, Le, Sp, Scaled, Close,
        End, Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual compensated generator has a scaled comparison with the signed Mellin integral.",
        H("Actual integer power generator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shifted-integer-power-profile"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator.powerProfile"),
                H("Shifted inverse power on the integers"),
                StatementSource.FromAuthor(Disp(Seq(Profile, Open, Z, Close, Eq,
                    Pow(Parens(Seq(D(2), Plus, Abs(Z))), Seq(Minus, Beta))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The position z is an integer, read as a real inside the absolute value; beta is real."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-compensated-generator"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator.actualGenerator"),
                H("Compensated generator with the actual weights"),
                StatementSource.FromAuthor(Disp(Seq(
                    Generator(U, Z), Eq, Sum, Underscore, Grp(I, Eq, D(0)), Caret, Grp(Infty),
                    Kappa, Underscore, Grp(I), Cdot, Sp,
                    Parens(Seq(At(Seq(Z, Plus, Parens(Seq(I, Plus, D(1))))), Plus,
                        At(Seq(Z, Minus, Parens(Seq(I, Plus, D(1))))), Minus, D(2), Cdot, Sp, At(Z)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function u maps integers to reals. The weight at index i is the occupation kernel's "
                    + "actual weight for jump size i+1, including its singleton term. The series is the real infinite sum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-generator-comparison-and-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/OccupiedActualPowerGenerator.actual_generator_power_comparison"),
                H("Uniform signed discrepancy and lower bound"),
                StatementSource.FromAuthor(Estimate()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The same two constants work for both inequalities, for every allowed exponent and mesh size. "
                        + "All powers of n are taken in the reals and the generator is evaluated at n as an integer. "
                        + "Here J is the signed whole-line Mellin integral and c is its fixed positive Kelvin coefficient.")),
                    Paragraph(Text(
                        "The half-line integral separates into two affine rays of the signed whole-line kernel. "
                        + "After normalizing the mesh, the leading power weight gives the integral term and the "
                        + "summable weight replacement gives an error. The Kelvin gap yields the one-sided bound."))),
                DescribeRole.Theorem))));
}
