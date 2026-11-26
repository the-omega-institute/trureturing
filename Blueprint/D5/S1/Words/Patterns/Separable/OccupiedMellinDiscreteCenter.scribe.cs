using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedMellinDiscreteCenterDocument : IScribeDocumentDefinition
{
    private static Formula Radius => DeltaLower;
    private static Formula Mesh => F.Id("n");
    private static Formula Width => F.Id("K");
    private static Formula Index => F.Id("i");
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Power(Formula x, Formula exponent) => Seq(x, Caret, Grp(exponent));
    private static Formula SampleAbs(Formula s) =>
        Seq(Left, Lvert, Sp, Call("sample", Beta, Ratio(D(2), Mesh), s), Right, Rvert);
    private static Formula Side(Formula sign) => Seq(
        Sum, Underscore, Grp(D(0), Le, Sp, Index, Lt, Width),
        Sp, SampleAbs(Seq(D(1), sign, Ratio(Seq(Index, Plus, D(1)), Mesh))));
    private static Formula Statement() => Disp(Seq(
        Ratio(Seq(Side(Minus), Plus, SampleAbs(D(1)), Plus, Side(Plus)), Mesh), Le,
        D(5, 6), Sp, Power(Radius, Ratio(D(1), D(4))), Plus,
        D(1, 6), Sp, Power(Mesh, Seq(Minus, Ratio(D(1), D(4))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The shifted Mellin grid has a controlled absolute sum around its central sample.",
        H("The discrete center of the shifted Mellin mesh"),
        Blocks(Describe.Lean(
            DescribeId.Create("shifted-mellin-near-center-cutoff"),
            DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedMellinDiscreteCenter.near_center_cutoff"),
            H("Uniform bound for the symmetric center window"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let n and K be natural numbers, with n positive, and let the real width delta satisfy 0 <= delta <= 1/2 and K/n <= delta. The exponent beta lies in [0,3/4]. The sample is the paired power sample from OccupiedMellinInterior, with actual regularization 2/n.")),
                Paragraph(Text("The two off-center sums run over the positive integer distances i+1 from m=n, once to the left and once to the right. The central term occurs exactly once, even when K is zero; the shift 2/n is retained there. The two sides use monotone integral comparison for the finite negative three-quarter power sum."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
