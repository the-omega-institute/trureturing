using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class WeilSmallSupportCoerciveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Separator/WeilSmallSupportCoercive.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completed-zeta gamma jump gives a mass margin on the fixed small support. "
            + "The explicit formula transfers the margin to the Weil square with its full boundary term.",
        H("Small-support Weil coercivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("small-support-gamma-coercive"),
                DeclarationHandle.Create(Prefix + "smallSupport_gamma_coercive"),
                H("Coercivity of the gamma term"),
                StatementSource.FromAuthor(GammaStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A shift above 1/20 confines the overlap to opposite half-intervals. "
                            + "The bound on twice the real cross term by the two half-interval masses "
                            + "leaves at least one full mass in the translation energy. "
                            + "A shift above 1/10 makes the supports disjoint and leaves two masses.")),
                    Paragraph(Text(
                        "The first 24 exponential terms of the jump density give a joint lower bound "
                            + "of 277/50 on the integrals over the two tails. The first twelve "
                            + "nonnegative digamma terms give a correction of at least 329/1000. "
                            + "Together with the Euler–Mascheroni and log pi bounds this places the "
                            + "constant at or above −549/100 and leaves a margin of 1/20."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("small-support-weil-positive"),
                DeclarationHandle.Create(Prefix + "smallSupport_weil_positive"),
                H("Weil lower bound with the boundary contribution"),
                StatementSource.FromAuthor(WeilStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At this support scale the exponential cutoff lies below two, so the active "
                        + "prime-power set is empty. The unconditional energy identity then gives "
                        + "the full boundary contribution plus the gamma margin for every zero "
                        + "presentation and every test supported in the stated interval."))),
                DescribeRole.Theorem)),
        []));

    private static Formula GammaStatement()
    {
        Formula f = F.Id("f");
        Formula gamma = Add(
            Multiply(Seq(Operatorname, Grp(F.Id("archimedeanConstant"))), Call("l2Mass", f)),
            Call("archimedeanJumpEnergy", f));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("f", F.Id("WeilTestFunction")), Bound("hSupport", Support(f))],
            Le(Margin(f), gamma)));
    }

    private static Formula WeilStatement()
    {
        Formula f = F.Id("f");
        Formula z = F.Id("Z");
        Formula x = F.Id("x");
        Formula square = Call("convolutionSquare", f);
        Formula witness = Call("symmetricConvergentOfZeroData", z, square);
        Formula integrand = Multiply(Call("exp", new Formula.Fraction(x, D(2))), Call("f", x));
        Formula integral = Seq(Int, Underscore, Grp(Seq(Mathbb, Grp(F.Id("R")))), Sp,
            integrand, Sp, F.Id("d"), x);
        Formula boundary = Multiply(D(2), Call("normSq", integral));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [
                Bound("Z", F.Id("ZeroData")),
                Bound("f", F.Id("WeilTestFunction")),
                Bound("hSupport", Support(f)),
            ],
            Le(Add(boundary, Margin(f)), Call("realPart", Call("zeroSum", z, square, witness)))));
    }

    private static Formula Radius() => new Formula.Fraction(D(1), D(2, 0));

    private static Formula Support(Formula f) => new Formula.Relation(
        Call("tsupport", f), FormulaRelationOperator.SubsetOf,
        Seq(OpenBracket, Seq(Minus, Radius()), Comma, Sp, Radius(), CloseBracket));

    private static Formula Margin(Formula f) => Multiply(Radius(), Call("l2Mass", f));

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
