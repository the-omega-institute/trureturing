using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletRampPrimeTailDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/DirichletRampPrimeTail.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mod-four square-layer correction",
        H("Square-root limits for the nonprime Mangoldt contribution"),
        Blocks(
            Paragraph(Text("For a real cutoff x, HChi(x) sums Λ(n)χ₄(n) over the nonprime positive integers "
                + "at most x. The character χ₄ takes values 0 on even integers, 1 on the residue class 1, "
                + "and −1 on the residue class 3 modulo four.")),
            Describe.Lean(DescribeId.Create("mod-four-nonprime-root-limit"),
                DeclarationHandle.Create(Module + "HChi_root_limit"),
                H("The nonprime Mangoldt sum"),
                StatementSource.FromAuthor(RootLimit()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every odd prime square has character value 1, and the square of 2 has "
                        + "character value 0. For x ≥ 4, the weighted square layer is θ(√x) − log 2. "
                        + "The absolute remainder is bounded by ψ(x) − θ(x) − θ(√x). After division by √x, "
                        + "the remainder tends to zero and θ(√x)/√x tends to one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mod-four-ramp-tail-root-limit"),
                DeclarationHandle.Create(Module + "HChi_ramp_tail_root_limit"),
                H("The integrated ramp correction"),
                StatementSource.FromAuthor(RampTailLimit()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The integral uses Lebesgue measure over t > x. The bound "
                        + "|HChi(t)| ≤ ψ(t) − θ(t) gives an integrable majorant after division by t² on t > 1. "
                        + "The first limit bounds HChi(t) between arbitrarily close multiples of √t on a "
                        + "sufficiently far tail. Integrating √t/t² over t > x gives 2/√x."))),
                DescribeRole.Theorem))));

    private static Formula RootLimit()
    {
        var x = F.Id("x");
        return Limit(x, HChi(x), 1);
    }

    private static Formula RampTailLimit()
    {
        var x = F.Id("x");
        var t = F.Id("t");
        var integrand = new Formula.Fraction(HChi(t), F.Seq(t, F.Caret, F.Grp(F.D(2))));
        var tail = F.Seq(F.Int, F.Underscore, F.Grp(t, F.Gt, x),
            F.Sp, integrand, F.Thin, F.Id("d"), F.Sp, t);
        return Limit(x, F.Seq(x, F.Thin, tail), 2);
    }

    private static Formula Limit(Formula x, Formula numerator, byte value) =>
        F.Disp(new Formula.Relation(
            F.Seq(F.Lim, F.Underscore, F.Grp(x, F.To, F.Sp, F.Plus, F.Infty), F.Sp,
                new Formula.Fraction(numerator, F.Seq(F.Sqrt, F.Grp(x)))),
            FormulaRelationOperator.Equal, F.D(value)));

    private static Formula HChi(Formula x) =>
        new Formula.FunctionCall(FormulaIdentifier.Create("HChi"), [x]);
}
