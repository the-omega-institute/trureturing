using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Obstructions;

internal sealed class ErdosMoserLocalObstructionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/PrimeForms/Obstructions/ErdosMoserLocalObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moser's local prime obstruction makes the predecessor of every Erdos-Moser "
            + "solution squarefree.",
        H("The Erdos-Moser Local Prime Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos-moser-local-prime-obstruction"),
                DeclarationHandle.Create(DeclarationPrefix + "erdos_moser_local_obstruction"),
                H("Every prime divisor of the predecessor satisfies Moser's obstruction"),
                StatementSource.FromAuthor(ErdosMoserFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each prime p dividing m - 1, write q for the natural-number "
                            + "quotient (m - 1) / p. The displayed floor notation denotes this "
                            + "integer quotient, never rational division.")),
                    Paragraph(Text(
                        "The proof partitions the power sum into q complete residue blocks in "
                            + "ZMod p, explicitly transports the residue range to ZMod p and then "
                            + "to its unit group, and applies the finite-field power-sum dichotomy. "
                            + "The zero branch is impossible, while the minus-one branch gives "
                            + "p dividing q + 1.")),
                    Paragraph(Text(
                        "If p squared also divided m - 1, exact natural division would make p "
                            + "divide q, contradicting p dividing q + 1. The resulting exclusion "
                            + "for every prime is precisely squarefreeness. No parity assumption "
                            + "on k is used, and no claim is made that the open Erdos-Moser "
                            + "equation has no further solutions."))),
                DescribeRole.Theorem))));

    private static Formula ErdosMoserFormula()
    {
        var m = F.Id("m");
        var k = F.Id("k");
        var p = F.Id("p");
        var naturals = Naturals();
        var mMinusOne = Seq(m, Sp, Minus, Sp, D(1));
        var pMinusOne = Parenthesized(Seq(p, Sp, Minus, Sp, D(1)));
        var quotientPlusOne = Parenthesized(Seq(
            NatDiv(Parenthesized(mMinusOne), p), Sp, Plus, Sp, D(1)));
        var localClauses = Parenthesized(Seq(
            Divides(pMinusOne, k), Sp, Land, Sp,
            Divides(p, quotientPlusOne), Sp, Land, Sp,
            Neg, Sp, Divides(Pow(p, D(2)), Parenthesized(mMinusOne))));
        var localObstruction = Parenthesized(Seq(
            Forall, Sp, p, Sp, InMacro, Sp, naturals, Comma, Esc,
            Call("Prime", p), Sp, Rightarrow, Sp,
            Divides(p, Parenthesized(mMinusOne)), Sp, Rightarrow, Sp,
            localClauses));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, m, Comma, Sp, k, Sp, InMacro, Sp, naturals, Comma),
            Seq(
                D(1), Sp, Lt, Sp, m, Sp, Land, Sp,
                D(0), Sp, Lt, Sp, k, Sp, Land, Sp,
                PowerSum(m, k), Sp, Eq, Sp, Pow(m, k), Sp, Rightarrow),
            Seq(
                localObstruction, Sp, Land, Sp,
                Call("Squarefree", mMinusOne), Dot),
        ]));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula PowerSum(Formula upperBound, Formula exponent) =>
        Seq(
            Sum, Underscore,
            Grp(Seq(F.Id("i"), Sp, InMacro, Sp, Call("range", upperBound))), Sp,
            Pow(F.Id("i"), exponent));

    private static Formula Pow(Formula basis, Formula exponent) =>
        Seq(basis, Caret, Grp(exponent));

    private static Formula Divides(Formula divisor, Formula value) =>
        Seq(divisor, Sp, Mid, Sp, value);

    private static Formula NatDiv(Formula numerator, Formula denominator) =>
        Seq(Lfloor, numerator, Sp, Slash, Sp, denominator, Rfloor);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
