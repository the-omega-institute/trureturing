using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class A331474HankelGeneratingFunctionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Oeis =
        LibraryNoteRef.Create("D5/L/Recurrence/barry2020a331474");
    private static readonly LibraryNoteRef CatalanFamily =
        LibraryNoteRef.Create("D5/L/Recurrence/bojicicpetkovicbarry2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual determinant sequence from the literal A331473 moments has Barry's "
            + "conjectured rational generating function.",
        H("A331474 Hankel Generating Function"),
        Blocks(Describe.Lean(
            DescribeId.Create("a331474-hankel-generating-function"),
            DeclarationHandle.Create(
                "D5/S3/Constants/Moments/A331474HankelGeneratingFunction."
                    + "a331474_hankel_generating_function"),
            H("The complete literal Hankel generating function"),
            StatementSource.FromAuthor(GeneratingFunctionFormula()),
            AssessedProvenance.FromRepo(Oeis, CatalanFamily),
            Blocks(
                Paragraph(Text(
                    "Here H is the determinant-defined sequence from the bridge module, and "
                        + "PowerSeries.mk H is the formal power series whose coefficient at n "
                        + "is that actual determinant. The denominator (1+7x^2+x^4)^2 has "
                        + "constant coefficient 1, so invOfUnit with witness 1 is defined.")),
                Paragraph(Text(
                    "The signed kernel bridge reduces H to scalar continuants. Parity gives "
                        + "p(2m)=1 and p(2m+1)=-4(m+1), while U(m)=u(2m) satisfies "
                        + "U(0)=1, U(1)=1, U(2)=7 and U(m+1)=7U(m)-U(m-1) for m at least 2. "
                        + "These identities give one recurrence for every H(n) from n=8 onward; "
                        + "the n=8 and n=9 closures are derived from the bridge, not accepted as "
                        + "a large finite verification.")),
                Paragraph(Text(
                    "The first ten values derived along that scalar route are "
                        + "1, 3, 2, -50, -43, 535, 487, -4983, -4654, 43174. Coefficientwise "
                        + "multiplication by the squared denominator uses those initial values "
                        + "below order 8 and the all-order recurrence thereafter. Thus every "
                        + "coefficient of the denominator product equals the displayed numerator. "
                        + "Multiplication by the unit inverse yields the full formal identity, "
                        + "not merely agreement of a finite prefix.")),
                Paragraph(Text(
                    "OEIS revision 9 attributes the conjectured scalar formula to Paul Barry. "
                        + "The proof is repo-derived. The cited 2025 three-consecutive-Catalan "
                        + "families do not subsume this literal source: matching its first two "
                        + "coefficients makes those formulas predict 9 or 10 for the third, "
                        + "whereas the literal source has 12."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a331474-hankel-generating-function"),
                ResolutionKind.Proved)))));

    private static Formula Parenthesized(params Formula[] value) => Seq([Open, .. value, Close]);
    private static Formula Power(Formula value, byte exponent) => new Formula.Power(value, D(exponent));

    private static Formula GeneratingFunctionFormula()
    {
        Formula x = F.Id("x");
        Formula numerator = Seq(
            D(1), Sp, Plus, Sp, D(3), x, Sp, Plus, Sp, D(1, 6), Power(x, 2),
            Sp, Minus, Sp, D(8), Power(x, 3), Sp, Plus, Sp, D(3, 6), Power(x, 4),
            Sp, Minus, Sp, D(1, 2), Power(x, 5), Sp, Plus, Sp, Power(x, 6),
            Sp, Minus, Sp, Power(x, 7));
        Formula denominator = Power(Parenthesized(
            D(1), Sp, Plus, Sp, D(7), Power(x, 2), Sp, Plus, Sp, Power(x, 4)), 2);
        Formula inverse = new Formula.FunctionCall(
            FormulaIdentifier.Create("invOfUnit"), [denominator, D(1)]);
        return Disp(Seq(
            Operatorname, Grp(F.Id("PowerSeries")), Dot, Operatorname, Grp(F.Id("mk")),
            Open, F.Id("H"), Close, Sp, Eq, Sp, Parenthesized(numerator), Sp, inverse));
    }
}
