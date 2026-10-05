using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class ReferenceReserveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reference harmonic-prefix objective bounds the actual prime optimizer reserve.",
        H("Reference Prime Reserve"),
        Blocks(
            Paragraph(Text("For x > 1 let lambda_x = 1/(x log x) and v_p = floor(log x/log p). "
                + "The reference objective is Q_a(1/p) - lambda_x a log p, where Q_a is the "
                + "harmonic power prefix. The actual objective is the existing geometric-prefix "
                + "logarithm minus the same cost. The reserve R_p(x) is the reference value "
                + "at v_p less the supremum of the actual objective over all natural exponents. "
                + "On nonprime indices the reserve is zero. Thus its value makes no choice "
                + "among tied maximizers.")),
            Describe.Lean(
                DescribeId.Create("reference-prime-reserve-bounds"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenResource/ReferenceReserve.result"),
                H("Local reserve bounds"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The k-th reference increment is nonnegative exactly when "
                    + "p^k <= x: after multiplying positive denominators this is the monotonicity "
                    + "of y log y. Hence v_p maximizes the reference objective. The finite-prefix "
                    + "logarithm is at most the harmonic prefix, so the actual supremum is no larger "
                    + "than the reference maximum. Evaluating the actual objective at v_p gives "
                    + "the upper bound by D_(v_p)(1/p)."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula x = F.Id("x");
        Formula p = F.Id("p");
        Formula reserve = new Formula.Apply(F.Id("reserve"), [x, p]);
        Formula exponent = new Formula.Apply(F.Id("referenceExponent"), [x, p]);
        Formula deficit = new Formula.Apply(F.Id("D"), [exponent, new Formula.Fraction(D(1), p)]);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, x, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
                Sp, D(1), Sp, Lt, Sp, x, Sp, Rightarrow),
            Seq(Forall, Sp, p, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
                Sp, new Formula.Apply(F.Id("Prime"), [p]), Sp, Rightarrow),
            Seq(D(0), Sp, Le, Sp, reserve, Sp, Le, Sp, deficit)
        ]));
    }
}
