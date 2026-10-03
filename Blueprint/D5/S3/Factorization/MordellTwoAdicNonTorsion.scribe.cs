using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class MordellTwoAdicNonTorsionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/MordellTwoAdicNonTorsion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative binary X-valuation forces infinite order on the smooth locus of an integral Mordell model.",
        H("Binary Valuation Descent on Mordell Curves"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integral-mordell-model"),
                DeclarationHandle.Create(Prefix + "mordellCurve"),
                H("The integral Mordell model"),
                StatementSource.FromAuthor(Disp(Seq(
                    new Formula.Subscript(F.Id("E"), F.Id("b")), Sp, Colon, Sp,
                    new Formula.Power(F.Id("Y"), D(2)), Sp, Eq, Sp,
                    Add(new Formula.Power(F.Id("X"), D(3)), F.Id("b"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Weierstrass coefficients are zero except for a6=b, with b an integer. "
                    + "At b=0 the model is singular; the theorem below concerns only its "
                    + "nonsingular affine points."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("negative-binary-x-valuation-has-infinite-order"),
                DeclarationHandle.Create(Prefix + "infinite_add_order_of_negative_two_adic_x"),
                H("Negative binary X-valuation forces infinite order"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("b"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    F.Id("P"), Sp, InMacro, Sp,
                    new Formula.Power(new Formula.Subscript(F.Id("E"), F.Id("b")),
                        Grp(F.Id("sm"), Comma, F.Id("aff"))),
                    Open, Mathbb, Grp(F.Id("Q")), Close, Comma, Sp,
                    new Formula.Subscript(F.Id("v"), D(2)),
                    Open, F.Id("X"), Open, F.Id("P"), Close, Close,
                    Sp, Lt, Sp, D(0), Sp, Rightarrow, Sp,
                    new Formula.Not(Seq(F.Id("FiniteAddOrder"), Open, F.Id("P"), Close))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any nonsingular affine rational point with v2(X)<0, the duplication "
                        + "formula and the integrality of b give v2(X(2P))=v2(X(P))-2. "
                        + "The same calculation applies to every subsequent double, yielding "
                        + "pairwise distinct points and therefore infinite additive order.")),
                    Paragraph(Text(
                        "An integral point with odd X and nonzero even Y has a double with "
                        + "negative binary X-valuation. The next theorem proves this first "
                        + "doubling step. Point construction and distinct twist classes are "
                        + "separate claims."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unit-x-positive-binary-y-valuation-has-infinite-order"),
                DeclarationHandle.Create(Prefix + "infinite_add_order_of_unit_x_positive_two_adic_y"),
                H("Unit X and positive binary Y-valuation force infinite order"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("b"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    F.Id("P"), Sp, InMacro, Sp,
                    new Formula.Power(new Formula.Subscript(F.Id("E"), F.Id("b")),
                        Grp(F.Id("sm"), Comma, F.Id("aff"))),
                    Open, Mathbb, Grp(F.Id("Q")), Close, Comma, Sp,
                    F.Id("X"), Open, F.Id("P"), Close, Sp, Neq, Sp, D(0), Sp, Land, Sp,
                    new Formula.Subscript(F.Id("v"), D(2)),
                    Open, F.Id("X"), Open, F.Id("P"), Close, Close,
                    Sp, Eq, Sp, D(0), Sp, Land, Sp, D(0), Sp, Lt, Sp,
                    new Formula.Subscript(F.Id("v"), D(2)),
                    Open, F.Id("Y"), Open, F.Id("P"), Close, Close,
                    Sp, Rightarrow, Sp,
                    new Formula.Not(Seq(F.Id("FiniteAddOrder"), Open, F.Id("P"), Close))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nonzero X condition excludes the zero abscissa, whose binary "
                    + "valuation is also zero by convention. The tangent calculation gives "
                    + "v2(X(2P))=-2-2v2(Y(P))<0. The preceding theorem then proves that "
                    + "the double, and therefore the original point, has infinite order."))),
                DescribeRole.Theorem))));
}
