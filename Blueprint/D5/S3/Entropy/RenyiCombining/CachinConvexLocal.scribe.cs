using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class CachinConvexLocalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic finite jets supply local signs for the actual Renyi Riccati quotient.",
        H("Local Riccati Signs from the Analytic Quotient"),
        Blocks(
            Describe.Lean(DescribeId.Create("cachin-convex-local-signs"),
                DeclarationHandle.Create("D5/S3/Entropy/RenyiCombining/CachinConvexLocal.C_local_signs"),
                H("Initial signs of the actual first and second derivatives"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    new Formula.Logic(
                        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("n")),
                        FormulaLogicOperator.And,
                        new Formula.Relation(F.Id("n"), FormulaRelationOperator.LessThanOrEqual,
                            new Formula.Fraction(D(1), D(4)))), Sp, Implies, Sp,
                    Exists, Sp, F.Id("delta"), Comma, Sp,
                    new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("delta")), Sp, Land, Sp,
                    Forall, Sp, F.Id("z"), Comma, Sp,
                    new Formula.Relation(F.Id("z"), FormulaRelationOperator.MemberOf,
                        Call("Ioo", D(0), F.Id("delta"))), Sp, Implies, Sp,
                    new Formula.Relation(Call("deriv", Call("C", F.Id("n")), F.Id("z")),
                        FormulaRelationOperator.LessThan, Seq(Minus, F.Id("n"))), Sp, Land, Sp,
                    new Formula.Relation(Call("deriv", Call("deriv", Call("C", F.Id("n"))), F.Id("z")),
                        FormulaRelationOperator.LessThan, D(0))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The analytic quotient Q agrees with C(t^2) for 0<t<1. "
                    + "Its first and third derivatives vanish at zero, while "
                    + "Q''(0)=2(n^2-1)/3 and Q''''(0)=-8(1-n^2)(4-n^2)/15. "
                    + "The bound (n^2+3n-1)/3 <= -1/16 yields Q''(0)<-2n. "
                    + "CachinConvexLimits applies with slope threshold -n, and neighborhood "
                    + "equalities transport both square-root derivative expressions to the actual C. "
                    + "Thus D'=C'+n is negative near zero and C'' is negative there. "
                    + "No derivative of C at zero or asymptotic expansion is assumed."))),
                DescribeRole.Theorem))));
}
