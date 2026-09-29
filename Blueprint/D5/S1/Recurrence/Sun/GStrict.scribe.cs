using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Sun;

internal sealed class GStrictDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Sun =
        LibraryNoteRef.Create("D5/L/Recurrence/sun2026generalizations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first complete closed-domain clause of Sun's Conjecture 5.2 holds at every positive index.",
        H("Strict Turan Inequality for g"),
        Blocks(Describe.Lean(
            DescribeId.Create("sun-g-strict-turan"),
            DeclarationHandle.Create("D5/S1/Recurrence/Sun/GStrict.g_strict_turan"),
            H("The full g inequality on x at most -1"), StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(Sun),
            Blocks(Paragraph(Text("For every n at least one and every real x at most -1, "
                + "the square of g(x,n) strictly exceeds the product of its two neighbors. "
                + "Put t=-(x+1)/2 and P(k)=(-1)^k g(-2t-1,k). The local recurrence has "
                + "a(k)=k^2 and b(k)=2k(k+1), and positive coefficients exclude adjacent "
                + "zeros. At t=0, GEndpoint supplies strictness. For 0<t<2n, the "
                + "recurrence determinant is a positive quadratic form, with discriminant "
                + "factor t(4n(n+1)-t)>0. On t at least 2n, recurrence uniqueness identifies "
                + "P with the canonical supplier sequence; the direct weighted-tail call "
                + "and weight (n+1)^2/n^2>1 give strictness after splitting the neighbor "
                + "product by sign. Sign transport returns the literal lowercase g claim. "
                + "The endpoint, local range and closed tail cover the entire source domain."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("sun-lowercase-turan-conjecture-52"),
                ResolutionKind.Proved,
                [DeclarationHandle.Create("D5/S1/Recurrence/Sun/VStrict.v_strict_turan")])))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var x = F.Id("x");
        Formula G(Formula index) => new Formula.Apply(F.Id("g"), [x, index]);
        Formula Index(FormulaBinaryOperator op, int offset) =>
            new Formula.Binary(n, op, D((byte)offset));
        var conclusion = new Formula.Relation(new Formula.Power(G(n), D(2)),
            FormulaRelationOperator.GreaterThan,
            new Formula.Binary(G(Index(FormulaBinaryOperator.Subtract, 1)),
                FormulaBinaryOperator.Multiply, G(Index(FormulaBinaryOperator.Add, 1))));
        return Disp(Seq(Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Sp, Le, Sp, n, Sp, Rightarrow, Sp,
            Forall, Sp, x, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            x, Sp, Le, Sp, Minus, D(1), Sp, Rightarrow, Sp, conclusion));
    }
}
