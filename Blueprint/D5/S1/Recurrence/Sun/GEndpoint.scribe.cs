using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Sun;

internal sealed class GEndpointDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Sun =
        LibraryNoteRef.Create("D5/L/Recurrence/sun2026generalizations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A factorial-scaled integer parity invariant makes the g determinant strict at the closed endpoint x=-1.",
        H("Strictness at the g Endpoint"),
        Blocks(Describe.Lean(
            DescribeId.Create("sun-g-endpoint-strict"),
            DeclarationHandle.Create("D5/S1/Recurrence/Sun/GEndpoint.g_endpoint_strict"),
            H("Strict g determinant at x=-1"), StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(Sun),
            Blocks(Paragraph(Text("For every positive n, set P(k)=(-1)^k g(-1,k) "
                + "and Z(k)=(k!)^2 P(k). The recurrence makes Z integral with "
                + "Z(0)=1, Z(1)=0 and Z(k+2)=-2(k+1)(k+2)Z(k+1)-(k+1)^4 Z(k). "
                + "Induction in ZMod 2 shows Z is odd at even indices and even at odd "
                + "indices. Consequently (n+1)Z(n)+n^3 Z(n-1) is odd and nonzero. "
                + "The scaled determinant is the square of the corresponding real "
                + "combination, so it is strictly positive. GStrict consumes this endpoint "
                + "result; no finite-index experiment substitutes for the parity induction."))),
            DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var endpoint = Seq(Minus, D(1));
        Formula G(Formula index) => new Formula.Apply(F.Id("g"), [endpoint, index]);
        Formula Product(Formula a, Formula b) =>
            new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
        return Disp(Seq(Forall, Sp, n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Sp, Le, Sp, n, Sp, Rightarrow, Sp,
            new Formula.Relation(new Formula.Power(G(n), D(2)),
                FormulaRelationOperator.GreaterThan,
                Product(G(new Formula.Binary(n, FormulaBinaryOperator.Subtract, D(1))),
                    G(new Formula.Binary(n, FormulaBinaryOperator.Add, D(1)))))));
    }
}
