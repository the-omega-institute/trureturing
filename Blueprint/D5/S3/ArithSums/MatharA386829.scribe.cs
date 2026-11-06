using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class MatharA386829Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/MatharA386829.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/mathar2026a386829");
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, body);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula n => F.Id("n");
    private static Formula k => F.Id("k");
    private static Formula z => F.Id("z");
    private static Formula A(Formula index) => Call("a", index);
    private static Formula Sum(Formula index, Formula top, Formula term) => Seq(F.Sum, Underscore,
        Grp(Seq(index, Eq, D(0))), Caret, Grp(top), Sp, term);
    private static DocumentBlock Node(string name, string title, Formula statement, string prose, DescribeRole role, bool derived) =>
        Describe.Lean(DescribeId.Create("mathar-a386829-" + name), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), derived ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create()
    {
        var literal = Mul(Mul(Mul(Pow(D(3), k), Pow(D(2), Sub(n, k))),
            Call("choose", Add(Mul(D(2), n), D(1)), k)), Call("choose", Sub(Mul(D(2), n), k), Sub(n, k)));
        var recurrence = All("n", Nat, Seq(D(2), Sp, Le, Sp, n, Sp, Implies, Sp,
            Add(Add(Mul(Mul(D(2), n), A(n)), Mul(Sub(D(2, 0), Mul(D(3, 1), n)), A(Sub(n, D(1))))),
                Mul(Mul(D(9, 0), Sub(D(1), Mul(D(2), n))), A(Sub(n, D(2))))), Eq, D(0)));
        var r = F.Id("r");
        var j = F.Id("j");
        var p = F.Id("p");
        var dfinite = Seq(Exists, Sp, r, Colon, Nat, Comma, Sp, Exists, Sp, p, Colon,
            Seq(Nat, Sp, To, Sp, Q, OpenBracket, z, CloseBracket), Comma, Sp,
            Seq(Open, Exists, Sp, j, Colon, Nat, Comma, Sp, D(0), Sp, Le, Sp, j, Sp, Le, Sp, r, Sp, Land, Sp, Call("p", j), Sp, Neq, Sp, D(0), Close),
            Land, Sp, Sum(j, r, Mul(Call("p", j), Pow(F.Id("series"), Seq(Open, j, Close)))), Eq, D(0));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The inclusive binomial sum A386829 satisfies Mathar's complete recurrence and a nonzero homogeneous formal differential equation.",
            H("Mathar's A386829 recurrence and D-finiteness"), Blocks(
            Paragraph(Text("All sequence indices are natural numbers. Binomial coefficients are ordinary natural binomial coefficients, cast into the integers in the finite sum. Both k=0 and k=n are included. Coefficient subtraction in the recurrence is integer subtraction. The offset is zero, and n>=2 is the complete domain on which all three sequence indices are defined; the source does not explicitly give a recurrence onset.")),
            Node("a", "Literal inclusive binomial sum", All("n", Nat, Seq(A(n), Eq, Sum(k, n, literal))),
                "This is the original Manyama definition in OEIS A386829, without assuming equivalence to another formula from the entry.", DescribeRole.Definition, false),
            Node("series", "Entire formal generating series", Seq(F.Id("series"), Eq,
                Seq(F.Sum, Underscore, Grp(Seq(n, Eq, D(0))), Caret, Grp(Infty), Sp, Mul(A(n), Pow(z, n)))),
                "series is the power series with coefficient a(n), cast into the rationals, at every natural index. It belongs to Q[[z]]; no analytic convergence is required.", DescribeRole.Definition, true),
            Node("result", "Full recurrence and homogeneous differential equation", Seq(Open, recurrence, Close, Sp, Land, Sp, Open, dfinite, Close),
                "The first conjunct quantifies over every n>=2. The second provides a natural r and a function p from the naturals to Q[z], with at least one nonzero member among indices 0 through r whose weighted formal derivatives sum to zero. The notation series superscript (j) means its j-fold formal derivative, with the zero-fold derivative equal to series; each polynomial coefficient is embedded in Q[[z]]. A witness has order two: p0=-270, p1=-(42+630z), and p2=2-31z-180z squared. The constant coefficient of p2 is 2, proving that the equation is nonzero.", DescribeRole.Theorem, true),
            Paragraph(Text("Expanding the auxiliary sum b(n)=sum over j=0 through n of 5 to the j times 3 to the (n-j) times choose(n+j,j), interchanging finite triangular sums, and applying the hockey-stick identity proves a(n)=b(n). The binomial product identity and the reflection of the inclusive index range account for every endpoint.")),
            Paragraph(Text("A weighted telescoping identity gives 4b(n+1)+18b(n)=7c(n+1), where c(n)=5 to the n times choose(2n,n). The central-binomial identity (n+1)c(n+1)=10(2n+1)c(n) eliminates c and yields the recurrence. Initial values a(0)=1 and a(1)=13 determine the constant term in the first-order inhomogeneous equation. Formal differentiation produces the displayed homogeneous equation.")))));
    }
}
