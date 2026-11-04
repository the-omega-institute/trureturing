using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA185765RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Recurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hardin2011a185765");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-column binary arrays and Hardin's trace-avoidance recurrence.",
        H("HardinA185765Recurrence"),
        Blocks(
            Node("claim", "Hardin’s empirical recurrence", IffTo(F.Id("claim"), ClaimBody()),
                "Empirical: a(n)=a(n-1)+30*a(n-2)+24*a(n-3)-95*a(n-4)-15*a(n-5)+64*a(n-6)-116*a(n-7)+16*a(n-8)+16*a(n-9) for n>12 Sole FORMULA field, OEIS A185765 revision 9, without page numbering. The count a is the preceding finite cardinality. Natural subtraction is truncated; all ten indices are positive when n is at least thirteen. Counts are embedded in the integers before signed operations.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("residual", "The vector residual", ResidualFormula(),
                "The residual applies the nine coefficients of the recurrence to consecutive continuation vectors, with scalar multiplication over the integers.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("Certificate", "Three finite equalities", IffTo(F.Id("Certificate"), CertificateBody()),
                "The vector residual at five is zero, and the scalar totals at three and four are zero.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("finite_certificate", "The three equalities hold", CertificateBody(),
                "The literal tables satisfy every transfer step through fourteen, the vector residual at five vanishes, and the scalar residual totals at three and four vanish.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The recurrence holds for every stated index", ClaimBody(),
                "Linearity propagates the vanishing vector residual from five onward. The scalar equalities at three and four cover indices thirteen and fourteen. The counting identity then gives the stated recurrence for every n at least thirteen.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin185765"), ResolutionKind.Proved))), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hardin-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula IffTo(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula LeTo(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula FinOf(long n) => Call("Fin", Num(n));
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Sp, Colon, Sp, Ints));
    private static Formula SumBound(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula ResidualFormula()
    {
        Formula k = F.Id("k");
        Formula body = Subtract(Call("u", Add(k, Num(9))), Call("u", Add(k, Num(8))));
        body = Subtract(body, App(Q("HSMul", "hSMul"), Cast(Num(30)), Call("u", Add(k, Num(7)))));
        body = Subtract(body, App(Q("HSMul", "hSMul"), Cast(Num(24)), Call("u", Add(k, Num(6)))));
        body = Add(body, App(Q("HSMul", "hSMul"), Cast(Num(95)), Call("u", Add(k, Num(5)))));
        body = Add(body, App(Q("HSMul", "hSMul"), Cast(Num(15)), Call("u", Add(k, Num(4)))));
        body = Subtract(body, App(Q("HSMul", "hSMul"), Cast(Num(64)), Call("u", Add(k, Num(3)))));
        body = Add(body, App(Q("HSMul", "hSMul"), Cast(Num(116)), Call("u", Add(k, Num(2)))));
        body = Subtract(body, App(Q("HSMul", "hSMul"), Cast(Num(16)), Call("u", Add(k, Num(1)))));
        body = Subtract(body, App(Q("HSMul", "hSMul"), Cast(Num(16)), Call("u", k)));
        return All("k", Nats, Equal(Call("residual", k), body));
    }
    private static Formula TotalExpr(Formula v) => SumBound("r", FinOf(64), SumBound("s", FinOf(64), App(v, F.Id("r"), F.Id("s"))));
    private static Formula CertificateBody() => And(Equal(Call("residual", Num(5)), Num(0)), And(Equal(TotalExpr(Call("residual", Num(3))), Num(0)), Equal(TotalExpr(Call("residual", Num(4))), Num(0))));
    private static Formula ClaimBody()
    {
        Formula n = F.Id("n");
        Formula a(long d) => Cast(Call("a", Subtract(n, Num(d))));
        Formula rhs = Add(a(1), Multiply(Num(30), a(2)));
        rhs = Add(rhs, Multiply(Num(24), a(3)));
        rhs = Subtract(rhs, Multiply(Num(95), a(4)));
        rhs = Subtract(rhs, Multiply(Num(15), a(5)));
        rhs = Add(rhs, Multiply(Num(64), a(6)));
        rhs = Subtract(rhs, Multiply(Num(116), a(7)));
        rhs = Add(rhs, Multiply(Num(16), a(8)));
        rhs = Add(rhs, Multiply(Num(16), a(9)));
        return All("n", Nats, Imp(LeTo(Num(13), n), Equal(Cast(Call("a", n)), rhs)));
    }
}
