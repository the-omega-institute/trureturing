using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class LuschnyA323206ParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/LuschnyA323206Parity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/luschny2019a323206");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ballot coefficients and Catalan parity prove Luschny's A323206 conjecture.",
        H("Luschny's A323206 Parity Conjecture"),
        Blocks(
            Paragraph(Text("All array indices are natural numbers, including zero. "
                + "The coefficient ordinaryHypergeometricCoefficient uses ascending "
                + "Pochhammer polynomials and the reciprocal factorial. Only the finite "
                + "range j < k+1 occurs; no infinite hypergeometric value is used. "
                + "Powers with exponent zero, including 0^0, equal one.")),
            Node("A", "The terminating hypergeometric array", ArrayFormula(),
                "OEIS A323206 NAME (revision 52, no page number): "
                + "\"A(n, k) = hypergeometric([-k, k+1], [-k-1], n), square array read "
                + "by ascending antidiagonals for n,k >= 0.\" The displayed finite sum "
                + "expands this terminating hypergeometric notation over the rationals. "
                + "The lower Pochhammer parameter is -k-1 and each index satisfies j <= k, "
                + "so every denominator factor is nonzero.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The integral parity proposition",
                Disp(Equal(Named("claim"), Parenthesized(ClaimBody()))),
                "OEIS A323206 COMMENTS (revision 52, no page number): "
                + "\"Conjecture: A(n, k) is odd if and only if n is even or (n is odd "
                + "and k + 2 = 2^j for some j > 0).\" The integer a expresses the "
                + "integrality of A(n,k); the source's exponent j is named e here. "
                + "Odd is applied to a in the integers, and Even and Odd applied to n "
                + "are predicates on natural numbers.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "The parity classification", Disp(ClaimBody()),
                "The degree-j coefficient equals one at j=0 and otherwise equals "
                + "choose(k+j,j)-choose(k+j,j-1), with subtraction in the integers. "
                + "Thus the finite sum has an integer value. At an even argument "
                + "its reduction modulo two is the constant coefficient one; at an "
                + "odd argument it is the coefficient sum. The two hockey-stick sums "
                + "give the Catalan number catalan(k+1). The binary support theorem "
                + "for the shifted Catalan series then gives k+2=2^e, and k+2>=2 "
                + "forces e>0.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("luschny-a323206"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a323206-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));

    private static Formula ArrayFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var j = F.Id("j");
        var qk = Cast(k, Rationals());
        var negativeK = Seq(Minus, qk);
        var coefficient = Call("ordinaryHypergeometricCoefficient", negativeK,
            Add(qk, D(1)), Sub(negativeK, D(1)), j);
        var range = new Formula.Apply(Qualified("Finset", "range"), [Add(k, D(1))]);
        var sum = Seq(new Formula.Subscript(Sum, Seq(j, Sp, InMacro, Sp, range)), Sp,
            Mul(coefficient, new Formula.Power(Cast(n, Rationals()), j)));
        return Disp(Seq(Bound("n", Naturals()), Bound("k", Naturals()),
            Equal(Call("A", n, k), sum)));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var a = F.Id("a");
        var e = F.Id("e");
        var power = Seq(Exists, Sp, e, Colon, Sp, Naturals(), Comma, Sp,
            And(Seq(D(0), Sp, Lt, Sp, e),
                Equal(Add(k, D(2)), new Formula.Power(D(2), e))));
        var alternative = Seq(Call("Even", n), Sp, Lor, Sp,
            Parenthesized(And(Call("Odd", n), power)));
        var parity = Seq(Call("Odd", a), Sp, Iff, Sp, Parenthesized(alternative));
        return Seq(Bound("n", Naturals()), Bound("k", Naturals()),
            Exists, Sp, a, Colon, Sp, Integers(), Comma, Sp,
            And(Equal(Cast(a, Rationals()), Call("A", n, k)), parity));
    }
}
