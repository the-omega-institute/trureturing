using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class HannaA381361AllOddDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/HannaA381361AllOdd.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/hanna2025a381361");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every exponential coefficient of Hanna's implicit rational series is an odd integer.",
        H("Hanna A381361: all terms are odd"),
        Blocks(
            Node("IsSourceSeries", "The implicit rational source series",
                All("A", PS(), Iff(Call("IsSourceSeries", V("A")), SourceBody(V("A")))),
                "OEIS A381361 revision 25, NAME field (no page number): “E.g.f. satisfies A(x) = exp( Integral abs(1/A(x)^2) dx ), where abs(F(x)) equals the series expansion formed by the unsigned coefficients in F(x).” The series A and I have rational coefficients. The primitive I has constant coefficient zero, A has constant coefficient one, and absSeries takes the absolute value of each ordinary coefficient. PowerSeries.subst takes I first and the rational exponential series second. All operations are formal.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The all-odd assertion",
                Iff(V("claim"), ClaimBody()),
                "OEIS A381361 revision 25, first COMMENTS line (no page number): “All terms appear to be odd.” The FORMULA field reads: “E.g.f. A(x) = Sum_{n>=0} a(n)*x^n/n! satisfies the following formulas.” The coefficient eCoeff A n is n! times PowerSeries.coeff n A. Existence is included, and every rational source solution has eCoeff A n = 2z+1 for an integer z at every natural index, including zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Every term is an odd integer", ClaimBody(),
                "The rational source series exists uniquely and its exponential coefficients are integers. In characteristic two every normalized Hurwitz square is the unit sequence; inversion and coefficientwise absolute value preserve this reduction. The derivative recurrence therefore gives a(n+1)=a(n) modulo two. Since a(0)=1, every term is odd. The claim concerns only this parity assertion; divisibility by five and elliptic or asymptotic formulas require separate arguments.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a381361-hanna-all-odd"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("hanna-a381361-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(name))), [.. args]);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula PS() => Call("PowerSeries", Q());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula SourceBody(Formula a)
    {
        var i = V("I");
        var inverseSquare = new Formula.Power(Parenthesized(new Formula.Power(a, D(2))), Seq(Minus, D(1)));
        return And(Eqn(Qualified("PowerSeries", "constantCoeff", a), D(1)),
            Ex("I", PS(), And(Eqn(Qualified("PowerSeries", "constantCoeff", i), D(0)),
                And(Eqn(Qualified("PowerSeries", "derivative", i), Qualified("HannaAbsoluteCubicCongruence", "absSeries", inverseSquare)),
                    Eqn(a, Qualified("PowerSeries", "subst", i, Qualified("PowerSeries", "exp", Q())))))));
    }
    private static Formula ClaimBody()
    {
        var a = V("A");
        var odd = All("n", N(), Ex("z", Z(), Eqn(Qualified("IntegralEGFComposition", "eCoeff", a, V("n")),
            new Formula.Binary(new Formula.Binary(Cast(D(2), Q()), FormulaBinaryOperator.Multiply, Cast(V("z"), Q())), FormulaBinaryOperator.Add, D(1)))));
        return And(Ex("A", PS(), Call("IsSourceSeries", a)),
            All("A", PS(), Imp(Call("IsSourceSeries", a), odd)));
    }
}
