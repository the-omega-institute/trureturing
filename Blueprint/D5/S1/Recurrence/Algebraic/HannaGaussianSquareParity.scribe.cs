using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaGaussianSquareParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2019a323689");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric coefficient pairs leave exactly the odd diagonal contribution.",
        H("Hanna's Gaussian square parity"),
        Blocks(
            Node("summand", "Rational summands", Disp(All("m", Nat(),
                Equal(Call("summand", V("m")), SummandBody()))),
                "OEIS A323689, NAME (unpaginated): \"G.f.: Sum_{n>=0} (x^n + i)^n / (1 + i*x^n)^(n+1), in which the constant term is taken to be 1.\" Complex.I is the imaginary unit and X is the formal series variable. The inverse has unit constant denominator.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A", "The coefficient series", Disp(Equal(V("A"),
                App(Q("PowerSeries", "mk"), Parenthesized(Seq(V("N"), Colon, Sp, Nat(), Sp, Mapsto, Sp, SeriesBody()))))),
                "OEIS A323689, NAME (unpaginated): \"G.f.: Sum_{n>=0} (x^n + i)^n / (1 + i*x^n)^(n+1), in which the constant term is taken to be 1.\" Degree zero is 1. At positive degree N, only indices 1 through N contribute.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The parity assertion", Disp(Equal(V("claim"), Parenthesized(ClaimBody()))),
                "OEIS A323689, COMMENTS and FORMULA (unpaginated): \"Odd terms occur only at n = k^2 for k >= 0 (conjecture); a(n^2) = 1 (mod 2) for n >= 0.\" The index N is natural, z is an ordinary integer embedded in the complex numbers, and degree zero is included.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Integral coefficients and exact odd support", Disp(ClaimBody()),
                "At positive degree, the exponent equation is symmetric in the two indices and off-diagonal pairs are even integers. A diagonal term is present exactly when N = r^2, and its weight is odd. The constant coefficient is 1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Complexes() => Seq(Mathbb, Grp(V("C")));

    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));


    private static Formula SumOn(string n, Formula s, Formula body) => Seq(
        new Formula.Subscript(Sum, Seq(V(n), Sp, InMacro, Sp, s)), Sp, Parenthesized(body));
    private static Formula If(Formula test, Formula yes, Formula no) => Seq(
        Named("if"), Sp, Parenthesized(test), Sp, Named("then"), Sp, yes,
        Sp, Named("else"), Sp, no);
    private static Formula Coeff(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula UnitI() => Q("Complex", "I");
    private static Formula RationalKernel(Formula m, Formula x) => Mul(
        Power(Add(x, App(V("C"), UnitI())), m),
        Power(Power(Add(D(1), Mul(App(V("C"), UnitI()), x)), Add(m, D(1))), Seq(Minus, D(1))));

    private static Formula SummandBody() => RationalKernel(V("m"), Power(V("X"), V("m")));
    private static Formula SeriesBody() => If(Equal(V("N"), D(0)), D(1),
        SumOn("m", App(Q("Finset", "Icc"), D(1), V("N")), Coeff(V("N"), Call("summand", V("m")))));

    private static Formula ClaimBody()
    {
        var representative = Equal(Coeff(V("N"), V("A")), Cast(V("z"), Complexes()));
        var support = Some("r", Nat(), Equal(V("N"), Power(V("r"), D(2))));
        var parity = Seq(Call("Odd", V("z")), Sp, Iff, Sp, Parenthesized(support));
        return All("N", Nat(), Some("z", Ints(), And(representative, parity)));
    }
}
