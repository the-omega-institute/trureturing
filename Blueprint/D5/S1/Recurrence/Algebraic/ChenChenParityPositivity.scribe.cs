using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class ChenChenParityPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.";
    private static readonly LibraryNoteRef SourceNote =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/chenchen2026stepm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every integer step at most minus three, two-step propagation makes each positive even row strictly positive.",
        H("Chen and Chen's Eulerian triangle parity positivity"),
        Blocks(
            Node("Source", "The exact boundary and recursion",
                All("m", Ints(), All("T", TriangleType(),
                    IffFormula(Call("Source", V("m"), V("T")), SourceBody()))),
                "OEIS A392664, A392665 and A392666 define T(n,1)=T(n,n)=1 for n>=1, "
                + "and the displayed recursion for 1<k<n, with m=-3,-4,-5 respectively. "
                + "All values are integers. Row zero and positions outside 1<=k<=n "
                + "are unconstrained. Subtractions in the two coefficients are integer "
                + "subtractions; predecessor indices use natural subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(SourceNote)),
            Node("ParityPositivity", "Existence and universal nonnegativity",
                All("m", Ints(), IffFormula(Call("ParityPositivity", V("m")), ParityBody())),
                "A solution exists, and every solution has nonnegative entries in each "
                + "positive even row. Existence is constructed recursively in the row "
                + "index with arbitrary zero values outside the prescribed triangle. "
                + "The universal clause applies to every extension, independently of those choices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(SourceNote)),
            Node("claim", "The three conjectures together", IffFormula(V("claim"), ClaimBody()),
                "The conjunction retains each source parameter separately, including "
                + "existence and the quantifier over every solution for each parameter.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(SourceNote)),
            Node("even_rows_positive", "Strict positivity for every integer r at least three",
                PositiveBody(),
                "Let U satisfy the source recursion with m=-r. Reflection follows by "
                + "row induction because the two recurrence coefficients exchange under "
                + "k -> n+1-k. Put x(n)=U(n,2). The recursion gives x(2)=1 and "
                + "x(n+2)=(r-1)^2*x(n)+r*(r-2)*n+2-r^2 for n>=2. In particular "
                + "x(4)=2*r*(r-3)+3>0. For n>=4 the forcing term is positive: "
                + "it equals r*(r-2)*(n-4)+3*r*(r-3)+r+2. Thus the second "
                + "column is positive at every even row, and reflection gives the "
                + "penultimate column. From a positive even row, both coefficients "
                + "are negative at every interior position of the next odd row, "
                + "making its interior negative. At positions 3 through n of row "
                + "n+2 both predecessors are negative, so both products are positive. "
                + "The second and penultimate positions use the column argument; "
                + "the two boundary positions equal one. Induction starts at row two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(SourceNote)),
            Node("result", "The complete source conjunction", ClaimBody(),
                "Apply the general positivity theorem at r=3,4,5 and weaken strict "
                + "positivity to nonnegativity. The recursively constructed solution "
                + "supplies existence for each parameter. No assumption about a "
                + "finite prefix or about the signs of later rows is used.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(SourceNote),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chen-chen-step-m-eulerian-parity-positivity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("chen-chen-" + name.ToLowerInvariant().Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(V("Z")));
    private static Formula TriangleType() => new Formula.TypeArrow(Nat(),
        new Formula.TypeArrow(Nat(), Ints()));
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, P(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, P(body));
    private static Formula And(Formula a, Formula b) => Seq(P(a), Sp, Land, Sp, P(b));
    private static Formula Implies(Formula a, Formula b) => Seq(P(a), Sp, Rightarrow, Sp, P(b));
    private static Formula IffFormula(Formula a, Formula b) => Seq(P(a), Sp, Iff, Sp, P(b));
    private static Formula EqFormula(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LE(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula LT(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Negate(Formula a) => Seq(Minus, a);
    private static Formula Cast(Formula a) => P(Seq(a, Colon, Sp, Ints()));
    private static Formula T(Formula n, Formula k) => new Formula.Apply(V("T"), [n, k]);

    private static Formula SourceBody()
    {
        var n = V("n");
        var k = V("k");
        var m = V("m");
        var boundary = All("n", Nat(), Implies(LE(D(1), n),
            And(EqFormula(T(n, D(1)), D(1)), EqFormula(T(n, n), D(1)))));
        var recurrence = EqFormula(T(n, k), Add(
            Mul(P(Add(Mul(m, P(Sub(Cast(n), Cast(k)))), D(1))), T(Sub(n, D(1)), Sub(k, D(1)))),
            Mul(P(Add(Mul(m, P(Sub(Cast(k), D(1)))), D(1))), T(Sub(n, D(1)), k))));
        return And(boundary, All("n", Nat(), All("k", Nat(),
            Implies(LT(D(1), k), Implies(LT(k, n), recurrence)))));
    }

    private static Formula Rows(Formula conclusion)
    {
        var columns = All("k", Nat(), Implies(LE(D(1), V("k")),
            Implies(LE(V("k"), V("n")), conclusion)));
        return All("n", Nat(), Implies(LE(D(1), V("n")),
            Implies(Call("Even", V("n")), columns)));
    }

    private static Formula ParityBody()
    {
        var existence = Some("T", TriangleType(), Call("Source", V("m"), V("T")));
        var universal = All("T", TriangleType(), Implies(Call("Source", V("m"), V("T")),
            Rows(LE(D(0), T(V("n"), V("k"))))));
        return And(existence, universal);
    }

    private static Formula ClaimBody() => And(Call("ParityPositivity", Negate(D(3))),
        And(Call("ParityPositivity", Negate(D(4))), Call("ParityPositivity", Negate(D(5)))));

    private static Formula PositiveBody()
    {
        var universal = All("T", TriangleType(), Implies(Call("Source", Negate(V("r")), V("T")),
            Rows(LT(D(0), T(V("n"), V("k"))))));
        return All("r", Ints(), Implies(LE(D(3), V("r")), universal));
    }
}
