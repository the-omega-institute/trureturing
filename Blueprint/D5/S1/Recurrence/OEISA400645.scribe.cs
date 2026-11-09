using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class OEISA400645Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/OEISA400645.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/oeis2026a400645");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed four-lag rounded norm sequence has Bernáth's exact ratio limit.",
        H("Bernáth's OEIS A400645 consecutive-ratio limit"),
        Blocks(
            Node("radicand", "The signed four-square radicand",
                All("a", SequenceType(), All("n", Nat(), Equal(Call("radicand", V("a"), V("n")), RadicandBody()))),
                "a(n+1) = round(sqrt(a(n)^2 + a(n-1)^2 + a(n-2)^2 - a(n-3)^2)). Source: OEIS A400645, revision 21, NAME field (unpaginated). The four squares are integers; the predecessor indices use natural subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceSequence", "The positive-index recurrence and initial values",
                All("a", SequenceType(), Equal(Call("IsSourceSequence", V("a")), Parenthesized(SourceBody()))),
                "a(n+1) = round(sqrt(a(n)^2 + a(n-1)^2 + a(n-2)^2 - a(n-3)^2)). The Mathematica field states a[1] == a[2] == a[3] == 0, a[4] == 1. Source: OEIS A400645, revision 21, NAME and Mathematica fields (unpaginated). The recurrence applies for n ≥ 4; index zero is unused. Nonnegativity of the signed radicand is explicit.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("squaredLimit", "The cross-referenced quartic constant",
                Equal(Cast(V("squaredLimit"), Real()),
                    Divide(Add(Add(D(1), SqrtOf(D(1,3))), SqrtOf(Sub(Mul(D(2), SqrtOf(D(1,3))), D(2)))), D(4))),
                "Equals (1 + sqrt(13) + sqrt(2*sqrt(13) - 2))/4. - _Vaclav Kotesovec_, Aug 27 2021. Source: OEIS A289917, revision 48, FORMULA field (unpaginated), cross-referenced by A400645.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("limitingRatio", "The conjectured consecutive-ratio limit",
                Equal(Cast(V("limitingRatio"), Real()), SqrtOf(V("squaredLimit"))),
                "Numerical evidence suggests that the ratio of consecutive terms (a(n+1)/a(n)) tends to 1.3122819079... (sqrt(A289917)) which is the largest real root of the asymptotic equation of this sequence: x^8-x^6-x^4-x^2+1. Source: OEIS A400645, revision 21, COMMENTS field (unpaginated). The value sqrt(A289917) is Real.sqrt squaredLimit.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The full infinite limit and largest-root assertion",
                Equal(V("claim"), Parenthesized(ClaimBody())),
                "Numerical evidence suggests that the ratio of consecutive terms (a(n+1)/a(n)) tends to 1.3122819079... (sqrt(A289917)) which is the largest real root of the asymptotic equation of this sequence: x^8-x^6-x^4-x^2+1. This is related to A116732 where the asymptotic equation is y^4-y^3-y^2-y+1 via y=x^2. Source: OEIS A400645, revision 21, COMMENTS field (unpaginated). Natural indices start at 1. Subtraction in the radicand is in ℤ, and nearest rounding produces an integer. Existence, eventual positive denominators and the largest real root are included.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The signed rounded recurrence has the stated infinite limit",
                ClaimBody(),
                "The integer rounding bound and monotonicity give a Fibonacci upper estimate. With squaredLimit greater than 17/10, the rounding errors grow more slowly than the dominant mode. The exact value a(26)=324 controls the entire infinite error tail and gives a positive normalized projection limit above 73872/17. A weighted three-coordinate contraction gives a positive limit for normalized squares. Division and continuity of Real.sqrt give the consecutive-ratio limit. The quartic factorization identifies the largest octic root.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("bernath-a400645"), ResolutionKind.Proved)))));

    private static Formula RadicandBody() => Sub(
        Add(Add(Pow(Cast(Call("a", V("n")), Int()), D(2)),
            Pow(Cast(Call("a", Sub(V("n"), D(1))), Int()), D(2))),
            Pow(Cast(Call("a", Sub(V("n"), D(2))), Int()), D(2))),
        Pow(Cast(Call("a", Sub(V("n"), D(3))), Int()), D(2)));

    private static Formula SourceBody()
    {
        var a = V("a");
        var n = V("n");
        var rounded = Call("round", SqrtOf(Cast(Call("radicand", a, n), Real())));
        var step = And(Le(D(0), Call("radicand", a, n)),
            Equal(Cast(Call("a", Add(n, D(1))), Int()), rounded));
        var recurrence = All("n", Nat(), Imp(Le(D(4), n), step));
        return And(Equal(Call("a", D(1)), D(0)),
            And(Equal(Call("a", D(2)), D(0)),
                And(Equal(Call("a", D(3)), D(0)),
                    And(Equal(Call("a", D(4)), D(1)), recurrence))));
    }

    private static Formula ClaimBody()
    {
        var a = V("a");
        var n = V("n");
        var ratio = Divide(Cast(Call("a", Add(n, D(1))), Real()),
            Cast(Call("a", n), Real()));
        var error = Lt(Abs(Sub(ratio, V("limitingRatio"))), V("e"));
        var tail = All("n", Nat(), Imp(Le(V("N"), n),
            And(Lt(D(0), Call("a", n)), error)));
        var threshold = ExistsOf("N", Nat(), And(Le(D(4), V("N")), tail));
        var convergence = All("a", SequenceType(), Imp(Call("IsSourceSequence", a),
            All("e", Real(), Imp(Lt(D(0), V("e")), threshold))));
        var algebraic = And(Equal(Octic(V("limitingRatio")), D(0)),
            All("x", Real(), Imp(Equal(Octic(V("x")), D(0)), Le(V("x"), V("limitingRatio")))));
        return And(ExistsOf("a", SequenceType(), Call("IsSourceSequence", a)),
            And(convergence, algebraic));
    }

    private static Formula Octic(Formula x) => Add(Sub(Sub(Sub(Pow(x, D(8)), Pow(x, D(6))), Pow(x, D(4))), Pow(x, D(2))), D(1));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("oeis-a400645-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula SqrtOf(Formula value) => new Formula.Apply(Q("Real", "sqrt"), [value]);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Int() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula SequenceType() => Seq(Nat(), Sp, To, Sp, Nat());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, Parenthesized(type), Comma, Sp, body);
    private static Formula ExistsOf(string name, Formula type, Formula body) => Seq(Exists, Sp, V(name), Colon, Sp, Parenthesized(type), Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Sub(Formula x, Formula y) => Seq(x, Sp, Minus, Sp, y);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Divide(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(Parenthesized(x), y);
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
}
