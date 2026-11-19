using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenMinpolyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpol"
                +
                "yRefutation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refuting the zero-fugacity degree formula", H("Refuting the zero-fugacity degree formula")
                , Blocks(
            Paragraph(Text("Conjecture B.1 asserts a minimal-polynomial degree formula for" +
                " every natural n at least two. The algebra is the full planar " +
                "diagram algebra at loop fugacity zero. At n=9 the asserted " +
                "value is 81, whereas an annihilating polynomial of degree 57 " +
                "gives an upper bound of 57.")),

            Node("claim", Eq(N("claim"), All("n", Nat(), Arrow(Le(D(2), X("n")),
                Eq(Typed(Call("Nat.cast", Call("Polynomial.natDegree",
                    Call("minpoly", N("Complex"), Call("h", N("Complex"), X("n"))))),
                    N("Rat")), Call("HDiv.hDiv", Add(
                        Power(Typed(D(3), N("Rat")), Call("Nat.div", Add(X("n"), D(1)), D(2))),
                        Mul(Power(Typed(Negate(D(1)), N("Rat")), X("n")),
                            Power(Typed(D(3), N("Rat")),
                                Call("Nat.div", Call("Nat.sub", X("n"), D(1)), D(2))))),
                        Typed(D(2), N("Rat"))))))),
                "Appendix B.1, (B.13): natural division defines both exponents;" +
                " Nat.sub is truncated. The outer division and the degree cast " +
                "are in Rat.",
                literature: true),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("result"), StatementSource.FromAuthor(Disp(Call("Not", N("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The integer recurrence and literal diagram action give " +
                    "p(h_9)=0 for a monic polynomial of degree 57. The minimal " +
                    "polynomial therefore has degree at most 57, which contradicts " +
                    "the conjectured value 81. No exact degree is asserted."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("poncini-rasmussen-2022-minpoly-degree-conjecture-b1"),
                    ResolutionKind.Refuted)))));


    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/poncini2023planar");
    private static Formula X(string name) => F.Id(name);

    private static Formula N(string name) => Q(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((s, i) =>
        i == 0 ? new[] { NamePart(s) } : new[] { Dot, NamePart(s) }).ToArray());
    private static Formula NamePart(string name)
    {
        bool prime = name.EndsWith('\'');
        var words = name.Replace("'", "").Split('_');
        Formula result = F.Id(words[^1]);
        for (int i = words.Length - 2; i >= 0; --i)
            result = Seq(F.Id(words[i]), Underscore, Grp(result));
        return prime ? Seq(Operatorname, Grp(result), Apos) : Seq(Operatorname, Grp(result));
    }

    private static Formula Call(string name, params Formula[] args) => At(Q(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula D(long n) => n < 0 ? Negate(D(-n)) : Num(n);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Bound(string name, Formula type) => Typed(X(name), type);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Bound(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Arrow(Formula a, Formula b) =>
        new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) =>
        new Formula.Power(Parenthesized(a), Parenthesized(b));
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula Nat() => N("Nat");
    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, bool literature = false,
        bool acknowledgeSource = false) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) :
                acknowledgeSource ? AssessedProvenance.FromRepo(Source) :
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

}
