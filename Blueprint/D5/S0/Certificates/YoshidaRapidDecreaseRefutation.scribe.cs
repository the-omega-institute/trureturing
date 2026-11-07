using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class YoshidaRapidDecreaseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/YoshidaRapidDecreaseRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/yoshida2010fiskbranden");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Z => new Formula.Integers();
    private static Formula SequenceType => new Formula.TypeArrow(N, R);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive sequence satisfies Yoshida's rapid-decrease inequalities but its first Turan transform does not.",
        H("Yoshida's Rapid-Decrease Question"),
        Blocks(
            Node("yoshida-rapid-decrease", "Rapid decrease", "RapidlyDecreasing", RapidFormula(),
                RapidProse(),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("yoshida-transform", "The transformed coefficients", "sCoeff", CoefficientFormula(),
                "Open Problem 5 (p. 11) writes Sᵣ[f(x)]=∑ₖ₌₀∞ "
                    + "(aₖ²−aₖ₋ᵣaₖ₊ᵣ)xᵏ:=∑ₖ₌₀∞ bₖxᵏ. "
                    + "The function sCoeff(a,r) is the coefficient sequence of S_r[f]. "
                    + "Definition 8 (p. 3) sets \"and aⱼ=0 if j∉{0,1,…,n}.\" Only negative indices are outside an infinite sequence. The conditional ite returns zero at negative indices and a(Int.toNat(j)) otherwise. Both k and r are natural numbers; the two shifted indices are cast "
                    + "to integers before subtraction and addition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("yoshida-question", "Open Problem 5", "claim",
                Disp(Equal(F.Id("claim"), ClaimBody())),
                QuestionProse(),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("yoshida-negative-answer", "A negative answer", "result",
                Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "Take aₖ=48ᵏ/32^(k choose 2) and r=1. Every a_k is positive, "
                    + "a_0=1 and a_1=48. The adjacent identity "
                    + "aₖ₊₁²=32aₖaₖ₊₂ gives rapid decrease with alpha=4 sqrt(2). "
                    + "The first transformed coefficients are 1, 2232 and 5022. The output "
                    + "inequality at index 1 forces alpha squared to be at most 992. "
                    + "Its threshold forces alpha squared to be at least 1117+sqrt(2233), "
                    + "which is larger. This contradiction concerns the coefficient "
                    + "question; it asserts no failure of Laguerre-Polya membership.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("yoshida-rapid-decrease"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Node(id, title, declaration, formula, Blocks(Paragraph(Text(prose))), role, provenance, resolution);

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, BlockSequence prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, prose, role, resolution);

    private static BlockSequence QuestionProse()
    {
        var k = F.Id("k");
        var a = F.Id("a");
        var x = F.Id("x");
        var r = F.Id("r");
        var input = SourceSum(Seq(new Formula.Subscript(a, k), Pow(x, k)));
        var coefficient = Sub(Pow(new Formula.Subscript(a, k), D(2)),
            Seq(new Formula.Subscript(a, Sub(k, r)), new Formula.Subscript(a, Add(k, r))));
        var transform = Seq(new Formula.Subscript(F.Id("S"), r), OpenBracket,
            Call("f", x), CloseBracket, Eq, SourceSum(Seq(Parenthesized(coefficient), Pow(x, k))),
            Colon, Eq, SourceSum(Seq(new Formula.Subscript(F.Id("b"), k), Pow(x, k))));
        return Blocks(Paragraph(Text("Open Problem 5 (p. 11): \"Let "),
            Math(Equal(Call("f", x), input)), Text(" where "), Math(SourceSequence(a)),
            Text(" is a rapidly decreasing sequence. If "), Math(transform),
            Text(", is it true that "), Math(SourceSequence(F.Id("b"))),
            Text(" is a rapidly decreasing sequence?\"")),
            Paragraph(Text("A power series is represented by its coefficients a. The first conjunct "
                + "asserts existence of such a sequence; the second asserts closure for "
                + "every such sequence and every positive natural r. The predicate "
                + "RapidlyDecreasing and the function sCoeff are expanded above.")));
    }

    private static BlockSequence RapidProse()
    {
        var k = F.Id("k");
        var sk = new Formula.Subscript(F.Id("s"), k);
        var sourceBound = Seq(new Formula.Fraction(Seq(Sqrt, Grp(D(2))), D(2)),
            Parenthesized(Add(D(1), Seq(Sqrt, Grp(Add(D(1),
                new Formula.Subscript(F.Id("s"), D(1))))))));
        var threshold = Seq(Alpha, Geq, Sp, Max, OpenBrace, D(2), Comma, sourceBound, CloseBrace);
        return Blocks(Paragraph(Text("Definition 29 (p. 10): \"A sequence of positive real numbers "),
            Math(SourceSequence(F.Id("s"))), Text(" is called rapidly decreasing, if the sequence "
                + "satisfies the following condition "),
            Math(Seq(Pow(sk, D(2)), Geq, Pow(Alpha, D(2)),
                new Formula.Subscript(F.Id("s"), Sub(k, D(1))),
                new Formula.Subscript(F.Id("s"), Add(k, D(1))))),
            Text(", for "), Math(threshold), Text(".\"")),
            Paragraph(Text("The sequence a has natural indices, all its terms are positive, and one "
                + "real alpha satisfies the threshold and every inequality at k>=1.")));
    }

    private static Formula SourceSequence(Formula a) => Seq(
        OpenBrace, new Formula.Subscript(a, F.Id("k")), CloseBrace,
        Underscore, Grp(F.Id("k"), Eq, D(0)), Caret, Grp(Infty));
    private static Formula SourceSum(Formula body) => Seq(
        Sum, Underscore, Grp(F.Id("k"), Eq, D(0)), Caret, Grp(Infty), body);

    private static Formula ZeroValue(Formula a, Formula j) =>
        Call("ite", Less(j, D(0)), D(0), App(a, App(Qualified("Int", "toNat"), j)));

    private static Formula RapidFormula()
    {
        var a = F.Id("a");
        var k = F.Id("k");
        var alpha = F.Id("alpha");
        var positive = All("k", N, Less(D(0), App(a, k)));
        var threshold = LessEqual(Call("max", D(2),
            Multiply(new Formula.Fraction(App(Qualified("Real", "sqrt"), D(2)), D(2)),
                Add(D(1), App(Qualified("Real", "sqrt"), Add(D(1), App(a, D(1))))))), alpha);
        var estimate = All("k", N, Implication(LessEqual(D(1), k),
            new Formula.Relation(Pow(App(a, k), D(2)), FormulaRelationOperator.GreaterThanOrEqual,
                Multiply(Multiply(Pow(alpha, D(2)), ZeroValue(a, Sub(CastZ(k), D(1)))),
                    ZeroValue(a, Add(CastZ(k), D(1)))))));
        return Disp(All("a", SequenceType, Equal(Call("RapidlyDecreasing", a),
            And(positive, Some("alpha", R, And(threshold, estimate))))));
    }

    private static Formula CoefficientFormula()
    {
        var a = F.Id("a");
        var r = F.Id("r");
        var k = F.Id("k");
        return Disp(All("a", SequenceType, All("r", N, All("k", N,
            Equal(Call("sCoeff", a, r, k), Sub(Pow(App(a, k), D(2)),
                Multiply(ZeroValue(a, Sub(CastZ(k), CastZ(r))),
                    ZeroValue(a, Add(CastZ(k), CastZ(r))))))))));
    }

    private static Formula ClaimBody()
    {
        var a = F.Id("a");
        var r = F.Id("r");
        return And(Some("a", SequenceType, Call("RapidlyDecreasing", a)),
            All("a", SequenceType, Implication(Call("RapidlyDecreasing", a),
                All("r", N, Implication(LessEqual(D(1), r),
                    Call("RapidlyDecreasing", Call("sCoeff", a, r)))))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(F.Id(name), arguments);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula CastZ(Formula x) => Parenthesized(Seq(x, Colon, Z));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LessEqual(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implication(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
