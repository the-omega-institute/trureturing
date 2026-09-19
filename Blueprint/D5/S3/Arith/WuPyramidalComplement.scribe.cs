using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class WuPyramidalComplementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/WuPyramidalComplement.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/wu2025pyramidalcomplement");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wu's formula enumerates every positive integer outside a k-gonal-pyramidal sequence for k at least nine.",
        H("Wu's Pyramidal Complement Formula"),
        Blocks(
            Node("pyramidal", "The k-gonal-pyramidal sequence", PyramidalFormula(),
                "The binomial expression is integral at every natural index and equals "
                    + "m(m+1)(m(k-2)-(k-5))/6. The value at index zero is included only "
                    + "as a counting extension; the source sequence uses positive indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("complement", "The positive complement", ComplementFormula(),
                "C(k,x) holds exactly when x is positive and is not P(k,m) for any positive m. "
                    + "This definition is independent of the proposed enumeration formula.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("root-index", "The integer root index", RootIndexFormula(),
                "R(k,n) is the greatest natural h whose cube is at most the natural quotient "
                    + "6n divided by k-2.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("upper-threshold", "The upper threshold", UpperFormula(),
                "U(k,h) is the inclusive upper-branch threshold in Equation (6).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lower-threshold", "The lower threshold", LowerFormula(),
                "L(k,h) is the inclusive lower-branch threshold in Equation (6).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("branch-selector", "The ordered source branches", SelectorFormula(),
                "The upper test is evaluated first. If it fails, the lower test is evaluated; "
                    + "otherwise the middle code is returned.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("evaluate-branch", "The three branch adjustments", EvaluateFormula(),
                "The codes some(true), some(false), and none evaluate respectively to n+h+1, "
                    + "n+h-1 using natural subtraction, and n+h.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("wu-conjecture-one", "Conjecture 1", ResultFormula(),
                "Let h be the floor of the real cube root of 6n/(k-2). For every k at least "
                    + "nine and every positive n, the (n-1)-st zero-based member of the positive "
                    + "complement is the value selected by the exact inclusive thresholds. "
                    + "The proof identifies this real floor with R(k,n), locates the answer "
                    + "strictly between consecutive pyramidal values in all three branches, "
                    + "and counts exactly n-1 complement values below it.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("wu-pyramidal-" + id),
        DeclarationHandle.Create(Prefix + DeclarationName(id)),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role);

    private static string DeclarationName(string id) => id switch
    {
        "root-index" => "rootIndex",
        "upper-threshold" => "upperThreshold",
        "lower-threshold" => "lowerThreshold",
        "branch-selector" => "branchSelector",
        "evaluate-branch" => "evaluateBranch",
        "wu-conjecture-one" => "wu_conjecture_one",
        _ => id
    };

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula EqF(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), N(), body);

    private static Formula PyramidalFormula()
    {
        var k = V("k"); var m = V("m");
        var rhs = Add(Mul(Sub(k, D(2)), Call("choose", Add(m, D(1)), D(3))),
            Call("choose", Add(m, D(1)), D(2)));
        return Disp(All("k", All("m", EqF(Call("P", k, m), rhs))));
    }

    private static Formula ComplementFormula()
    {
        var k = V("k"); var x = V("x"); var m = V("m");
        var excluded = All("m", Imp(Lt(D(0), m), Ne(Call("P", k, m), x)));
        return Disp(All("k", All("x", Iff(Call("C", k, x), And(Lt(D(0), x), excluded)))));
    }

    private static Formula RootIndexFormula()
    {
        var k = V("k"); var n = V("n");
        return Disp(All("k", All("n", EqF(Call("R", k, n),
            Call("root", D(3), Call("div", Mul(D(6), n), Sub(k, D(2))))))));
    }

    private static Formula UpperFormula()
    {
        var k = V("k"); var h = V("h");
        var rhs = Add(Add(Add(Mul(Sub(k, D(2)), Pow(h, D(3))),
            Mul(Mul(D(3), Sub(k, D(1))), Pow(h, D(2)))),
            Mul(Sub(Mul(D(2), k), D(1)), h)), D(6));
        return Disp(All("k", All("h", EqF(Call("U", k, h), rhs))));
    }

    private static Formula LowerFormula()
    {
        var k = V("k"); var h = V("h");
        var rhs = Mul(Mul(h, Sub(h, D(1))), Add(Mul(h, Sub(k, D(2))), Add(k, D(1))));
        return Disp(All("k", All("h", EqF(Call("L", k, h), rhs))));
    }

    private static Formula SelectorFormula()
    {
        var u = V("u"); var l = V("l"); var c = V("c");
        var k = V("k"); var n = V("n"); var h = V("h");
        var rhs = Call("if", Le(Call("U", k, h), Mul(D(6), n)), u,
            Call("if", Le(Mul(D(6), n), Call("L", k, h)), l, c));
        return Disp(EqF(Call("B", u, l, c, k, n, h), rhs));
    }

    private static Formula EvaluateFormula()
    {
        var b = V("b"); var n = V("n"); var h = V("h");
        return Disp(EqF(Call("E", b, n, h), Call("match", b,
            Add(Add(n, h), D(1)), Sub(Add(n, h), D(1)), Add(n, h))));
    }

    private static Formula ResultFormula()
    {
        var k = V("k"); var n = V("n");
        var h = new Formula.Floor(Pow(Div(Mul(D(6), n), Sub(k, D(2))), Div(D(1), D(3))));
        var branch = Call("B", Call("some", V("true")), Call("some", V("false")),
            V("none"), k, n, h);
        var result = EqF(Call("nth", Call("C", k), Sub(n, D(1))), Call("E", branch, n, h));
        return Disp(All("k", All("n", Imp(Le(D(9), k), Imp(Le(D(1), n), result)))));
    }
}
