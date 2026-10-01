using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class SplitCovarianceIntersectionEvenConvexityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Estimation/li2026splitcif");
    private const string DefinitionQuote = @"Section 2.1, p. 2: ""Matrices mentioned in this paper are symmetric matrices by default. Given matrices $\mathbf{P}_{1d}$, $\mathbf{P}_{1i}$, $\mathbf{P}_{2d}$, and $\mathbf{P}_{2i}$ that are positive semi-definite, i.e., $\mathbf{P}_{1d} \geq \mathbf{0}$, $\mathbf{P}_{1i} \geq \mathbf{0}$, $\mathbf{P}_{2d} \geq \mathbf{0}$, $\mathbf{P}_{2i} \geq \mathbf{0}$. Besides, the matrices $\mathbf{P}_{1d} + \mathbf{P}_{1i}$ and $\mathbf{P}_{2d} + \mathbf{P}_{2i}$ which normally correspond to covariances of certain estimates are always positive definite, i.e., $\mathbf{P}_{1d} + \mathbf{P}_{1i} > 0$ and $\mathbf{P}_{2d} + \mathbf{P}_{2i} > 0$. For $w \in [0,1]$, define""; equation (1) reads $\mathbf{P}_{1}(w) = \mathbf{P}_{1d}/w + \mathbf{P}_{1i}$, $\mathbf{P}_{2}(w) = \mathbf{P}_{2d}/(1-w) + \mathbf{P}_{2i}$, $\mathbf{P}(w) = (\mathbf{P}_{1}(w)^{-1} + \mathbf{P}_{2}(w)^{-1})^{-1}$. ""When $w=0$ or $w=1$, $\mathbf{P}(w)$ denotes the limit value as $w \to 0$ or $w \to 1$ respectively."" The encoding uses real matrices indexed by Fin n and A, B, C, D for the four source matrices in that order. Scalar division by w is multiplication by the reciprocal scalar, denoted smul in the formula; inv is the matrix inverse. The definition is total in Lean. The theorem concerns only 0 < w < 1; the endpoints w in {0,1} and their limit convention are not part of the formal statement.";
    private const string ClaimQuote = @"Section 2.2, p. 3: ""For a generic function $f(x)$, if its $m$-th-order derivative is always non-negative (or positive semi-definite), namely $\frac{d^m}{dx^m} f(x) \geq 0$, then it is said to have the \textbf{$m$-th-order convexity} [16]."" ""The proposed conjecture is that \textbf{the $w$-optimization problem has arbitrary even-order convexity}, more specifically, for $k \in \{1, 2, 3, \cdots\}$ we always have"" $\frac{d^{2 k}}{d w^{2 k}} \ln \det(\mathbf{P}(w)) \geq 0$, $\frac{d^{2 k}}{d w^{2 k}} tr \{ \mathbf{P}(w) \} \geq 0$ (7a), (7b). The encoding quantifies over every natural dimension n, including the harmless empty dimension, all four positive semidefinite real matrices with A+B and C+D positive definite, all natural k at least 1, and all real w in (0,1). PosSemidef includes symmetry for real matrices. The iteratedDeriv operator is the ordinary iterated real derivative; log is Real.log. Neither individual positive definiteness nor commutativity is assumed.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The split covariance intersection covariance has nonnegative derivatives of every positive even order for both its log determinant and its trace, with semidefinite input covariances and positive definite pair sums.",
        H("Arbitrary even-order convexity of split covariance intersection"),
        Blocks(
            Node("splitP", "The split covariance intersection covariance", SplitDefinition(), DefinitionQuote,
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Li's arbitrary even-order convexity conjecture", Disp(new Formula.Logic(
                F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody()))), ClaimQuote,
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Both even-order derivative inequalities", Disp(ClaimBody()),
                "For positive definite inputs, introduce a three-block positive definite affine pencil M and its lower two-block compression K. The upper inverse corner is splitP, and det(splitP) = det(K)/det(M). Noncommutative differentiation of the affine inverse gives positive semidefinite even inverse derivatives by a matrix congruence. Spectral diagonalization and scalar Jensen applied to squared overlaps give the even-power trace inequality for isometric compression; this makes each even derivative of log det(K) minus log det(M) nonnegative. Adding a positive scalar multiple of the identity to each input and taking the scalar to zero extends both inequalities to semidefinite inputs. Joint smoothness near each interior weight gives continuity of every fixed-order derivative in the regularization parameter.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))), []));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("split-cif-" + declaration.ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(QuotedParagraph(prose)), role, resolution);

    private static DocumentBlock QuotedParagraph(string prose)
    {
        prose = prose.Replace(@"\textbf{$m$-th-order convexity}", "**$m$-th-order convexity**")
            .Replace(@"\textbf{the $w$-optimization problem has arbitrary even-order convexity}",
                "**the $w$-optimization problem has arbitrary even-order convexity**");
        var parts = prose.Split('$');
        if (parts.Length % 2 != 1) throw new ArgumentException("Unclosed source quotation math span.");
        var inlines = new List<Inline>();
        for (var i = 0; i < parts.Length; i++)
        {
            if (i % 2 == 1) inlines.Add(Math(SourceFormula(parts[i])));
            else if (parts[i].Length > 0) inlines.Add(Text(parts[i]));
        }
        return Paragraph([.. inlines]);
    }

    private static Formula SourceMatrix(byte input, string component) => new Formula.Subscript(
        Seq(Mathbf, Grp(F.Id("P"))), Seq(D(input), F.Id(component)));
    private static Formula SourceP(byte? input = null) => input is byte i
        ? new Formula.Subscript(Seq(Mathbf, Grp(F.Id("P"))), D(i))
        : Seq(Mathbf, Grp(F.Id("P")));
    private static Formula SourceValue(byte? input = null) => Seq(SourceP(input), Parenthesized(F.Id("w")));
    private static Formula SourceInverse(Formula value) => new Formula.Power(value, Seq(Minus, D(1)));
    private static Formula SourceDerivative(Formula order, string variable, Formula objective) => Seq(
        new Formula.Fraction(new Formula.Power(F.Id("d"), order),
            Seq(F.Id("d"), new Formula.Power(F.Id(variable), order))), Sp, objective);
    private static Formula SourceNonnegative(Formula value) => new Formula.Relation(
        value, FormulaRelationOperator.GreaterThanOrEqual, D(0));

    private static Formula SourceFormula(string source)
    {
        Formula w = F.Id("w"), m = F.Id("m"), k = F.Id("k");
        Formula fx = Seq(F.Id("f"), Parenthesized(F.Id("x")));
        Formula pd1 = SourceMatrix(1, "d"), pi1 = SourceMatrix(1, "i");
        Formula pd2 = SourceMatrix(2, "d"), pi2 = SourceMatrix(2, "i");
        Formula order = Seq(D(2), Sp, k);
        return source switch
        {
            @"\mathbf{P}_{1d}" => pd1,
            @"\mathbf{P}_{1i}" => pi1,
            @"\mathbf{P}_{2d}" => pd2,
            @"\mathbf{P}_{2i}" => pi2,
            @"\mathbf{P}_{1d} \geq \mathbf{0}" => new Formula.Relation(pd1,
                FormulaRelationOperator.GreaterThanOrEqual, Seq(Mathbf, Grp(D(0)))),
            @"\mathbf{P}_{1i} \geq \mathbf{0}" => new Formula.Relation(pi1,
                FormulaRelationOperator.GreaterThanOrEqual, Seq(Mathbf, Grp(D(0)))),
            @"\mathbf{P}_{2d} \geq \mathbf{0}" => new Formula.Relation(pd2,
                FormulaRelationOperator.GreaterThanOrEqual, Seq(Mathbf, Grp(D(0)))),
            @"\mathbf{P}_{2i} \geq \mathbf{0}" => new Formula.Relation(pi2,
                FormulaRelationOperator.GreaterThanOrEqual, Seq(Mathbf, Grp(D(0)))),
            @"\mathbf{P}_{1d} + \mathbf{P}_{1i}" => Add(pd1, pi1),
            @"\mathbf{P}_{2d} + \mathbf{P}_{2i}" => Add(pd2, pi2),
            @"\mathbf{P}_{1d} + \mathbf{P}_{1i} > 0" => new Formula.Relation(
                Add(pd1, pi1), FormulaRelationOperator.GreaterThan, D(0)),
            @"\mathbf{P}_{2d} + \mathbf{P}_{2i} > 0" => new Formula.Relation(
                Add(pd2, pi2), FormulaRelationOperator.GreaterThan, D(0)),
            @"w \in [0,1]" => new Formula.Relation(w, FormulaRelationOperator.MemberOf,
                Seq(OpenBracket, D(0), Comma, D(1), CloseBracket)),
            @"\mathbf{P}_{1}(w) = \mathbf{P}_{1d}/w + \mathbf{P}_{1i}" => Equal(
                SourceValue(1), Add(Seq(pd1, Slash, w), pi1)),
            @"\mathbf{P}_{2}(w) = \mathbf{P}_{2d}/(1-w) + \mathbf{P}_{2i}" => Equal(
                SourceValue(2), Add(Seq(pd2, Slash, Parenthesized(Sub(D(1), w))), pi2)),
            @"\mathbf{P}(w) = (\mathbf{P}_{1}(w)^{-1} + \mathbf{P}_{2}(w)^{-1})^{-1}" => Equal(
                SourceValue(), SourceInverse(Parenthesized(Add(
                    SourceInverse(SourceValue(1)), SourceInverse(SourceValue(2)))))),
            "w=0" => Equal(w, D(0)),
            "w=1" => Equal(w, D(1)),
            @"\mathbf{P}(w)" => SourceValue(),
            @"w \to 0" => Seq(w, Sp, To, Sp, D(0)),
            @"w \to 1" => Seq(w, Sp, To, Sp, D(1)),
            "f(x)" => fx,
            "m" => m,
            @"\frac{d^m}{dx^m} f(x) \geq 0" => SourceNonnegative(SourceDerivative(m, "x", fx)),
            "w" => w,
            @"k \in \{1, 2, 3, \cdots\}" => new Formula.Relation(k, FormulaRelationOperator.MemberOf,
                Seq(OpenBrace, D(1), Comma, Sp, D(2), Comma, Sp, D(3), Comma, Sp,
                    Cdot, Cdot, Cdot, CloseBrace)),
            @"\frac{d^{2 k}}{d w^{2 k}} \ln \det(\mathbf{P}(w)) \geq 0" => SourceNonnegative(
                SourceDerivative(order, "w", Seq(Named("ln"), Sp, Named("det"), Parenthesized(SourceValue())))),
            @"\frac{d^{2 k}}{d w^{2 k}} tr \{ \mathbf{P}(w) \} \geq 0" => SourceNonnegative(
                SourceDerivative(order, "w", Seq(F.Id("tr"), Sp, OpenBrace, Sp, SourceValue(), Sp, CloseBrace))),
            _ => throw new ArgumentException("Unknown mathematical span in source quotation: " + source),
        };
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string v, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(
        Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula AtLeast(Formula a, Formula b) => new Formula.Relation(b, FormulaRelationOperator.LessThanOrEqual, a);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NumberType(string t) => Seq(Mathbb, Grp(F.Id(t)));
    private static Formula MatrixType(Formula n) => Call("Matrix", Call("Fin", n), Call("Fin", n), NumberType("R"));
    private static Formula P(Formula w) => Call("splitP", F.Id("A"), F.Id("B"), F.Id("C"), F.Id("D"), w);

    private static Formula MatrixBinders(Formula body)
    {
        foreach (var name in new[] { "D", "C", "B", "A" }) body = All(name, MatrixType(F.Id("n")), body);
        return All("n", NumberType("N"), body);
    }

    private static Formula SplitDefinition()
    {
        Formula w = F.Id("w");
        Formula left = Call("inv", Add(Call("smul", Call("inv", w), F.Id("A")), F.Id("B")));
        Formula right = Call("inv", Add(Call("smul", Call("inv", Sub(D(1), w)), F.Id("C")), F.Id("D")));
        return Disp(MatrixBinders(All("w", NumberType("R"), Equal(P(w), Call("inv", Add(left, right))))));
    }

    private static Formula ClaimBody()
    {
        Formula k = F.Id("k"), w = F.Id("w"), x = F.Id("x");
        Formula logObjective = Parenthesized(Seq(x, Sp, Mapsto, Sp, Call("log", Call("det", P(x)))));
        Formula traceObjective = Parenthesized(Seq(x, Sp, Mapsto, Sp, Call("trace", P(x))));
        Formula logInequality = AtLeast(Call("iteratedDeriv", Mul(D(2), k), logObjective, w), D(0));
        Formula traceInequality = AtLeast(Call("iteratedDeriv", Mul(D(2), k), traceObjective, w), D(0));
        Formula body = new Formula.Logic(Parenthesized(logInequality), FormulaLogicOperator.And, Parenthesized(traceInequality));
        body = All("w", NumberType("R"), Implies(new Formula.Relation(
            w, FormulaRelationOperator.MemberOf, Call("Ioo", D(0), D(1))), body));
        body = All("k", NumberType("N"), Implies(AtLeast(k, D(1)), body));
        body = Implies(Call("PosDef", Add(F.Id("C"), F.Id("D"))), body);
        body = Implies(Call("PosDef", Add(F.Id("A"), F.Id("B"))), body);
        foreach (var name in new[] { "D", "C", "B", "A" }) body = Implies(Call("PosSemidef", F.Id(name)), body);
        return MatrixBinders(body);
    }
}
