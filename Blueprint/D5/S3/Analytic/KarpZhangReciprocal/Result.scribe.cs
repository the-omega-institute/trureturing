using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangReciprocal;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal-Pochhammer half of Karp-Zhang Conjecture 5.2.",
        H("Reciprocal coefficients and Abel reduction"), Blocks(
            Entry("karp-zhang-reciprocal-log-concave-sequence", "IsLogConcave", "The sequence convention",
                "The Lean predicate retains all four conditions: nonnegativity at every natural index, an index with nonzero value, the adjacent-product inequality for k ≥ 1, and the stated disjunction for every zero entry. Natural subtraction is used only with the stated bounds.", DescribeRole.Definition),
            Entry("karp-zhang-reciprocal-turanian-coefficient", "delta", "Finite Cauchy coefficient",
                "For a real sequence y, real mu, alpha, beta and natural m, delta(y,mu,alpha,beta,m) is the sum over k=0,...,m of y(k)y(m-k) times [c(k,mu+alpha)c(m-k,mu+beta)-c(k,mu)c(m-k,mu+alpha+beta)]. It is exactly the degree-m coefficient of the difference of the two formal Cauchy products of the reciprocal series. No analytic convergence hypothesis is imposed.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-reciprocal-increment"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangReciprocal/Result.increment"),
                H("Initial value and successive increments"),
                StatementSource.FromAuthor(IncrementFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At q=0 the increment is W(0); at a positive natural index it is W(q)-W(q-1). Telescoping these increments recovers W at the last index."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("karp-zhang-reciprocal-tail-sum"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangReciprocal/Result.tail_sum"),
                H("Reindexing a symmetric tail"),
                StatementSource.FromAuthor(TailSumFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("When 2q ≤ m, the indices satisfying q ≤ k and q ≤ m-k are exactly q+i with 0 ≤ i < m-q-q+1. Natural subtraction is used with these bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("karp-zhang-reciprocal-abel-layers"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangReciprocal/Result.abel_layers"),
                H("Abel decomposition into symmetric layers"),
                StatementSource.FromAuthor(AbelLayersFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For arbitrary real sequences y and K, telescoping the balanced products y(i)y(m-i) and interchanging the finite sums expresses their weighted sum as increments times symmetric tails. No positivity hypothesis is needed; the even middle index is counted once."))),
                DescribeRole.Theorem),
            Entry("karp-zhang-reciprocal-balanced-step", "balanced_step", "Balancing one pair of indices",
                "For every real sequence y satisfying IsLogConcave, natural m and natural k strictly less than floor(m/2), y(k)y(m-k) <= y(k+1)y(m-(k+1)). The interval-support condition justifies the distant ratio comparison when the endpoint product is positive; a zero endpoint product is handled by nonnegativity.", DescribeRole.Theorem),
            Entry("karp-zhang-reciprocal-abel-reduction", "abel_reduction", "Abel summation identity",
                "For every real sequence y, real mu, alpha, beta and natural m, put h=floor(m/2), W(q)=y(q)y(m-q), and T(q)=F(m,q,m-q,mu+alpha,mu+beta)-F(m,q,m-q,mu,mu+alpha+beta). Then delta=W(0)T(0)+sum over q=0,...,h-1 of [W(q+1)-W(q)]T(q+1). The identity holds without positivity assumptions. The even central index is counted once, because each T is an unpaired interval sum.", DescribeRole.Theorem),
            Entry("karp-zhang-reciprocal-half", "reciprocal_half", "All coefficients are nonnegative",
                "For every sequence y satisfying IsLogConcave, positive real mu, nonnegative real alpha and beta, and every natural m, 0 <= delta(y,mu,alpha,beta,m). This proves the reciprocal-Pochhammer assertion of Conjecture 5.2 on page 12 under exactly the sequence convention of Definition 1.1. It does not assert the corresponding gamma-series half.", DescribeRole.Theorem),
            Paragraph(Text(
                "The interval-support condition forces every entry between two positive entries to be positive. Divide the adjacent log-concavity inequalities only on such positive intervals and induct to compare distant successive ratios. Consequently W(q+1) >= W(q) below the middle; if W(q)=0, nonnegativity gives the same conclusion directly. Telescoping the increments of W expresses W(min(k,m-k)) as a sum of layers. Interchanging two finite sums turns each layer into a symmetric tail and proves the Abel identity. The interval-convolution balancing theorem makes each tail nonnegative, and every Abel weight is nonnegative. Thus each formal coefficient is nonnegative independently of growth or convergence of the infinite series.")))));

    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(Operatorname, Grp(F.Id("if")), Sp, condition,
            Sp, Operatorname, Grp(F.Id("then")), Sp, yes,
            Sp, Operatorname, Grp(F.Id("else")), Sp, no));

    private static Formula IncrementFormula()
    {
        Formula w = F.Id("W");
        Formula q = F.Id("q");
        return Disp(All("W", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")),
            All("q", F.Id("Nat"), Equal(Call("increment", w, q),
                Conditional(Equal(q, Num(0)), App(w, Num(0)),
                    Subtract(App(w, q), App(w, Subtract(q, Num(1)))))))));
    }

    private static Formula TailSumFormula()
    {
        Formula kernel = F.Id("K");
        Formula m = F.Id("m");
        Formula q = F.Id("q");
        Formula k = F.Id("k");
        Formula i = F.Id("i");
        Formula condition = new Formula.Logic(Le(q, k), FormulaLogicOperator.And,
            Le(q, Subtract(m, k)));
        Formula left = SumRange("k", Add(m, Num(1)),
            Conditional(condition, App(kernel, k), Num(0)));
        Formula right = SumRange("i", Add(Subtract(Subtract(m, q), q), Num(1)),
            App(kernel, Add(q, i)));
        return Disp(All("K", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")),
            All("m", F.Id("Nat"), All("q", F.Id("Nat"),
                Implies(Le(Multiply(Num(2), q), m), Equal(left, right))))));
    }

    private static Formula AbelLayersFormula()
    {
        Formula y = F.Id("y");
        Formula kernel = F.Id("K");
        Formula m = F.Id("m");
        Formula q = F.Id("q");
        Formula k = F.Id("k");
        Formula i = F.Id("i");
        Formula weight = Parenthesized(Seq(i, Colon, Sp, F.Id("Nat"), Sp, Mapsto, Sp,
            Multiply(App(y, i), App(y, Subtract(m, i)))));
        Formula left = SumRange("k", Add(m, Num(1)),
            Multiply(Multiply(App(y, k), App(y, Subtract(m, k))), App(kernel, k)));
        Formula tail = SumRange("i", Add(Subtract(Subtract(m, q), q), Num(1)),
            App(kernel, Add(q, i)));
        Formula right = SumRange("q", Add(App(Qualified("Nat", "div"), m, Num(2)), Num(1)),
            Multiply(Call("increment", weight, q), Parenthesized(tail)));
        return Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")),
            All("K", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")),
                All("m", F.Id("Nat"), Equal(left, right)))));
    }

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangReciprocal/Result." + name),
            H(title), TheoremStatement(name),
            name == "IsLogConcave" || name == "delta"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            name == "IsLogConcave"
                ? Blocks(SourceDefinition(), Paragraph(Text(text)))
                : Blocks(Paragraph(Text(text))), role);

    private static StatementSource TheoremStatement(string name) =>
        name == "delta" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("mu", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), All("m", F.Id("Nat"), Equal(Call("delta", F.Id("y"), F.Id("mu"), F.Id("alpha"), F.Id("beta"), F.Id("m")), SumRange("k", Add(F.Id("m"), Num(1)), Multiply(Multiply(App(F.Id("y"), F.Id("k")), App(F.Id("y"), Subtract(F.Id("m"), F.Id("k")))), Subtract(Multiply(Call("c", F.Id("k"), Add(F.Id("mu"), F.Id("alpha"))), Call("c", Subtract(F.Id("m"), F.Id("k")), Add(F.Id("mu"), F.Id("beta")))), Multiply(Call("c", F.Id("k"), F.Id("mu")), Call("c", Subtract(F.Id("m"), F.Id("k")), Add(Add(F.Id("mu"), F.Id("alpha")), F.Id("beta"))))))))))))))) :
        name == "IsLogConcave" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), new Formula.Logic(Call("IsLogConcave", F.Id("y")), FormulaLogicOperator.Iff, new Formula.Logic(All("k", F.Id("Nat"), Le(Num(0), App(F.Id("y"), F.Id("k")))), FormulaLogicOperator.And, new Formula.Logic(new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("k"), F.Id("Nat"), new Formula.Relation(App(F.Id("y"), F.Id("k")), FormulaRelationOperator.NotEqual, Num(0))), FormulaLogicOperator.And, new Formula.Logic(All("k", F.Id("Nat"), Implies(Le(Num(1), F.Id("k")), Le(Multiply(App(F.Id("y"), Subtract(F.Id("k"), Num(1))), App(F.Id("y"), Add(F.Id("k"), Num(1)))), new Formula.Power(App(F.Id("y"), F.Id("k")), Num(2))))), FormulaLogicOperator.And, All("N", F.Id("Nat"), Implies(Equal(App(F.Id("y"), F.Id("N")), Num(0)), new Formula.Logic(All("i", F.Id("Nat"), Equal(App(F.Id("y"), Add(F.Id("N"), F.Id("i"))), Num(0))), FormulaLogicOperator.Or, All("i", F.Id("Nat"), Implies(Le(F.Id("i"), F.Id("N")), Equal(App(F.Id("y"), Subtract(F.Id("N"), F.Id("i"))), Num(0)))))))))))))) :
        name == "balanced_step" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), Implies(Call("IsLogConcave", F.Id("y")), All("m", F.Id("Nat"), All("k", F.Id("Nat"), Implies(Lt(F.Id("k"), App(Qualified("Nat", "div"), F.Id("m"), Num(2))), Le(Multiply(App(F.Id("y"), F.Id("k")), App(F.Id("y"), Subtract(F.Id("m"), F.Id("k")))), Multiply(App(F.Id("y"), Add(F.Id("k"), Num(1))), App(F.Id("y"), Subtract(F.Id("m"), Add(F.Id("k"), Num(1))))))))))))) :
        name == "abel_reduction" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("mu", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), All("m", F.Id("Nat"), Equal(Call("delta", F.Id("y"), F.Id("mu"), F.Id("alpha"), F.Id("beta"), F.Id("m")), Add(Multiply(Multiply(App(F.Id("y"), Num(0)), App(F.Id("y"), F.Id("m"))), Subtract(Call("F", F.Id("m"), Num(0), F.Id("m"), Add(F.Id("mu"), F.Id("alpha")), Add(F.Id("mu"), F.Id("beta"))), Call("F", F.Id("m"), Num(0), F.Id("m"), F.Id("mu"), Add(Add(F.Id("mu"), F.Id("alpha")), F.Id("beta"))))), SumRange("q", App(Qualified("Nat", "div"), F.Id("m"), Num(2)), Multiply(Subtract(Multiply(App(F.Id("y"), Add(F.Id("q"), Num(1))), App(F.Id("y"), Subtract(F.Id("m"), Add(F.Id("q"), Num(1))))), Multiply(App(F.Id("y"), F.Id("q")), App(F.Id("y"), Subtract(F.Id("m"), F.Id("q"))))), Subtract(Call("F", F.Id("m"), Add(F.Id("q"), Num(1)), Subtract(F.Id("m"), Add(F.Id("q"), Num(1))), Add(F.Id("mu"), F.Id("alpha")), Add(F.Id("mu"), F.Id("beta"))), Call("F", F.Id("m"), Add(F.Id("q"), Num(1)), Subtract(F.Id("m"), Add(F.Id("q"), Num(1))), F.Id("mu"), Add(Add(F.Id("mu"), F.Id("alpha")), F.Id("beta"))))))))))))))) :
        name == "reciprocal_half" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), Implies(Call("IsLogConcave", F.Id("y")), All("mu", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), Implies(Lt(Num(0), F.Id("mu")), Implies(Le(Num(0), F.Id("alpha")), Implies(Le(Num(0), F.Id("beta")), All("m", F.Id("Nat"), Le(Num(0), Call("delta", F.Id("y"), F.Id("mu"), F.Id("alpha"), F.Id("beta"), F.Id("m")))))))))))))) :
        StatementSource.WithoutFormula();

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula SumRange(string name, Formula upper, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(F.Id(name), Sp, InMacro, Sp,
            App(Qualified("Finset", "range"), upper)), Sp, Parenthesized(body));

    private static DocumentBlock SourceDefinition() => Paragraph(
        Text("Definition 1.1, page 2: Let "), Math(SourceSequence()),
        Text(" be a non-negative nontrivial real sequence. We call "), Math(SourceSequence()),
        Text(" log-concave (or Pólya frequency two – "),
        Math(new Formula.Subscript(F.Id("PF"), Num(2))),
        Text(", or doubly positive) if "),
        Math(new Formula.Relation(
            Seq(F.Id("f"), Underscore, Grp(F.Id("k")), Caret, Grp(Num(2))),
            FormulaRelationOperator.GreaterThanOrEqual,
            Seq(new Formula.Subscript(F.Id("f"), Subtract(F.Id("k"), Num(1))),
                new Formula.Subscript(F.Id("f"), Add(F.Id("k"), Num(1)))))),
        Text(" for each "), Math(Seq(F.Id("k"), InMacro, Sp, Mathbb, Grp(F.Id("N")))),
        Text(", and "), Math(SourceSequence()),
        Text(" is supported on an interval of integers (i.e., "),
        Math(Equal(new Formula.Subscript(F.Id("f"), F.Id("N")), Num(0))),
        Text(" implies either "),
        Math(Equal(new Formula.Subscript(F.Id("f"), Add(F.Id("N"), F.Id("i"))), Num(0))),
        Text(" for all "),
        Math(Seq(F.Id("i"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Underscore, Grp(Num(0)))),
        Text(" or "),
        Math(Equal(new Formula.Subscript(F.Id("f"), Subtract(F.Id("N"), F.Id("i"))), Num(0))),
        Text(" for "),
        Math(Seq(F.Id("i"), Eq, Num(0), Comma, Dot, Dot, Dot, Comma, F.Id("N"))),
        Text(")."));

    private static Formula SourceSequence() =>
        Seq(OpenBrace, new Formula.Subscript(F.Id("f"), F.Id("k")), CloseBrace,
            Underscore, Grp(F.Id("k"), Eq, Num(0)), Caret, Grp(Infty));
}
