using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class MaxKCutQuboPenaltyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/MaxKCutQuboPenalty.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/harkness2025qubomaxkcut");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For max k-cut with real edge weights, every optimal solution of the one-hot QUBO reformulation is an optimal k-cut as soon as each penalty c_v exceeds max(d+_v / k, -d-_v / 2), and every optimal solution of the reduced R-QUBO reformulation is one as soon as c_v exceeds d+_v - d-_v, where d+_v and d-_v are the sums of the positive and of the negative weights at v. These are Conjectures 1 and 2 of A. Harkness et al. (arXiv:2511.01108), who proved the bounds with -(3/2) d-_v and -2 d-_v.",
        H("Tight penalty coefficients for the QUBO reformulations of max k-cut"),
        Blocks(
            Node("ind", "Binary variables", IndFormula(),
                "A Boolean entry x_vj is read as the number 1 or 0.",
                "ind", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("dplus", "Positive weighted degree", DegreeFormula("dplus", true),
                "The sum of the positive weights w(u, v) over the vertices u other than v.",
                "dplus", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("dminus", "Negative weighted degree", DegreeFormula("dminus", false),
                "The sum of the negative weights w(u, v) over the vertices u other than v.",
                "dminus", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cut", "The BQO objective", CutFormula(),
                "The weight of the edges u < v whose endpoints share no part, written as in the BQO formulation of max k-cut.",
                "cutValue", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("qubo", "The QUBO objective", QuboFormula(),
                "The BQO objective minus the penalty c_v (sum_j x_vj - 1)^2 at every vertex.",
                "quboObjective", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("onehot", "BQO feasibility", OneHotFormula("OneHot", FormulaRelationOperator.Equal),
                "Every vertex lies in exactly one part.",
                "OneHot", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rcut", "The R-BQO objective", ReducedCutFormula(),
                "The reduced formulation keeps k - 1 columns; a vertex with no column set lies in the last part, so an edge is cut unless its endpoints share a column or both have none.",
                "reducedCutValue", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rqubo", "The R-QUBO objective", ReducedQuboFormula(),
                "The R-BQO objective minus the penalty c_v sum_{i<j} x_vi x_vj at every vertex.",
                "reducedQuboObjective", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("atmostone", "R-BQO feasibility",
                OneHotFormula("AtMostOneHot", FormulaRelationOperator.LessThanOrEqual),
                "Every vertex has at most one of the k - 1 columns set.",
                "AtMostOneHot", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conj1", "Conjecture 1", Conjecture1Formula(),
                "For k at least 3 (the scope of the paper) and symmetric real weights, if c_v > max(d+_v / k, -d-_v / 2) for every vertex, then every maximiser of the QUBO objective over all Boolean matrices is one-hot and maximises the BQO objective among one-hot matrices.",
                "quboPenaltyConjecture", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conj2", "Conjecture 2", Conjecture2Formula(),
                "For m = k - 1 at least 2 columns and symmetric real weights, if c_v > d+_v - d-_v for every vertex, then every maximiser of the R-QUBO objective has at most one column set at each vertex and maximises the R-BQO objective among such matrices.",
                "reducedQuboPenaltyConjecture", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Both conjectures", Disp(Iff(F.Id("claim"),
                    And(Named(F.Id("quboPenaltyConjecture")), Named(F.Id("reducedQuboPenaltyConjecture"))))),
                "The conjunction of Conjectures 1 and 2.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of both conjectures", Disp(F.Id("claim")),
                "Let t_v be the number of parts of v in an optimal x, and suppose some vertex has t_v at least 2. For each colour j delete j from every vertex with two or more colours, and add up the changes of the objective over all k colours. The penalty of such a vertex drops by c_v t_v (2 t_v - 3) in total, and an edge touching such a vertex loses w_uv times the number of its shared colours. That number is at most half the sum of t (2t - 3) over the endpoints with two or more colours, so the edges with negative weight cost at most -d-_v / 2 times t_v (2 t_v - 3) at each such vertex, and the edges with positive weight only help. The total is therefore at least the sum of (c_v + d-_v / 2) t_v (2 t_v - 3), which is positive, so one of the deletions improves x, a contradiction. If some vertex had no colour, giving it colour i gains c_v minus the weight of its neighbours of colour i, which is at least k c_v - d+_v > 0 when summed over i. So x is one-hot and, since the penalty vanishes on one-hot matrices, an optimal k-cut. For the reduced objective the same deletion changes each edge term by at most s_u (s_u - 1) + s_v (s_v - 1) in absolute value and each penalty by c_v s_v (s_v - 1), where s_v is the number of columns set, so the total gain is at least the sum of (c_v - d+_v + d-_v) s_v (s_v - 1) > 0.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("qubo-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Minus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula n) => Call(F.Id("Fin"), n);
    private static Formula W(Formula u, Formula v) => new Formula.Apply(F.Id("w"), [u, v]);
    private static Formula Ind(Formula x, Formula v, Formula j) =>
        Call(F.Id("ind"), new Formula.Apply(x, [v, j]));
    private static Formula RowSum(Formula x, Formula v) =>
        SumOver(F.Id("j"), Ind(x, v, F.Id("j")));
    private static Formula Overlap(Formula x, Formula u, Formula v) =>
        SumOver(F.Id("j"), Times(Ind(x, u, F.Id("j")), Ind(x, v, F.Id("j"))));
    private static Formula PairIndex() => Seq(F.Id("u"), Sp, Lt, Sp, F.Id("v"));

    private static Formula IndFormula()
    {
        Formula b = F.Id("b");
        return Disp(Equal(Call(F.Id("ind"), b), Seq(Named(F.Id("if")), Sp, b, Sp,
            Named(F.Id("then")), Sp, D(1), Sp, Named(F.Id("else")), Sp, D(0))));
    }

    private static Formula DegreeFormula(string name, bool positive)
    {
        Formula u = F.Id("u"), v = F.Id("v");
        Formula sign = positive ? Seq(D(0), Sp, Lt, Sp, W(u, v)) : Seq(W(u, v), Sp, Lt, Sp, D(0));
        Formula index = Seq(u, Sp, Neq, Sp, v, Comma, Sp, sign);
        return Disp(Equal(Call(F.Id(name), F.Id("w"), v), SumOver(index, W(u, v))));
    }

    private static Formula CutBody(Formula x)
    {
        Formula u = F.Id("u"), v = F.Id("v");
        return SumOver(PairIndex(), Times(W(u, v), Parenthesized(Minus(D(1), Overlap(x, u, v)))));
    }

    private static Formula CutFormula() =>
        Disp(Equal(Call(F.Id("cutValue"), F.Id("w"), F.Id("x")), CutBody(F.Id("x"))));

    private static Formula QuboFormula()
    {
        Formula x = F.Id("x"), v = F.Id("v");
        Formula penalty = SumOver(v, Times(new Formula.Apply(F.Id("c"), [v]),
            new Formula.Power(Parenthesized(Minus(RowSum(x, v), D(1))), D(2))));
        return Disp(Equal(Call(F.Id("quboObjective"), F.Id("w"), F.Id("c"), x),
            Minus(Call(F.Id("cutValue"), F.Id("w"), x), penalty)));
    }

    private static Formula OneHotFormula(string name, FormulaRelationOperator op)
    {
        Formula x = F.Id("x"), v = F.Id("v");
        return Disp(Iff(Call(F.Id(name), x), All("v", FinOf(F.Id("n")), Rel(RowSum(x, v), op, D(1)))));
    }

    private static Formula ReducedCutFormula()
    {
        Formula x = F.Id("x"), u = F.Id("u"), v = F.Id("v");
        Formula empty = Times(Parenthesized(Minus(D(1), RowSum(x, u))),
            Parenthesized(Minus(D(1), RowSum(x, v))));
        Formula term = Times(W(u, v), Parenthesized(Minus(Minus(D(1), Overlap(x, u, v)), empty)));
        return Disp(Equal(Call(F.Id("reducedCutValue"), F.Id("w"), x), SumOver(PairIndex(), term)));
    }

    private static Formula ReducedQuboFormula()
    {
        Formula x = F.Id("x"), v = F.Id("v"), i = F.Id("i"), j = F.Id("j");
        Formula pairs = SumOver(Seq(i, Sp, Lt, Sp, j),
            Times(Ind(x, v, i), Ind(x, v, j)));
        Formula penalty = SumOver(v, Times(new Formula.Apply(F.Id("c"), [v]), pairs));
        return Disp(Equal(Call(F.Id("reducedQuboObjective"), F.Id("w"), F.Id("c"), x),
            Minus(Call(F.Id("reducedCutValue"), F.Id("w"), x), penalty)));
    }

    private static Formula Conjecture(string name, string columnName, Formula columnBound,
        Formula penaltyBound, string objective, string cut, string feasible)
    {
        Formula n = F.Id("n"), w = F.Id("w"), c = F.Id("c"), u = F.Id("u"), v = F.Id("v");
        Formula x = F.Id("x"), xh = F.Id("xh"), columns = F.Id(columnName);
        Formula matrices = new Formula.TypeArrow(FinOf(n),
            new Formula.TypeArrow(FinOf(columns), Named(F.Id("Bool"))));
        Formula symmetric = All("u", FinOf(n), All("v", FinOf(n), Equal(W(u, v), W(v, u))));
        Formula penalties = All("v", FinOf(n),
            Rel(penaltyBound, FormulaRelationOperator.LessThan, new Formula.Apply(c, [v])));
        Formula optimal = All("x", matrices, Rel(Call(F.Id(objective), w, c, x),
            FormulaRelationOperator.LessThanOrEqual, Call(F.Id(objective), w, c, xh)));
        Formula conclusion = And(Call(F.Id(feasible), xh), All("x", matrices,
            Implies(Call(F.Id(feasible), x), Rel(Call(F.Id(cut), w, x),
                FormulaRelationOperator.LessThanOrEqual, Call(F.Id(cut), w, xh)))));
        Formula body = Implies(columnBound, Implies(symmetric, Implies(penalties,
            All("xh", matrices, Implies(optimal, conclusion)))));
        Formula weights = new Formula.TypeArrow(FinOf(n), new Formula.TypeArrow(FinOf(n), Reals()));
        return Disp(Iff(F.Id(name), All("n", Naturals(), All(columnName, Naturals(),
            All("w", weights, All("c", new Formula.TypeArrow(FinOf(n), Reals()), body))))));
    }

    private static Formula Conjecture1Formula()
    {
        Formula k = F.Id("k"), w = F.Id("w"), v = F.Id("v");
        Formula bound = Call(F.Id("max"),
            new Formula.Fraction(Call(F.Id("dplus"), w, v), k),
            new Formula.Fraction(new Formula.Negate(Call(F.Id("dminus"), w, v)), D(2)));
        return Conjecture("quboPenaltyConjecture", "k",
            Rel(D(3), FormulaRelationOperator.LessThanOrEqual, k), bound,
            "quboObjective", "cutValue", "OneHot");
    }

    private static Formula Conjecture2Formula()
    {
        Formula m = F.Id("m"), w = F.Id("w"), v = F.Id("v");
        Formula bound = Minus(Call(F.Id("dplus"), w, v), Call(F.Id("dminus"), w, v));
        return Conjecture("reducedQuboPenaltyConjecture", "m",
            Rel(D(2), FormulaRelationOperator.LessThanOrEqual, m), bound,
            "reducedQuboObjective", "reducedCutValue", "AtMostOneHot");
    }
}
