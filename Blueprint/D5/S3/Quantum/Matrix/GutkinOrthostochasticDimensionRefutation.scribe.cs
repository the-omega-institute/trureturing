using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class GutkinOrthostochasticDimensionRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/gutkin2013orthostochastic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Star matrices contradict an eventual upper bound of three on Gutkin's internal dimension.",
        H("Star matrices force large orthostochastic dimension"),
        Blocks(
            Paragraph(Text(
                "Rows and columns are indexed by Fin n, with values 0 through n − 1; the first index is the row. "
                    + "This corresponds to the upper index in Gutkin's notation, whose lower index denotes the column. "
                    + "EuclideanSpace ℝ (Fin d) is the real d-dimensional Euclidean space. "
                    + "The set Matrix.doublyStochastic ℝ (Fin n) consists of real n by n matrices with nonnegative "
                    + "entries and every row and column summing to one.")),
            Entry("gutkin-lift", "IsGutkinLift", "Norms and two orthogonality systems", LiftFormula(),
                "Lemma 1, equations (1)–(2), and the definition of Iso and ν prescribe the two orthogonality "
                    + "systems and the entrywise squared norms. The sum over r is column orthogonality, and "
                    + "the sum over c is row orthogonality. Both systems are required here; their equivalence "
                    + "is not assumed. The right-hand side is one for equal indices and zero otherwise.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("gutkin-orthostochastic", "IsOrthostochasticOfDim", "Real d-orthostochastic matrices",
                OrthostochasticFormula(),
                "Definition 1 calls a bistochastic matrix P real d-orthostochastic when P = ν(V) for "
                    + "a vector-valued matrix V in Iso(ℝ,n,d). Thus bistochasticity is required together with "
                    + "a lift satisfying the norm equations and both orthogonality systems.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("gutkin-dmin", "dMin", "The infimum of the universal dimensions", DimensionFormula(),
                "Conjecture 1 defines d_min(n) as the smallest internal dimension for which every "
                    + "bistochastic n by n matrix is d-orthostochastic. The formula uses the infimum in ℕ "
                    + "of exactly that set of dimensions. A nonempty subset of ℕ contains its infimum; "
                    + "the infimum of the empty set in ℕ is zero.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("gutkin-claim", "claim", "Gutkin's eventual dimension bound", ClaimFormula(),
                "Conjecture 1 asserts that there exists a threshold n₀ such that "
                    + "2 ≤ d_min(n) ≤ 3 for every n ≥ n₀, over the real field.",
                AssessedProvenance.FromLiterature(Source)),
            Entry("gutkin-star-matrix", "starMatrix", "A symmetric star matrix", StarFormula(),
                "For n ≥ 2, put a = 1/(n − 1). The central diagonal entry is zero, every edge from "
                    + "the central index 0 has weight a, and every other diagonal entry has weight 1 − a. "
                    + "All remaining entries vanish. This matrix tests the universal dimension bound "
                    + "in Gutkin's conjecture. The formula defines it for every natural n: the subtraction "
                    + "n − 1 is performed in ℕ before coercion to ℝ, and real division by zero is zero.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("gutkin-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The eventual dimension bound is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(V("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For n ≥ 2 let S = starMatrix(n) and a = 1/(n − 1). Its entries are S₀₀ = 0, "
                            + "S₀ⱼ = Sⱼ₀ = a for j ≠ 0, Sⱼⱼ = 1 − a for j ≠ 0, and zero elsewhere. "
                            + "They are nonnegative. Row 0 sums to (n − 1)a = 1; every other row sums "
                            + "to a + (1 − a) = 1. Symmetry gives the same column sums, so S is bistochastic.")),
                    Paragraph(Text(
                        "Suppose V lifts S in ℝᵈ. Fix distinct nonzero columns j and k. For a row r ≠ 0, "
                            + "if r = j then Sᵣₖ = 0, while if r ≠ j then Sᵣⱼ = 0. "
                            + "The norm equations make the corresponding vector zero, so every cross term "
                            + "⟨Vᵣⱼ,Vᵣₖ⟩ vanishes except possibly the term in row 0. "
                            + "Column orthogonality therefore gives ⟨V₀ⱼ,V₀ₖ⟩ = 0.")),
                    Paragraph(Text(
                        "For each j ≠ 0 the norm equation gives ‖V₀ⱼ‖² = a > 0. The n − 1 vectors "
                            + "V₀ⱼ are thus nonzero and pairwise orthogonal. They are linearly independent "
                            + "in the d-dimensional real Euclidean space, which forces n − 1 ≤ d.")),
                    Paragraph(Text(
                        "Assume the conjectured threshold n₀ exists and take n = max(n₀,5). Then "
                            + "2 ≤ dMin(n) ≤ 3. The set defining dMin(n) cannot be empty, since its "
                            + "infimum would then be zero. Its natural-number infimum belongs to it, "
                            + "so S has a lift in dimension dMin(n). The dimension bound gives "
                            + "4 ≤ n − 1 ≤ dMin(n), contradicting dMin(n) ≤ 3."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula LiftFormula()
    {
        Formula n = V("n"), d = V("d"), p = V("P"), v = V("V");
        Formula r = V("r"), c = V("c"), j = V("j"), k = V("k");
        Formula norms = All("r", Fin(n), All("c", Fin(n),
            Eqn(new Formula.Power(new Formula.Norm(Apply(v, r, c)), D(2)), Apply(p, r, c))));
        Formula columns = All("j", Fin(n), All("k", Fin(n),
            Eqn(SumOver("r", Fin(n), Inner(Apply(v, r, j), Apply(v, r, k))), DeltaEntry(j, k))));
        Formula rows = All("j", Fin(n), All("k", Fin(n),
            Eqn(SumOver("c", Fin(n), Inner(Apply(v, j, c), Apply(v, k, c))), DeltaEntry(j, k))));
        return Disp(All("n", Naturals(), All("d", Naturals(), All("P", MatrixType(n),
            All("V", LiftType(n, d),
                IffOf(Call("IsGutkinLift", p, v), And(norms, And(columns, rows))))))));
    }

    private static Formula OrthostochasticFormula()
    {
        Formula n = V("n"), d = V("d"), p = V("P");
        return Disp(All("n", Naturals(), All("d", Naturals(), All("P", MatrixType(n),
            IffOf(Call("IsOrthostochasticOfDim", d, p), And(Member(p, Bistochastic(n)),
                Some("V", LiftType(n, d), Call("IsGutkinLift", p, V("V")))))))));
    }

    private static Formula DimensionFormula()
    {
        Formula n = V("n"), d = V("d"), p = V("P");
        Formula dimensions = Seq(OpenBrace, Typed(d, Naturals()), Sp, Mid, Sp,
            All("P", MatrixType(n), Imp(Member(p, Bistochastic(n)),
                Call("IsOrthostochasticOfDim", d, p))), CloseBrace);
        return Disp(All("n", Naturals(), Eqn(Call("dMin", n), Call("sInf", dimensions))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = V("n"), n0 = V("n0");
        return Disp(IffOf(V("claim"), Some("n0", Naturals(), All("n", Naturals(),
            Imp(LE(n0, n), And(LE(D(2), Call("dMin", n)), LE(Call("dMin", n), D(3))))))));
    }

    private static Formula StarFormula()
    {
        Formula n = V("n"), r = V("r"), c = V("c");
        Formula r0 = Eqn(Apply(Qualified("Fin", "val"), r), D(0));
        Formula c0 = Eqn(Apply(Qualified("Fin", "val"), c), D(0));
        Formula rn = NE(Apply(Qualified("Fin", "val"), r), D(0));
        Formula cn = NE(Apply(Qualified("Fin", "val"), c), D(0));
        Formula a = new Formula.Fraction(D(1), Typed(Typed(Subtract(n, D(1)), Naturals()), Reals()));
        Formula entries = Seq(Begin, Grp(V("cases")),
            D(0), Amp, And(r0, c0), RowBreak,
            a, Amp, And(r0, cn), RowBreak,
            a, Amp, And(rn, c0), RowBreak,
            Subtract(D(1), a), Amp, And(rn, And(cn, Eqn(r, c))), RowBreak,
            D(0), Amp, And(rn, And(cn, NE(r, c))),
            End, Grp(V("cases")));
        return Disp(All("n", Naturals(), All("r", Fin(n), All("c", Fin(n),
            Eqn(Apply(Call("starMatrix", n), r, c), entries)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula MatrixType(Formula n) => Call("Matrix", Fin(n), Fin(n), Reals());
    private static Formula LiftType(Formula n, Formula d) =>
        Arrow(Fin(n), Arrow(Fin(n), Call("EuclideanSpace", Reals(), Fin(d))));
    private static Formula Bistochastic(Formula n) => Apply(Qualified("Matrix", "doublyStochastic"), Reals(), Fin(n));
    private static Formula Qualified(string space, string name) => Seq(Operatorname, Grp(V(space), Dot, V(name)));
    private static Formula Call(string name, params Formula[] arguments) => Apply(V(name), arguments);
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Arrow(Formula domain, Formula codomain) => Seq(domain, Sp, To, Sp, Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula SumOver(string name, Formula type, Formula summand) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, summand);
    private static Formula Inner(Formula left, Formula right) => Seq(Langle, left, Comma, Sp, right, Rangle);
    private static Formula DeltaEntry(Formula j, Formula k) => Seq(Begin, Grp(V("cases")),
        D(1), Amp, Eqn(j, k), RowBreak, D(0), Amp, NE(j, k), End, Grp(V("cases")));
}
