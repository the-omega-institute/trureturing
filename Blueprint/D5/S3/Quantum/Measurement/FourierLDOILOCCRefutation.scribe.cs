using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FourierLDOILOCCRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/FourierLDOILOCCRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/johnston2026ldoi");
    private static readonly LibraryNoteRef LOCC =
        LibraryNoteRef.Create("D5/L/QuantumBounds/chitambar2014locc");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Johnston and Russo ask whether their lower bound for the uniform Fourier LDOI ensemble is tight. In local dimension three a finite tree of complete local Kraus instruments has success probability 1/2, exceeding the proposed value 4/9. This refutes the universal tightness assertion.",
        H("The Fourier LDOI LOCC lower bound is not tight"),
        Blocks(
            Node("fourier", "Normalized Fourier entries", FourierFormula(),
                "Example 17, p. 18: \"Let n ≥ 3 and consider an orthonormal LDOI basis arising from Definition 6 with A = (1/√2)1ₙ (the all-ones matrix scaled by 1/√2) and U equal to the n-dimensional Fourier matrix.\" The entries use zero-based Fin n indices and the positive exponential convention. The square root is real; the exponent and the divisor are complex.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("phi", "The Fourier LDOI vectors", PhiFormula(),
                "Definition 6, p. 9, Eq. (21), specialized as in Example 17: \"Define the uniform ensemble E = {(1/n², |ϕᵢⱼ⟩⟨ϕᵢⱼ|) : 1 ≤ i, j ≤ n}, where |ϕᵢⱼ⟩ are the basis vectors.\" Diagonal labels give the Fourier superpositions of |kk⟩. For i < j the two ordered labels give (|ij⟩ + |ji⟩)/√2 and (|ij⟩ − |ji⟩)/√2. Pi.single is the coordinate basis vector. All functions below have carrier Fin n × Fin n → ℂ.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Protocol", "Finite-round local Kraus trees", ProtocolFormula(),
                "The inductive type has precisely leaf, alice and bob constructors. A leaf reports an ordered label. Each internal node applies a complete square local Kraus instrument on its indicated side and chooses a child from the classical outcome. Instruments farther down a tree may depend on the entire preceding outcome history. The displayed constructor telescopes describe these generators; the carrier is the inductive type, with no additional constructors.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("actA", "Alice's local action", ActionFormula(true),
                "Alice multiplies the first coordinate, leaving the second coordinate fixed. Vectors are unnormalized after an outcome, so their squared norm includes the branch probability.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("actB", "Bob's local action", ActionFormula(false),
                "Bob multiplies the second coordinate, leaving the first coordinate fixed.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("mass", "Squared Euclidean norm", MassFormula(),
                "The squared norm is the sum of Complex.normSq over every coordinate, rather than the norm of the product-space function with the supremum norm.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("score", "Correct-leaf mass", ScoreFormula(),
                "The recursion sums the squared norms of the leaves whose guesses equal the supplied label. At every internal node the unnormalized vector is passed through its local Kraus operator. Repeated recursion therefore applies the product of the operators on each path.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("success", "Uniform success probability", SuccessFormula(),
                "Example 17, p. 18: \"Define the uniform ensemble E = {(1/n², |ϕᵢⱼ⟩⟨ϕᵢⱼ|) : 1 ≤ i, j ≤ n}, where |ϕᵢⱼ⟩ are the basis vectors.\" Section 1, p. 4, defines the success probability as the prior-weighted probability of reporting the correct state. Here the prior is 1/n², and all n² labels are included, even though the counterexample never reports a diagonal label.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("optLOCC", "The LOCC optimization supremum", OptLOCCFormula(),
                "Section 1, p. 4: \"We use the notation optPPT(E) and optSEP(E) for the optimal success probabilities under PPT and separable measurements, and optLOCC(E) for the supremum over LOCC measurements (since LOCC is not topologically closed, the supremum may not be attained).\" Here optLOCC is the supremum over finite-round LOCC (LOCC_ℕ) trees with dimension-preserving local Kraus instruments. Chitambar–Leung–Mančinska–Ozols–Winter, Section 2.2, gives LOCC_ℕ ⊆ LOCC ⊆ cl(LOCC_ℕ); success is a continuous linear functional of the measurement, so the supremum equals that over all LOCC measurements. Every finite-round LOCC measurement has this tree form, since each Kraus operator's output space pulls back by polar decomposition. These carrier correspondences are arguments on paper, not Lean theorems. The completeness of every local instrument bounds each tree's success probability by one.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source, LOCC)),
            Node("lower", "The lower bound in Equation (61)", LowerFormula(),
                "Example 17, p. 18, Eq. (61), gives this lower bound and the PPT upper bound 1/2. Every arithmetic operation displayed here takes place in ℝ, with n coerced from ℕ.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The tightness equality", ClaimFormula(),
                "Example 17, p. 19: \"Whether the lower bound in Equation (61) is tight—that is, whether opt_LOCC(E) = 1/2 − (n − 2)/(2n²)—remains an open question.\" The encoding asserts this equality for every n ≥ 3, with optLOCC the supremum over finite-round LOCC trees with dimension-preserving local Kraus instruments. Every finite-round LOCC measurement has this form, since each Kraus operator's output space pulls back by polar decomposition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Tightness fails", Disp(new Formula.Not(F.Id("claim"))),
                "At n = 3 Alice first selects an unordered pair with its diagonal projector divided by √2. Bob tests membership in that pair. Inside it a shared fair choice of X or Y measurements resolves the symmetric and antisymmetric labels; outside it computational outcomes and a fair sign guess are used. The X and Y instruments include the complementary level as a third outcome and reset measured factors using |0⟩⟨x|. A zero-probability branch receives the fixed label (0,1). All local instruments are complete. Each of the six off-diagonal states has correct-leaf mass 3/4, and all three diagonal states have correct-leaf mass zero. The uniform success is therefore (6 · 3/4)/9 = 1/2, while lower(3) = 4/9. Local completeness and induction on the tree bound every success probability by one, so the supremum is bounded and optLOCC(3) ≥ 1/2 > lower(3). Only this dimension-three refutation is asserted; an all-dimension family and the exact optimization value are separate statements.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("jr-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Of(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) => new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula AddTo(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula SubTo(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Arrow(Formula from, Formula to) => Seq(Parenthesized(from), Sp, To, Sp, to);
    private static Formula All(Formula variable, Formula type, Formula body) => Seq(Forall, Sp, variable, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Labels(Formula n) => Seq(Fin(n), Sp, Times, Sp, Fin(n));
    private static Formula Vector(Formula n) => Arrow(Labels(n), Complex());
    private static Formula Mat(Formula n) => Call("Matrix", Fin(n), Fin(n), Complex());
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula First(Formula x) => Seq(x, Dot, D(1));
    private static Formula Second(Formula x) => Seq(x, Dot, D(2));
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Sp, Colon, Sp, type));
    private static Formula SumOver(Formula variable, Formula type, Formula body) => Seq(Sum, Underscore, Grp(Seq(variable, Sp, Colon, Sp, type)), Sp, body);
    private static Formula If(Formula condition, Formula yes, Formula no) => Seq(
        Operatorname, Grp(F.Id("if")), Sp, Parenthesized(condition), Sp,
        Operatorname, Grp(F.Id("then")), Sp, Parenthesized(yes), Sp,
        Operatorname, Grp(F.Id("else")), Sp, Parenthesized(no));
    private static Formula Complete(Formula k, Formula m, Formula a) => EqTo(
        SumOver(a, Fin(m), Mul(Of(Qualified("Matrix", "conjTranspose"), Of(k, a)), Of(k, a))), D(1));

    private static Formula FourierFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), k = F.Id("k");
        Formula exponent = Frac(Mul(Mul(Mul(Mul(D(2), Qualified("Real", "pi")), Qualified("Complex", "I")),
            Cast(Call("val", i), Complex())), Cast(Call("val", k), Complex())), Cast(n, Complex()));
        Formula value = Frac(Of(Qualified("Complex", "exp"), exponent),
            Cast(Of(Qualified("Real", "sqrt"), Cast(n, Real())), Complex()));
        return Disp(All(n, Nat(), All(i, Fin(n), All(k, Fin(n), EqTo(Call("fourier", n, i, k), value)))));
    }

    private static Formula PhiFormula()
    {
        Formula n = F.Id("n"), l = F.Id("l"), p = F.Id("p");
        Formula basis1 = Of(Qualified("Pi", "single"), Pair(First(l), Second(l)), D(1), p);
        Formula basis2 = Of(Qualified("Pi", "single"), Pair(Second(l), First(l)), D(1), p);
        Formula root = Cast(Of(Qualified("Real", "sqrt"), D(2)), Complex());
        Formula diagonal = If(EqTo(First(p), Second(p)), Call("fourier", n, First(l), First(p)), D(0));
        Formula cross = If(Rel(First(l), FormulaRelationOperator.LessThan, Second(l)),
            Frac(AddTo(basis1, basis2), root), Frac(SubTo(basis2, basis1), root));
        return Disp(All(n, Nat(), All(l, Labels(n), All(p, Labels(n),
            EqTo(Of(Call("phi", l), p), If(EqTo(First(l), Second(l)), diagonal, cross))))));
    }

    private static Formula ProtocolFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), g = F.Id("g"), k = F.Id("K"),
            h = F.Id("h"), next = F.Id("next"), a = F.Id("a");
        Formula protocol = Call("Protocol", n);
        Formula leaf = All(n, Nat(), All(g, Labels(n), Seq(Of(Qualified("Protocol", "leaf"), g), Sp, Colon, Sp, protocol)));
        Formula Constructor(string side) => All(n, Nat(), All(m, Nat(),
            All(k, Arrow(Fin(m), Mat(n)), All(h, Parenthesized(Complete(k, m, a)),
                All(next, Arrow(Fin(m), protocol), Seq(Of(Qualified("Protocol", side), k, h, next), Sp, Colon, Sp, protocol))))));
        return Disp(new Formula.Aligned([leaf, Constructor("alice"), Constructor("bob")]));
    }

    private static Formula ActionFormula(bool alice)
    {
        Formula n = F.Id("n"), k = F.Id("K"), v = F.Id("v"), p = F.Id("p"), a = F.Id("a");
        Formula term = alice ? Mul(Of(k, First(p), a), Of(v, Pair(a, Second(p))))
            : Mul(Of(k, Second(p), a), Of(v, Pair(First(p), a)));
        return Disp(All(n, Nat(), All(k, Mat(n), All(v, Vector(n), All(p, Labels(n),
            EqTo(Of(Call(alice ? "actA" : "actB", k, v), p), SumOver(a, Fin(n), term)))))));
    }

    private static Formula MassFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v"), p = F.Id("p");
        return Disp(All(n, Nat(), All(v, Vector(n), EqTo(Call("mass", v),
            SumOver(p, Labels(n), Of(Qualified("Complex", "normSq"), Of(v, p)))))));
    }

    private static Formula ScoreFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m"), l = F.Id("l"), v = F.Id("v"), g = F.Id("g"),
            k = F.Id("K"), h = F.Id("h"), next = F.Id("next"), a = F.Id("a");
        Formula leaf = All(n, Nat(), All(l, Labels(n), All(v, Vector(n), All(g, Labels(n),
            EqTo(Call("score", l, Of(Qualified("Protocol", "leaf"), g), v), If(EqTo(g, l), Call("mass", v), D(0)))))));
        Formula Step(string side, string action) => All(n, Nat(), All(m, Nat(), All(l, Labels(n),
            All(v, Vector(n), All(k, Arrow(Fin(m), Mat(n)), All(h, Parenthesized(Complete(k, m, a)),
                All(next, Arrow(Fin(m), Call("Protocol", n)),
                    EqTo(Call("score", l, Of(Qualified("Protocol", side), k, h, next), v),
                        SumOver(a, Fin(m), Call("score", l, Of(next, a), Call(action, Of(k, a), v)))))))))));
        return Disp(new Formula.Aligned([leaf, Step("alice", "actA"), Step("bob", "actB")]));
    }

    private static Formula SuccessFormula()
    {
        Formula n = F.Id("n"), t = F.Id("T"), l = F.Id("l");
        Formula value = Mul(Frac(D(1), Pow(Cast(n, Real()), D(2))),
            Parenthesized(SumOver(l, Labels(n), Call("score", l, t, Call("phi", l)))));
        return Disp(All(n, Nat(), All(t, Call("Protocol", n), EqTo(Call("success", n, t), value))));
    }

    private static Formula LowerFormula()
    {
        Formula n = F.Id("n");
        Formula value = SubTo(Frac(D(1), D(2)),
            Frac(SubTo(Cast(n, Real()), D(2)), Mul(D(2), Pow(Cast(n, Real()), D(2)))));
        return Disp(All(n, Nat(), EqTo(Call("lower", n), value)));
    }

    private static Formula OptLOCCFormula()
    {
        Formula n = F.Id("n");
        Formula value = Call("sSup", Of(Qualified("Set", "range"), Call("success", n)));
        return Disp(All(n, Nat(), EqTo(Call("optLOCC", n), value)));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula body = All(n, Nat(), Imp(Rel(D(3), FormulaRelationOperator.LessThanOrEqual, n),
            EqTo(Call("optLOCC", n), Call("lower", n))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(body)));
    }
}
