using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class FidelityMeasurementROCRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/bodorkoniorczyk2017quantumroc");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-dimensional fidelity measurement point lies below the optimal quantum ROC curve.",
        H("The Fuchs–Caves fidelity ROC question is refuted"),
        Blocks(
            Node("on-optimal-roc", "The optimal ROC boundary at a fixed false-positive coordinate",
                OnOptimalROCFormula(),
                "The source describes the feasible ROC domain as convex and calls its upper boundary the optimal ROC curve (TeX lines 289–300). For a matrix test f, onOptimalROC requires every effect between zero and the identity whose false-positive coordinate is x to have true-positive coordinate at most y.",
                "onOptimalROC", AssessedProvenance.FromLiterature(Source)),
            Node("fidelity-observable", "The Fuchs–Caves fidelity observable",
                FidelityObservableFormula(),
                "The observable is the matrix in equation (44), TeX lines 932–940: the inverse of the positive square root of the first state, followed by the positive square root of the sandwich with the second state, followed by the same inverse.",
                "fidelityObservable", AssessedProvenance.FromLiterature(Source)),
            Node("cumulative", "Cumulative measurement probability",
                CumulativeFormula(),
                "The source forms cumulative ROC coordinates by summing the ordered outcome probabilities (TeX lines 383–392). The definition sums the readout of m on the first k indices of the matrix-valued outcome family a.",
                "cumulative", AssessedProvenance.FromLiterature(Source)),
            Node("ordered-eigenbasis", "An ordered eigenbasis of the fidelity observable",
                OrderedEigenbasisFormula(),
                "The source orders measurement outcomes by decreasing likelihood ratio p_i/q_i (TeX lines 329–335). This predicate requires normalized rows, pairwise orthogonality, eigenvector equations for the fidelity observable, and the corresponding likelihood-ratio ordering.",
                "isOrderedFidelityEigenbasis", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("fidelity-measurement-roc-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Every cumulative fidelity point is optimal"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The formal question asserts that for every finite dimension, every pair of positive-definite trace-one complex matrices, every ordered orthonormal eigenbasis of the fidelity observable, and every k in Fin(d + 1), the cumulative point is on the optimal ROC boundary."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fidelity-measurement-roc-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A qutrit counterexample"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use the displayed three-dimensional states with entries 1/20 times [[2,1,1],[1,10,1],[1,1,8]] and 1/40 times [[16,4,2],[4,20,1],[2,1,4]], and use the diagonal observable diag(2,1,1/2). The first state is positive definite because its unscaled matrix is the sum of the all-ones rank-one matrix and a positive diagonal matrix; the second is a positive diagonal congruence of the first. Direct trace calculation gives trace one for both.")),
                    Paragraph(Text(
                        "The positive square-root uniqueness argument identifies the Fuchs–Caves observable with the displayed diagonal matrix. Its coordinate basis is an ordered eigenbasis: the eigenvalues are 2, 1 and 1/2, while the readout probabilities are q = (1/10, 1/2, 2/5) and p = (2/5, 1/2, 1/10), so the likelihood ratios decrease as 4, 1, 1/4. At k = 1 the cumulative point is (1/10, 2/5).")),
                    Paragraph(Text(
                        "Take the rank-one effect vvᵀ/1382 with v = (37,2,−3). Its positive-semidefinite and upper-bound certificates place it in the interval [0,1]. Exact multiplication gives false-positive coordinate 1/10 and true-positive coordinate 5539/13820, while 2/5 is 5528/13820. Applying the claimed optimality at k = 1 would therefore give 5539/13820 ≤ 2/5, which is false."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bodor-koniorczyk-2017-fidelity-measurement-roc-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("fidelity-roc-" + id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula OnOptimalROCFormula()
    {
        Formula d = X("d"), rho = RhoSymbol(), sigma = SigmaSymbol(), x = X("x"), y = X("y"), f = X("f");
        Formula body = All("f", MatrixType(d),
            Implies(Member(f, Interval(Typed(D(0), MatrixType(d)), Typed(D(1), MatrixType(d)))),
                Implies(Equal(TraceRe(Multiply(f, rho)), x),
                    LE(TraceRe(Multiply(f, sigma)), y))));
        return All("d", Naturals(), AllSymbol(rho, MatrixType(d), AllSymbol(sigma, MatrixType(d),
            All("x", Reals(), All("y", Reals(),
                Iff(LocalCall("onOptimalROC", rho, sigma, x, y), body))))));
    }

    private static Formula FidelityObservableFormula()
    {
        Formula d = X("d"), rho = RhoSymbol(), sigma = SigmaSymbol();
        Formula root = At(Qualified("CFC", "sqrt"), rho);
        Formula inverse = At(Qualified("Inv", "inv"), root);
        Formula sandwich = Multiply(Multiply(root, sigma), root);
        Formula rhs = Multiply(Multiply(inverse, At(Qualified("CFC", "sqrt"), sandwich)), inverse);
        return All("d", Naturals(), AllSymbol(rho, MatrixType(d), AllSymbol(sigma, MatrixType(d),
            Equal(LocalCall("fidelityObservable", rho, sigma), rhs))));
    }

    private static Formula CumulativeFormula()
    {
        Formula d = X("d"), a = X("a"), m = X("m"), k = X("k"), i = X("i");
        Formula domain = FinOf(d);
        Formula filter = At(Qualified("Finset", "filter"),
            LambdaOf("i", domain, LT(FinVal(i), FinVal(k))),
            At(Qualified("Finset", "univ"), domain));
        Formula sum = At(Qualified("Finset", "sum"), filter,
            LambdaOf("i", domain, At(Readout(), m, At(a, i))));
        return All("d", Naturals(), All("a", FamilyType(d), All("m", MatrixType(d),
            All("k", FinOf(Add(d, D(1))),
                Equal(LocalCall("cumulative", a, m, k), sum)))));
    }

    private static Formula OrderedEigenbasisFormula()
    {
        Formula d = X("d"), rho = RhoSymbol(), sigma = SigmaSymbol(), a = X("a");
        Formula i = X("i"), j = X("j"), k = X("k"), r = X("r");
        Formula domain = FinOf(d);
        Formula normalized = All("i", domain,
            Equal(SumOver("j", domain,
                Multiply(At(Qualified("star"), At(At(a, i), j)), At(At(a, i), j))),
                Typed(D(1), Complexes())));
        Formula orthogonal = All("i", domain, All("j", domain,
            Implies(Neq(i, j),
                Equal(SumOver("k", domain,
                    Multiply(At(Qualified("star"), At(At(a, i), k)), At(At(a, j), k))),
                    Typed(D(0), Complexes())))));
        Formula eigen = All("i", domain,
            Exists("r", Reals(),
                Equal(At(Qualified("Matrix", "mulVec"), LocalCall("fidelityObservable", rho, sigma), At(a, i)),
                    Smul(CastComplex(r), At(a, i)))));
        Formula ordered = All("i", domain, All("j", domain,
            Implies(LE(i, j),
                GE(Multiply(At(Readout(), sigma, At(a, i)), At(Readout(), rho, At(a, j))),
                    Multiply(At(Readout(), sigma, At(a, j)), At(Readout(), rho, At(a, i)))))));
        return All("d", Naturals(), AllSymbol(rho, MatrixType(d),
            AllSymbol(sigma, MatrixType(d),
                All("a", FamilyType(d),
                    Iff(LocalCall("isOrderedFidelityEigenbasis", rho, sigma, a),
                        And(normalized, And(orthogonal, And(eigen, ordered))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = X("d"), rho = RhoSymbol(), sigma = SigmaSymbol();
        Formula stateBody = Implies(At(Qualified("Matrix", "PosDef"), rho),
            Implies(Equal(At(Qualified("Matrix", "trace"), rho), Typed(D(1), Complexes())),
                Implies(At(Qualified("Matrix", "PosDef"), sigma),
                    Implies(Equal(At(Qualified("Matrix", "trace"), sigma), Typed(D(1), Complexes())),
                        All("a", FamilyType(d),
                            Implies(LocalCall("isOrderedFidelityEigenbasis", rho, sigma, X("a")),
                                All("k", FinOf(Add(d, D(1))),
                                    LocalCall("onOptimalROC", rho, sigma,
                                        LocalCall("cumulative", X("a"), rho, X("k")),
                                        LocalCall("cumulative", X("a"), sigma, X("k"))))))))));
        Formula universal = All("d", Naturals(), AllSymbol(rho, MatrixType(d),
            AllSymbol(sigma, MatrixType(d), stateBody)));
        return Iff(LocalCall("claim"), universal);
    }

    private static Formula ResultFormula() => new Formula.Not(Parenthesized(LocalCall("claim")));

    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurement",
        "FidelityMeasurementROCRefutation", name);
    private static Formula Readout() => Qualified("D5", "S3", "Quantum", "Recovery", "ProductPrefixRigidity", "readout");
    private static Formula X(string name) => F.Id(name);
    private static Formula RhoSymbol() => F.Rho;
    private static Formula SigmaSymbol() => F.Sigma;
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula MatrixType(Formula d) => At(Qualified("Matrix"), FinOf(d), FinOf(d), Complexes());
    private static Formula FamilyType(Formula d) => new Formula.TypeArrow(FinOf(d),
        new Formula.TypeArrow(FinOf(d), Complexes()));
    private static Formula FinOf(Formula d) => At(Qualified("Fin"), d);
    private static Formula FinVal(Formula x) => At(Qualified("Fin", "val"), x);
    private static Formula Interval(Formula lower, Formula upper) => At(Qualified("Set", "Icc"), lower, upper);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula CastComplex(Formula value) => Typed(At(Qualified("Complex", "ofReal"), value), Complexes());
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula AllSymbol(Formula symbol, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(symbol, type), Comma, Sp, Parenthesized(body));
    private static Formula Exists(string name, Formula type, Formula body) =>
        Seq(FormulaDsl.Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Neq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula GE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula value) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        At(Qualified("Finset", "sum"), At(Qualified("Finset", "univ"), type),
            LambdaOf(name, type, body));
    private static Formula TraceRe(Formula value) =>
        At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"), value));
}
