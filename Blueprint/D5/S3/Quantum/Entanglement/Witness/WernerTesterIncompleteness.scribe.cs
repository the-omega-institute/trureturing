using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class WernerTesterIncompletenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/Entropy/jivulescularciennechita2022testers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entangled Werner states with dimension at least three and parameter between one over the dimension and one half escape every pair of complex testers.",
        H("Werner states undetected by all complex testers"),
        Blocks(
            Node("is-tester", "Complex testers", IsTesterFormula(),
                "A complex tester is a complex linear contraction from the trace norm to the Euclidean norm "
                    + "that attains equality at a nonzero matrix. This expresses operator norm exactly one. "
                    + "The source defines complex testers in main.tex, lines 340–352, and the trace norm in lines 288–290.",
                "IsTester", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tensor-pair", "Pure tensors of Euclidean outputs", TensorPairFormula(),
                "The two Euclidean vectors form a pure tensor in the Bool-indexed PiTensorProduct. "
                    + "The false factor has dimension n₁ and the true factor has dimension n₂. "
                    + "Bool.rec selects the first or second vector accordingly. "
                    + "This tensor space carries the bundled projective norm.",
                "tensorPair", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("tester-image", "The tensor product image", TesterImageFormula(),
                "Expand the input in tensor products of matrix units and apply the two linear maps to the respective factors. "
                    + "Sum the resulting pure tensors with the input entries as complex scalar coefficients. "
                    + "The output belongs to the Bool-indexed PiTensorProduct of the two Euclidean spaces. "
                    + "DFunLike.coe displays evaluation of a linear map as a function. "
                    + "This is the bipartite tensor product action described in main.tex, lines 377–380.",
                "testerImage", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("separable", "Separable density matrices", SeparableFormula(),
                "A matrix is separable when it lies in the real convex hull of tensor products of positive semidefinite "
                    + "matrices of trace one. The factors may have different dimensions. "
                    + "The source discusses mixed states and their separable decompositions in main.tex, lines 288–309.",
                "Separable", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("werner", "The Werner mixture", WernerFormula(),
                "The coordinate swap F exchanges the two factors. The Werner matrix is the weighted sum of I + F and I − F "
                    + "with the displayed normalizing denominators. For d greater than one and parameter between zero and one, "
                    + "these are mixtures of the normalized symmetric and antisymmetric projections. "
                    + "The formula is from main.tex, line 946. Nat.cast explicitly includes d in the reals; "
                    + "the dots between real coefficients and complex matrices denote real scalar multiplication.",
                "werner", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Completeness without permuting indices", ClaimFormula(),
                "The bipartite completeness assertion asks for two complex testers detecting each entangled density matrix, "
                    + "in arbitrary natural dimensions, by a projective norm strictly greater than one. "
                    + "No permutation of the input indices is allowed. This is the bipartite reading of the question "
                    + "in main.tex, line 1365; a bipartite counterexample also disproves the assertion for all numbers of parties.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("werner-family", "An undetected entangled family", FamilyFormula(),
                "For d at least three and parameter in the interval from 1/d inclusive to 1/2 exclusive, "
                    + "the Werner matrix is positive semidefinite, has trace one, and is entangled. "
                    + "Every pair of complex linear contractions has image projective norm at most one, "
                    + "whether or not the contractions attain norm one.",
                "werner_family", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Complex testers are incomplete"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Local("claim")))),
                AssessedProvenance.FromRepo(Source),
                ResultProof(),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("jivulescu-lancien-nechita-2022-werner-tester-incompleteness"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(DefinitionDsl.Text(prose))), role);

    private static BlockSequence ResultProof() => Blocks(
        Paragraph(DefinitionDsl.Text(
            "Let F be the coordinate swap. For positive semidefinite matrices a and b, "
                + "the real part of the trace of F(a ⊗ b) equals the real part of the trace of ab and is nonnegative. "
                + "This real linear functional remains nonnegative on the convex hull of product density matrices, "
                + "hence on every separable matrix.")),
        Paragraph(DefinitionDsl.Text(
            "The tensor product image of any finite sum of product matrices is the sum of the pure tensors of their images. "
                + "If the two families of image vectors each have sum of squared norms at most one, "
                + "Cauchy–Schwarz bounds the sum of the products of their norms by one. "
                + "The triangle inequality and the projective seminorm bound on each pure tensor "
                + "then bound the bundled norm of the sum by one.")),
        Paragraph(DefinitionDsl.Text(
            "For positive d, use a finite ensemble of rank-one projectors P indexed by the computational basis "
                + "and by all d-tuples of fourth roots of unity. Each basis projector has weight 1/(d(d + 1)); "
                + "each projector onto a flat unit vector with those phases has weight d/((d + 1)4^d). "
                + "The weights are nonnegative and sum to one, and every projector is positive semidefinite with trace one. "
                + "The fourth-root moment identity gives the weighted tensor second moment (I + F)/(d(d + 1)). "
                + "Taking a partial trace of this identity gives the weighted mean m = I/d.")),
        Paragraph(DefinitionDsl.Text(
            "The swap is Hermitian and squares to the identity, so I + F and I − F are positive semidefinite. "
                + "Their traces are d squared plus d and d squared minus d, since the trace of F is d. "
                + "The Werner mixture is consequently positive semidefinite with trace one whenever d > 1 and 0 ≤ μ ≤ 1. "
                + "Its swap trace is 2μ − 1. For μ < 1/2 this is negative, contradicting the nonnegativity "
                + "of the swap trace on separable matrices.")),
        Paragraph(DefinitionDsl.Text(
            "Center each ensemble projector by subtracting m. Expanding the centered tensor second moment "
                + "using its mean and total weight expresses the Werner matrix as m ⊗ m minus "
                + "c times the weighted sum of the tensors (P − m) ⊗ (P − m), "
                + "where c = (d + 1 − 2μd)/(d − 1).")),
        Paragraph(DefinitionDsl.Text(
            "For any trace-norm-to-Euclidean contraction e, the squared norm of e(m) plus the weighted sum "
                + "of the squared norms of e(P − m) equals the weighted sum of the squared norms of e(P). "
                + "This follows by expanding squared differences and using the weighted mean. "
                + "Each P has trace norm one, so contraction and the total weight one bound that sum by one. "
                + "On 1/d ≤ μ < 1/2, elementary inequalities give 0 ≤ c ≤ 1.")),
        Paragraph(DefinitionDsl.Text(
            "In the product decomposition of the Werner matrix, take m on both sides for one summand. "
                + "For each projector of weight w, take the two factors to be the centered projector scaled "
                + "by the square root of cw and its negative. Their tensor product is minus cw times "
                + "the tensor square of the centered projector. The preceding squared-norm estimate, "
                + "together with 0 ≤ c ≤ 1, bounds each family's sum of squared image norms by one. "
                + "Applying the tensor product image identity and the Cauchy–Schwarz bound proves the uniform "
                + "projective norm estimate. For d ≥ 3 the parameter interval also ensures 0 ≤ μ ≤ 1, "
                + "so positivity, unit trace, entanglement, and this estimate hold together.")),
        Paragraph(DefinitionDsl.Text(
            "Finally take d = 3 and μ = 1/3. Completeness would supply testers with image projective norm "
                + "strictly greater than one for this entangled density matrix. Each tester is a contraction, "
                + "so the uniform estimate makes that same norm at most one, a contradiction.")));

    private static Formula IsTesterFormula()
    {
        Formula x = X("x");
        Formula condition = And(Contraction(X("e"), X("d")), Some("x", Square(X("d")),
            And(NotEqual(x, Typed(D(0), Square(X("d")))),
                Equal(Norm(Evaluate(X("e"), x)), TraceNorm(x)))));
        return All("d", Naturals(), All("n", Naturals(), All("e", LinearType(X("d"), X("n")),
            Equal(LocalCall("IsTester", X("e")), condition))));
    }

    private static Formula TensorPairFormula()
    {
        Formula pure = At(Qualified("PiTensorProduct", "tprod"), Complexes(),
            At(Qualified("Bool", "rec"), X("a"), X("b")));
        return All("n₁", Naturals(), All("n₂", Naturals(),
            All("a", Euclidean(X("n₁")), All("b", Euclidean(X("n₂")),
                Equal(LocalCall("tensorPair", X("a"), X("b")), pure)))));
    }

    private static Formula TesterImageFormula()
    {
        Formula entry = Smul(
            At(X("ρ"), Pair(X("i"), X("j")), Pair(X("k"), X("l"))),
            LocalCall("tensorPair",
                Evaluate(X("e₁"), At(Qualified("Matrix", "single"), X("i"), X("k"), Typed(D(1), Complexes()))),
                Evaluate(X("e₂"), At(Qualified("Matrix", "single"), X("j"), X("l"), Typed(D(1), Complexes())))));
        Formula sum = SumOver("i", FinOf(X("d₁")), SumOver("j", FinOf(X("d₂")),
            SumOver("k", FinOf(X("d₁")), SumOver("l", FinOf(X("d₂")), entry))));
        return Dimensions(All("e₁", LinearType(X("d₁"), X("n₁")),
            All("e₂", LinearType(X("d₂"), X("n₂")), All("ρ", Bipartite(X("d₁"), X("d₂")),
                Equal(LocalCall("testerImage", X("e₁"), X("e₂"), X("ρ")), sum)))));
    }

    private static Formula SeparableFormula()
    {
        Formula products = SetOf("σ", Bipartite(X("d₁"), X("d₂")),
            Some("ρ₁", Square(X("d₁")), Some("ρ₂", Square(X("d₂")),
                And(Positive(X("ρ₁")), And(Equal(Trace(X("ρ₁")), Typed(D(1), Complexes())),
                    And(Positive(X("ρ₂")), And(Equal(Trace(X("ρ₂")), Typed(D(1), Complexes())),
                        Equal(X("σ"), At(Qualified("Matrix", "kroneckerMap"),
                            LambdaOf("x1", Complexes(), LambdaOf("x2", Complexes(), Multiply(X("x1"), X("x2")))),
                            X("ρ₁"), X("ρ₂"))))))))));
        return All("d₁", Naturals(), All("d₂", Naturals(), All("ρ", Bipartite(X("d₁"), X("d₂")),
            Equal(LocalCall("Separable", X("ρ")), Member(X("ρ"), At(Qualified("convexHull"), Reals(), products))))));
    }

    private static Formula WernerFormula()
    {
        Formula d = NatToReal(X("d"));
        Formula one = Typed(D(1), Bipartite(X("d"), X("d")));
        Formula swap = At(Qualified("Equiv", "Perm", "permMatrix"), Complexes(),
            At(Qualified("Equiv", "prodComm"), FinOf(X("d")), FinOf(X("d"))));
        Formula first = Smul(Div(X("μ"), Multiply(d, Add(d, Typed(D(1), Reals())))), Add(one, swap));
        Formula second = Smul(Div(Subtract(Typed(D(1), Reals()), X("μ")),
            Multiply(d, Subtract(d, Typed(D(1), Reals())))), Subtract(one, swap));
        return All("d", Naturals(), All("μ", Reals(), Equal(LocalCall("werner", X("d"), X("μ")), Add(first, second))));
    }

    private static Formula ClaimFormula()
    {
        Formula detection = Some("n₁", Naturals(), Some("n₂", Naturals(),
            Some("e₁", LinearType(X("d₁"), X("n₁")), Some("e₂", LinearType(X("d₂"), X("n₂")),
                And(LocalCall("IsTester", X("e₁")), And(LocalCall("IsTester", X("e₂")),
                    Less(Typed(D(1), Reals()), Norm(LocalCall("testerImage", X("e₁"), X("e₂"), X("ρ"))))))))));
        return Equal(Local("claim"), All("d₁", Naturals(), All("d₂", Naturals(),
            All("ρ", Bipartite(X("d₁"), X("d₂")), Imp(Positive(X("ρ")),
                Imp(Equal(Trace(X("ρ")), Typed(D(1), Complexes())),
                    Imp(new Formula.Not(LocalCall("Separable", X("ρ"))), detection)))))));
    }

    private static Formula FamilyFormula()
    {
        Formula state = LocalCall("werner", X("d"), X("μ"));
        Formula bound = All("n₁", Naturals(), All("n₂", Naturals(),
            All("e₁", LinearType(X("d"), X("n₁")), All("e₂", LinearType(X("d"), X("n₂")),
                Imp(Contraction(X("e₁"), X("d")), Imp(Contraction(X("e₂"), X("d")),
                    LE(Norm(LocalCall("testerImage", X("e₁"), X("e₂"), state)), Typed(D(1), Reals()))))))));
        return All("d", Naturals(), All("μ", Reals(), Imp(LE(Typed(D(3), Naturals()), X("d")),
            Imp(LE(Div(Typed(D(1), Reals()), NatToReal(X("d"))), X("μ")),
                Imp(Less(X("μ"), Div(Typed(D(1), Reals()), Typed(D(2), Reals()))),
                    And(Positive(state), And(Equal(Trace(state), Typed(D(1), Complexes())),
                        And(new Formula.Not(LocalCall("Separable", state)), bound))))))));
    }

    private static Formula Contraction(Formula e, Formula d) => All("x", Square(d),
        LE(Norm(Evaluate(e, X("x"))), TraceNorm(X("x"))));
    private static Formula Dimensions(Formula body) => All("d₁", Naturals(), All("d₂", Naturals(),
        All("n₁", Naturals(), All("n₂", Naturals(), body))));
    private static Formula LinearType(Formula d, Formula n) => Seq(Parenthesized(Square(d)), Sp,
        new Formula.Subscript(To, F.Id("l")), OpenBracket, Complexes(), CloseBracket, Sp, Parenthesized(Euclidean(n)));
    private static Formula MatrixOf(Formula rows, Formula columns) => At(Qualified("Matrix"), rows, columns, Complexes());
    private static Formula Square(Formula d) => MatrixOf(FinOf(d), FinOf(d));
    private static Formula Bipartite(Formula d1, Formula d2) => MatrixOf(
        Product(FinOf(d1), FinOf(d2)), Product(FinOf(d1), FinOf(d2)));
    private static Formula Euclidean(Formula n) => At(Qualified("EuclideanSpace"), Complexes(), FinOf(n));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Trace(Formula value) => At(Qualified("Matrix", "trace"), value);
    private static Formula TraceNorm(Formula value) => At(
        Qualified("D5", "S3", "Quantum", "Foundation", "FiniteTraceDistance", "traceNorm"), value);
    private static Formula Positive(Formula value) => At(Qualified("Matrix", "PosSemidef"), value);
    private static Formula Evaluate(Formula e, Formula x) => At(At(Qualified("DFunLike", "coe"), e), x);
    private static Formula Norm(Formula value) => new Formula.Norm(value);
    private static Formula NatToReal(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Entanglement", "Witness", "WernerTesterIncompleteness", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => name switch
    {
        "μ" => Mu,
        "ρ" => Rho,
        "σ" => SigmaLower,
        "d₁" => new Formula.Subscript(F.Id("d"), D(1)),
        "d₂" => new Formula.Subscript(F.Id("d"), D(2)),
        "n₁" => new Formula.Subscript(F.Id("n"), D(1)),
        "n₂" => new Formula.Subscript(F.Id("n"), D(2)),
        "e₁" => new Formula.Subscript(F.Id("e"), D(1)),
        "e₂" => new Formula.Subscript(F.Id("e"), D(2)),
        "ρ₁" => new Formula.Subscript(Rho, D(1)),
        "ρ₂" => new Formula.Subscript(Rho, D(2)),
        _ => F.Id(name),
    };
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
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula body) => Seq(OpenBrace, Typed(X(name), type), Sp, Mid, Sp, Parenthesized(body), CloseBrace);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
}
