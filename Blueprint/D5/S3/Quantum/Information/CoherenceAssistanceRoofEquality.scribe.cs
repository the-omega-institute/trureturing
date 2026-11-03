using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class CoherenceAssistanceRoofEqualityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/zhaopereiramafei2021coherenceassistance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-two state in four dimensions has equal coherence roofs, refuting the universal strict-gap claim.",
        H("Equal coherence roofs on a mixed rank-two state"),
        Blocks(
            Node("is-coherence-function", "Symmetric concave coherence functions", IsCoherenceFunctionFormula(),
                "A coherence function is real-valued on the finite probability simplex, concave there, invariant under every coordinate permutation, and zero on every simplex vertex.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coherence-vector", "The coherence vector", CoherenceVectorFormula(),
                "The coherence vector records the squared complex amplitudes in the fixed reference basis by applying Complex.normSq coordinatewise.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("is-decomposition", "Finite pure-state decompositions", IsDecompositionFormula(),
                "A decomposition consists of nonnegative real weights summing to one, unit-norm complex vectors, and the exact density-matrix sum of their rank-one projectors. Each real weight is embedded into the complex matrix space before scalar multiplication.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("decomposition-values", "Values of decomposition averages", DecompositionValuesFormula(),
                "The value set contains each real average obtained from a finite pure-state decomposition, evaluating the coherence function on every coherence vector.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("convex-roof", "The convex roof", ConvexRoofFormula(),
                "The convex roof is the real infimum of the decomposition-average value set.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("assistance", "The coherence of assistance", AssistanceFormula(),
                "The coherence of assistance is the real supremum of the same decomposition-average value set.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("is-mixed", "Mixed density matrices", IsMixedFormula(),
                "A matrix is mixed when it is positive semidefinite, has complex trace one, and its squared matrix has trace different from one.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The universal strict roof gap", ClaimFormula(),
                "The claim asks whether every natural dimension, every symmetric concave coherence function with a nonzero simplex value, and every mixed density matrix have strictly separated convex and assisted roofs.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "A rank-two counterexample", new Formula.Not(Parenthesized(Local("claim"))),
                "Choose the quadratic function q(p) = 1 − Σᵢ pᵢ² in dimension four. It is concave on the simplex, permutation invariant, zero at every vertex, and nonzero at the barycenter. Let v = (1/√2, 1/√6, 1/√6, 1/√6) and w = (0, 1/√3, ω/√3, ω²/√3), where ω = (−1 + i√3)/2. Direct calculation gives unit norms and zero mutual inner products. Let P be the sum of their rank-one density matrices and let ρ = (1/2)P. The two vectors make P a self-adjoint idempotent, and the complementary projection has zero trace against ρ. For every complex a and b, the fourth-moment identity Σᵢ |a vᵢ + b wᵢ|⁴ = (|a|² + |b|²)²/3 holds. Therefore every unit vector in the range of P has q equal to 2/3. Positivity of the complementary projection and the zero trace force every positive-weight vector in any decomposition of ρ into the range of P. Hence every decomposition average is 2/3. The displayed two-vector decomposition shows that this value is attained, so the decomposition-value set is exactly {2/3}. Finally ρ is positive semidefinite, has trace one, and has trace(ρ²) = 1/2, so it is mixed. The convex roof and the coherence of assistance are both 2/3, contradicting the strict inequality asserted by the claim.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhao-pereira-ma-fei-2021-coherence-assistance-roof-equality"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("coherence-assistance-" + id), DeclarationHandle.Create(Prefix + Declaration(id)),
        H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static string Declaration(string id) => id switch
    {
        "is-coherence-function" => "IsCoherenceFunction",
        "coherence-vector" => "coherenceVector",
        "is-decomposition" => "IsDecomposition",
        "decomposition-values" => "decompositionValues",
        "convex-roof" => "convexRoof",
        "assistance" => "assistance",
        "is-mixed" => "IsMixed",
        "claim" => "claim",
        "result" => "result",
        _ => throw new ArgumentOutOfRangeException(nameof(id)),
    };

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified(
        "D5", "S3", "Quantum", "Information", "CoherenceAssistanceRoofEquality", name);
    private static Formula LocalCall(string name, params Formula[] args) =>
        new Formula.Apply(Local(name), [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Qualified(name.Split('.')), [.. args]);
    private static Formula At(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(variable, type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula value) =>
        Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula SumOver(Formula variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Colon, Sp, domain)), Sp, Parenthesized(body));
    private static Formula SetOf(Formula variable, Formula type, Formula body) =>
        Seq(OpenBrace, variable, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Function(Formula domain, Formula codomain) => Arrow(domain, codomain);
    private static Formula Matrix(Formula n) => Call("Matrix", Fin(n), Fin(n), Complex());
    private static Formula Simplex(Formula n) => Call("stdSimplex", Real(), Fin(n));
    private static Formula One(Formula type) => Typed(D(1), type);
    private static Formula RankOneDensity(Formula psi) =>
        Call("D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity", psi);
    private static Formula NormSq(Formula value) => Call("Complex.normSq", value);
    private static Formula Trace(Formula value) => Call("Matrix.trace", value);
    private static Formula MatrixMul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));

    private static Formula IsCoherenceFunctionFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), sigma = SigmaLower, p = F.Id("p"), i = F.Id("i");
        Formula function = Function(Fin(n), Real());
        Formula simplex = Simplex(n);
        Formula permutation = Call("Equiv.Perm", Fin(n));
        Formula composition = Seq(p, Sp, Circ, Sp, Typed(sigma, Function(Fin(n), Fin(n))));
        Formula symmetry = All(sigma, permutation,
            All(p, function, Imp(Mem(p, simplex), Eq(At(f, composition), At(f, p)))));
        Formula vertices = All(i, Fin(n), Eq(At(f, Call("Pi.single", i, One(Real()))), Typed(D(0), Real())));
        Formula body = And(Call("ConcaveOn", Real(), simplex, f), And(symmetry, vertices));
        return All(n, Nat(), All(f, Function(function, Real()), Iff(LocalCall("IsCoherenceFunction", f), body)));
    }

    private static Formula CoherenceVectorFormula()
    {
        Formula n = F.Id("n"), psi = Psi, i = F.Id("i");
        Formula state = Function(Fin(n), Complex());
        Formula body = LambdaOf(i, Fin(n), NormSq(At(psi, i)));
        return All(n, Nat(), All(psi, state, Eq(LocalCall("coherenceVector", psi), body)));
    }

    private static Formula IsDecompositionFormula()
    {
        Formula n = F.Id("n"), rho = Rho, k = F.Id("k"), p = F.Id("p"), psi = Psi;
        Formula j = F.Id("j"), i = F.Id("i");
        Formula weight = Function(Fin(k), Real());
        Formula state = Function(Fin(k), Function(Fin(n), Complex()));
        Formula nonnegative = All(j, Fin(k), Le(D(0), At(p, j)));
        Formula total = Eq(SumOver(j, Fin(k), At(p, j)), One(Real()));
        Formula unit = All(j, Fin(k), Eq(SumOver(i, Fin(n), NormSq(At(At(psi, j), i))), One(Real())));
        Formula sum = SumOver(j, Fin(k), Smul(Typed(At(p, j), Complex()), RankOneDensity(At(psi, j))));
        Formula body = And(nonnegative, And(total, And(unit, Eq(rho, sum))));
        return All(n, Nat(), All(rho, Matrix(n), All(k, Nat(), All(p, weight,
            All(psi, state, Iff(LocalCall("IsDecomposition", rho, k, p, psi), body))))));
    }

    private static Formula DecompositionValuesFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), rho = Rho, x = F.Id("x");
        Formula k = F.Id("k"), p = F.Id("p"), psi = Psi, j = F.Id("j");
        Formula function = Function(Fin(n), Real());
        Formula weight = Function(Fin(k), Real());
        Formula state = Function(Fin(k), Function(Fin(n), Complex()));
        Formula average = Eq(x, SumOver(j, Fin(k), Mul(At(p, j), At(f,
            LocalCall("coherenceVector", At(psi, j))))));
        Formula members = Some(k, Nat(), Some(p, weight, Some(psi, state,
            And(LocalCall("IsDecomposition", rho, k, p, psi), average))));
        Formula set = SetOf(x, Real(), members);
        return All(n, Nat(), All(f, Function(function, Real()), All(rho, Matrix(n),
            Eq(LocalCall("decompositionValues", f, rho), set))));
    }

    private static Formula ConvexRoofFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), rho = Rho;
        Formula function = Function(Fin(n), Real());
        return All(n, Nat(), All(f, Function(function, Real()), All(rho, Matrix(n),
            Eq(LocalCall("convexRoof", f, rho), Call("sInf", LocalCall("decompositionValues", f, rho))))));
    }

    private static Formula AssistanceFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), rho = Rho;
        Formula function = Function(Fin(n), Real());
        return All(n, Nat(), All(f, Function(function, Real()), All(rho, Matrix(n),
            Eq(LocalCall("assistance", f, rho), Call("sSup", LocalCall("decompositionValues", f, rho))))));
    }

    private static Formula IsMixedFormula()
    {
        Formula n = F.Id("n"), rho = Rho;
        Formula trace = Trace(rho);
        Formula squareTrace = Trace(MatrixMul(rho, rho));
        Formula body = And(Call("Matrix.PosSemidef", rho),
            And(Eq(trace, One(Complex())), Ne(squareTrace, One(Complex()))));
        return All(n, Nat(), All(rho, Matrix(n), Iff(LocalCall("IsMixed", rho), body)));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), f = F.Id("f"), p = F.Id("p"), rho = Rho;
        Formula function = Function(Fin(n), Real());
        Formula witness = Some(p, Function(Fin(n), Real()),
            And(Mem(p, Simplex(n)), Ne(At(f, p), D(0))));
        Formula conclusion = All(rho, Matrix(n), Imp(LocalCall("IsMixed", rho),
            Lt(LocalCall("convexRoof", f, rho), LocalCall("assistance", f, rho))));
        return All(n, Nat(), All(f, Function(function, Real()), Imp(LocalCall("IsCoherenceFunction", f),
            Imp(witness, conclusion))));
    }

    private static Formula ClaimFormula() => Iff(Local("claim"), ClaimBody());
}
