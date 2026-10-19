using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PathCHS;

internal sealed class PathCHSNormClosedFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/chavez2023extremalpolynomialnorms");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete homogeneous symmetric functions of finite path spectra.",
        H("PathCHSNormClosedForm"),
        Blocks(
            Node("hermitian", "The path matrix is Hermitian", HermitianFormula(), "pathAdjHermitian", "The entry with indices i and j equals the entry with indices j and i. The matrix is the adjacency matrix of the path with vertices Fin n.", DescribeRole.Theorem, false),
            Node("chs", "Complete homogeneous symmetric value", ChsFormula(), "chs", "Page 2, Equation (1.1): “∑_{d=0}^{∞} h_d(x₁, x₂, …, x_n) t^d = ∏_{i=1}^{n} 1/(1 − x_i t).” The polynomial hsymm is evaluated at the real eigenvalues of the path adjacency matrix.", DescribeRole.Definition, true),
            Node("norm", "The complete homogeneous symmetric norm", NormFormula(), "chsNorm", "Page 2, Theorem 1.4: “Suppose d ≥ 2 is even. The following function defines a norm on H_n: ‖A‖_d = h_d(λ₁, λ₂, …, λ_n)^{1/d}.” Natural d is cast to ℝ in the reciprocal exponent.", DescribeRole.Definition, true),
            Node("formula", "Finite second-difference expression", PathFormula(), "pathFormula", "The upper index is 2m+n−1. Nat.div is natural-number quotient. Each binomial value is cast to ℤ before subtraction.", DescribeRole.Definition, false),
            Node("claim", "Problem 1 for path norms", ClaimFormula(), "claim", "Page 14, Section 5, Problem 1: “The path of order n has m = n − 1 edges. Proposition 5.14 (a) therefore implies that ‖P_n‖₂ = √(n − 1). However, computing ‖P_n‖_d for d ≥ 4 seems unattainable at the moment. We leave this is an interesting open problem. Problem 1. Compute ‖P_n‖_d for d ≥ 4.” Here n ≥ 1 and d=2m with m ≥ 2; both the symmetric polynomial and its real root are specified.", DescribeRole.Definition, false),
            Node("geometric", "A geometric series times its denominator", GeometricFormula(), "geometric_mul_linear", "Rescaling the geometric series gives the inverse of 1−aX over any commutative ring.", DescribeRole.Theorem, false),
            Node("symmetricseries", "The symmetric-polynomial generating function", HsymmFormula(), "hsymm_series_product", "Equation (1.1), page 2, gives the generating function. Grouping monomials by total degree gives the reciprocal product of the linear factors over a commutative ring.", DescribeRole.Theorem, true),
            Node("map", "Ring homomorphisms and constant-weight continuants", ContinuantMapFormula(), "continuant_map", "A ring homomorphism preserves the initial values and the second-order recurrence.", DescribeRole.Theorem, false),
            Node("zero", "The zero-weight continuant", ContinuantZeroFormula(), "continuant_zero", "At zero weight every term of the continuant is one.", DescribeRole.Theorem, false),
            Node("pathseries", "The reciprocal path continuant", PathSeriesFormula(), "path_hsymm_series", "The product over adjacency eigenvalues is the path determinant. Its reciprocal generates the symmetric polynomials.", DescribeRole.Theorem, false),
            Node("coefficients", "Even-degree values", ChsIdentityFormula(), "chs_formula", "Catalan substitution transforms the reciprocal continuant into a binomial second difference and a geometric series of reflections.", DescribeRole.Theorem, false),
            Node("result", "Closed form for every even path norm", Disp(ClaimBody()), "result", "The second-difference expression gives the complete homogeneous symmetric value and hence its real root.", DescribeRole.Theorem, false, new OpenProblemResolutionClaim(ProblemSlugRef.Create("chavez-2023-path-chs-norm-closed-form"), ResolutionKind.Proved)),
            Node("degree", "Degree of the monic Chebyshev polynomial", DegreeFormula(), "chebS_degree", "The identity with the second-kind Chebyshev polynomial after scaling the variable gives degree n.", DescribeRole.Theorem, false)),
        []));
    private static DocumentBlock Node(string id, string title, Formula formula, string name, string prose, DescribeRole role, bool literature, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("pathchsnormclosedform-" + id), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula N(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string name)
    {
        var parts = name.Split('.');
        Formula value = N(parts[0]);
        for (var i = 1; i < parts.Length; i++) value = Seq(value, Dot, N(parts[i]));
        return value;
    }
    private static Formula C(string name, params Formula[] args) => new Formula.Apply(Q(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula A(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula S(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula M(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Rat(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals(string[] names, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; i--) body = All(names[i], Nat(), body);
        return body;
    }
    private static Formula SumOver(string name, Formula set, Formula body) => Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Lambda(string name, Formula type, Formula body) => Seq(N("fun"), Sp, Parenthesized(Seq(V(name), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula If(Formula condition, Formula yes, Formula no) => Seq(N("if"), Sp, Parenthesized(condition), Sp, N("then"), Sp, yes, Sp, N("else"), Sp, no);

    private static Formula MatrixBody()
    {
        Formula n = V("n"), i = V("i"), j = V("j");
        var condition = Seq(Parenthesized(Eq(A(Cast(i, Nat()), D(1)), Cast(j, Nat()))), Sp, Lor, Sp, Parenthesized(Eq(A(Cast(j, Nat()), D(1)), Cast(i, Nat()))));
        return C("Matrix.of", Lambda("i", C("Fin", n), Lambda("j", C("Fin", n), If(condition, Cast(D(1), Real()), D(0)))));
    }
    private static Formula HermitianFormula() => Disp(All("n", Nat(), C("Matrix.IsHermitian", MatrixBody())));
    private static Formula ChsFormula() => Disp(Naturals(["n", "d"], Eq(C("chs", V("n"), V("d")),
        C("MvPolynomial.eval", C("Matrix.IsHermitian.eigenvalues", C("pathAdjHermitian", V("n"))), C("MvPolynomial.hsymm", C("Fin", V("n")), Real(), V("d"))))));
    private static Formula NormFormula() => Disp(Naturals(["n", "d"], Eq(C("chsNorm", V("n"), V("d")),
        Pow(C("chs", V("n"), V("d")), Rat(Cast(D(1), Real()), Cast(V("d"), Real()))))));
    private static Formula PathFormula()
    {
        Formula n = V("n"), m = V("m"), k = V("k");
        var l = S(A(M(D(2), m), n), D(1));
        var r = S(Cast(m, Int()), M(Cast(k, Int()), A(Cast(n, Int()), D(1))));
        var value = A(S(Cast(C("D5.S0.Conventions.IntegerIndexBinomial.binom", l, r), Int()), M(D(2), Cast(C("D5.S0.Conventions.IntegerIndexBinomial.binom", l, S(r, D(1))), Int()))), Cast(C("D5.S0.Conventions.IntegerIndexBinomial.binom", l, S(r, D(2))), Int()));
        var sum = SumOver("k", C("Finset.range", A(C("Nat.div", m, A(n, D(1))), D(1))), value);
        return Disp(Naturals(["n", "m"], Eq(C("pathFormula", n, m), sum)));
    }
    private static Formula ClaimBody()
    {
        Formula n = V("n"), m = V("m"), d = M(D(2), m);
        var value = Cast(C("pathFormula", n, m), Real());
        return Naturals(["n", "m"], Imp(Le(D(1), n), Imp(Le(D(2), m),
            And(Eq(C("chs", n, d), value), Eq(C("chsNorm", n, d), Pow(value, Rat(Cast(D(1), Real()), Cast(d, Real()))))))));
    }
    private static Formula ClaimFormula() => Disp(Eq(N("claim"), ClaimBody()));
    private static Formula Generic(string[] types, string[] instances, Formula body)
    {
        Formula suffix = body;
        for (var i = instances.Length - 1; i >= 0; i--)
        {
            var parts = instances[i].Split(' ');
            var arguments = parts.Skip(1).Select(V).ToArray();
            suffix = Seq(OpenBracket, C(parts[0], arguments), CloseBracket, Sp, suffix);
        }
        for (var i = types.Length - 1; i >= 0; i--) suffix = All(types[i], N("Type"), suffix);
        return suffix;
    }
    private static Formula SeriesProduct(Formula a, Formula r, Formula index)
    {
        var coefficient = C("MvPolynomial.eval", a, C("MvPolynomial.hsymm", index, r, V("d")));
        var series = C("PowerSeries.mk", Lambda("d", Nat(), coefficient));
        var factor = S(D(1), M(C("PowerSeries.C", C("a", V("i"))), Q("PowerSeries.X")));
        var product = Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, index)), Sp, Parenthesized(factor));
        return Eq(M(series, product), D(1));
    }
    private static Formula GeometricFormula() => Disp(Generic(["R"], ["CommRing R"], All("a", V("R"),
        Eq(M(C("PowerSeries.mk", Lambda("k", Nat(), Pow(V("a"), V("k")))), Parenthesized(S(D(1), M(C("PowerSeries.C", V("a")), Q("PowerSeries.X"))))), D(1)))));
    private static Formula HsymmFormula() => Disp(Generic(["I", "R"], ["Fintype I", "DecidableEq I", "CommRing R"],
        All("a", new Formula.TypeArrow(V("I"), V("R")), SeriesProduct(V("a"), V("R"), V("I")))));
    private static Formula Continuant(Formula x, Formula n) => C("D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductAlgebra.cont", C("Function.const", Nat(), x), D(1), D(1), n);
    private static Formula ContinuantMapFormula() => Disp(Generic(["R", "S"], ["CommRing R", "CommRing S"],
        All("f", Seq(V("R"), Sp, To, Sp, Plus, Star, Sp, V("S")), All("x", V("R"), All("n", Nat(),
            Eq(C("f", Continuant(V("x"), V("n"))), Continuant(C("f", V("x")), V("n"))))))));
    private static Formula ContinuantZeroFormula() => Disp(Generic(["R"], ["CommRing R"], All("n", Nat(), Eq(Continuant(Cast(D(0), V("R")), V("n")), D(1)))));
    private static Formula PathSeriesFormula() => Disp(All("n", Nat(), Eq(M(C("PowerSeries.mk", Lambda("d", Nat(), C("chs", V("n"), V("d")))),
        Continuant(Pow(Cast(Q("PowerSeries.X"), C("PowerSeries", Real())), D(2)), V("n"))), D(1))));
    private static Formula ChsIdentityFormula() => Disp(Naturals(["n", "m"], Eq(C("chs", V("n"), M(D(2), V("m"))), Cast(C("pathFormula", V("n"), V("m")), Real()))));
    private static Formula DegreeFormula() => Disp(Generic(["K"], ["Field K", "CharZero K"], All("n", Nat(), Eq(C("Polynomial.natDegree", C("Polynomial.Chebyshev.S", V("K"), Cast(V("n"), Int()))), V("n")))));

}
