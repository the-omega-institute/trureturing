using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class ComplexLocalTomographyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Foundation/ComplexLocalTomography";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bipartite dimension counts and separation by local product observables.",
        H("Complex local tomography and two-particle exchange"),
        Blocks(
            DescribeStatement("dyson-dimension", "dysonDim", "Dyson dimension", DysonDefinition(),
                "The parameter d counts diagonal entries. The index b counts real coordinates per unordered off-diagonal pair.",
                DescribeRole.Definition),
            DescribeStatement("dyson-dimension-gap", "dyson_bipartite_dimension_gap",
                "Factored bipartite dimension gap", GapIdentity(),
                "Subtract the product of the local counts from the count at the composite size and factor the difference over a field of characteristic zero."),
            DescribeStatement("dyson-multiplicativity", "dyson_local_tomography_iff",
                "Multiplicativity at the classical and complex indices", Multiplicativity(),
                "For integer sizes at least two, each size factor in the gap is nonzero. The classical index zero and the complex index two exhaust the vanishing cases."),
            DescribeStatement("dyson-gap-sign", "dyson_sign_trichotomy", "Sign and size of the gap", GapSigns(),
                "The size factors are positive. At index one the real count exceeds the product by the product of the skew dimensions. At index four the quaternionic count falls below the product by twice the product of the four size factors."),
            DescribeStatement("real-skew-tensor", "real_skew_kron_orthogonal_to_symmetric_products",
                "A symmetric tensor orthogonal to real product tests", RealSkew(),
                "Transposition negates each skew factor and thereby fixes their Kronecker product. Each local trace of a skew factor times a symmetric test is its own negative. The Kronecker trace factors into those local traces."),
            DescribeStatement("two-rebit-states", "two_rebit_hidden_orthogonal_states",
                "Orthogonal two-rebit states with equal local statistics", Rebit(),
                "Write J for the real two-by-two matrix with rows (0, -1) and (1, 0). Write W for its Kronecker square and U and V for one fourth of I + W and I - W. These are real four-by-four matrices indexed by pairs of two coordinates. The half-scaled square identities and symmetry give positive semidefiniteness. The product traces agree for every pair of symmetric local tests."),
            DescribeStatement("complex-completeness", "complex_local_tomography_iff",
                "Complex product tests separate matrices", ComplexCompleteness(),
                "The coordinate index types X and Y may be empty. Each complex local matrix is its Hermitian real part plus the imaginary unit times its Hermitian imaginary part. Bilinearity extends equality of traces to arbitrary product factors. Tensor products of transposed local matrix units then probe each individual matrix entry."),
            DescribeStatement("dark-product-extension", "darkProductExt",
                "Normalized trace extension on the extra summand", DarkDefinition(),
                "Here T denotes darkProductExt and card denotes the finite cardinality. The visible block is the product test. The dark block is the identity on Z scaled by the product of the two normalized traces. Division by zero is zero here, as in the complex field operations in Lean. If either local carrier is empty, the extension is the zero matrix.",
                DescribeRole.Definition),
            DescribeStatement("dark-indistinguishability", "dark_sector_product_indistinguishable",
                "Orthogonal states with the same normalized trace readout", DarkSector(),
                "Take finite X, Y and Z with X and Y nonempty. For a dark index z, E(z) is the diagonal matrix unit at z on the direct sum. The extension T preserves the unit, adjoints and all visible pairings. Two distinct dark coordinate states both yield the statistics of the maximally mixed visible state for every product test."),
            DescribeStatement("two-particle-exchange", "two_particle_exchange_decomposition",
                "Symmetric and alternating exchange projections", Exchange(),
                "On V = X × X → C, let S interchange the two coordinates and P and Q be one half of id + S and id - S. The images have exchange eigenvalues +1 and -1. For w(i,j) = v(i)v(j), commutativity fixes w under S, and a nonzero coordinate v(i) gives a nonzero diagonal coordinate w(i,i)."))));

    private static DocumentBlock.Describe DescribeStatement(string id, string declaration, string title, Formula statement,
        string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{declaration}"),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fraction(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Negative(Formula a) => Seq(Minus, a);
    private static Formula Conj(params Formula[] terms) => terms.Aggregate((a, b) => And(a, b));
    private static Formula Matrix(Formula idx, Formula scalar) => Call("Matrix", idx, idx, scalar);
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Tensor(Formula a, Formula b) => Call("kron", a, b);
    private static Formula Trace(Formula a) => Call("tr", a);
    private static Formula Adjoint(Formula a) => Call("adj", a);
    private static Formula Transpose(Formula a) => Call("transpose", a);
    private static Formula Psd(Formula a) => Call("PSD", a);
    private static Formula Scalar(string s) => Seq(Mathbb, Grp(F.Id(s)));
    private static Formula Instance(string name, Formula type) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula Finite(string name, Formula body) =>
        All(name, F.Id("Type"), Seq(Instance("Fintype", F.Id(name)), body));
    private static Formula Dim(Formula b, Formula d) => Call("dysonDim", b, d);
    private static Formula Gap(Formula b, Formula x, Formula y) => Sub(Dim(b, Mul(x, y)), Mul(Dim(b, x), Dim(b, y)));
    private static Formula Endpoints(Formula b) => Or(Equal(b, D(0)), Equal(b, D(2)));

    private static Formula DysonDefinition()
    {
        var k = F.Id("K");
        var b = F.Id("b");
        var d = F.Id("d");
        return All("K", F.Id("Type"), Seq(Instance("Field", k),
            All("b", k, All("d", k, Equal(Dim(b, d),
                Add(d, Mul(Mul(Fraction(b, D(2)), d), Sub(d, D(1)))))))));
    }

    private static Formula GapIdentity()
    {
        var k = F.Id("K");
        var b = F.Id("b");
        var x = F.Id("x");
        var y = F.Id("y");
        var factored = Mul(Mul(Mul(Mul(Fraction(Mul(b, Sub(D(2), b)), D(4)), x), y),
            Sub(x, D(1))), Sub(y, D(1)));
        return All("K", F.Id("Type"), Seq(Instance("Field", k), Instance("CharZero", k),
            All("b", k, All("x", k, All("y", k, Equal(Gap(b, x, y), factored))))));
    }

    private static Formula Multiplicativity()
    {
        var k = F.Id("K");
        var b = F.Id("b");
        var x = F.Id("x");
        var y = F.Id("y");
        var result = Equivalent(Equal(Dim(b, Mul(x, y)), Mul(Dim(b, x), Dim(b, y))), Endpoints(b));
        return All("K", F.Id("Type"), Seq(Instance("Field", k), Instance("CharZero", k),
            All("b", k, Sizes(result))));
    }

    private static Formula Sizes(Formula body) =>
        All("x", Scalar("N"), All("y", Scalar("N"),
            Imp(And(AtMost(D(2), F.Id("x")), AtMost(D(2), F.Id("y"))), body)));

    private static Formula GapSigns()
    {
        var b = F.Id("b");
        var x = F.Id("x");
        var y = F.Id("y");
        Formula Skew(Formula d) => Fraction(Mul(d, Sub(d, D(1))), D(2));
        var gap = Gap(b, x, y);
        var quaternionic = Mul(Mul(Mul(Mul(Negative(D(2)), x), y), Sub(x, D(1))), Sub(y, D(1)));
        return All("b", Scalar("R"), Sizes(Conj(
            Equivalent(Less(D(0), gap), And(Less(D(0), b), Less(b, D(2)))),
            Equivalent(Equal(gap, D(0)), Endpoints(b)),
            Equivalent(Less(gap, D(0)), Or(Less(b, D(0)), Less(D(2), b))),
            Equal(Gap(D(1), x, y), Mul(Skew(x), Skew(y))),
            Equal(Gap(D(4), x, y), quaternionic))));
    }

    private static Formula RealSkew()
    {
        var s = F.Id("S");
        var t = F.Id("T");
        var a = F.Id("A");
        var b = F.Id("B");
        var xMat = Matrix(F.Id("X"), Scalar("R"));
        var yMat = Matrix(F.Id("Y"), Scalar("R"));
        var w = Tensor(s, t);
        var result = Imp(Conj(Equal(Transpose(s), Negative(s)), Equal(Transpose(t), Negative(t)),
            Equal(Transpose(a), a), Equal(Transpose(b), b)),
            And(Equal(Transpose(w), w), Equal(Trace(Mul(w, Tensor(a, b))), D(0))));
        return Finite("X", Finite("Y", All("S", xMat, All("A", xMat, All("T", yMat, All("B", yMat, result))))));
    }

    private static Formula Rebit()
    {
        var w = F.Id("W");
        var u = F.Id("U");
        var v = F.Id("V");
        var a = F.Id("A");
        var b = F.Id("B");
        var j = F.Id("J");
        var local = Matrix(Call("Fin", D(2)), Scalar("R"));
        var joint = Matrix(Product(Call("Fin", D(2)), Call("Fin", D(2))), Scalar("R"));
        var tests = All("A", local, All("B", local,
            Imp(And(Equal(Transpose(a), a), Equal(Transpose(b), b)),
                Equal(Trace(Mul(u, Tensor(a, b))), Trace(Mul(v, Tensor(a, b)))))));
        var result = Conj(Equal(Transpose(w), w), Equal(Mul(w, w), D(1)), Equal(Trace(w), D(0)),
            NotEqual(w, D(0)), NotEqual(u, v), Equal(Transpose(u), u), Equal(Transpose(v), v),
            Equal(Trace(u), D(1)), Equal(Trace(v), D(1)), Equal(Mul(u, v), D(0)),
            Equal(Mul(u, u), Mul(Fraction(D(1), D(2)), u)), Equal(Mul(v, v), Mul(Fraction(D(1), D(2)), v)),
            Psd(u), Psd(v), tests);
        var definitions = Conj(Equal(j, Call("matrixTwo", D(0), Negative(D(1)), D(1), D(0))),
            Equal(w, Tensor(j, j)), Equal(u, Mul(Fraction(D(1), D(4)), Add(D(1), w))),
            Equal(v, Mul(Fraction(D(1), D(4)), Sub(D(1), w))));
        return All("J", local, All("W", joint, All("U", joint, All("V", joint, Imp(definitions, result)))));
    }

    private static Formula ComplexCompleteness()
    {
        var m = F.Id("M");
        var n = F.Id("N");
        var a = F.Id("A");
        var b = F.Id("B");
        var joint = Matrix(Product(F.Id("X"), F.Id("Y")), Scalar("C"));
        var condition = All("A", Matrix(F.Id("X"), Scalar("C")), All("B", Matrix(F.Id("Y"), Scalar("C")),
            Imp(And(Equal(Adjoint(a), a), Equal(Adjoint(b), b)),
                Equal(Trace(Mul(m, Tensor(a, b))), Trace(Mul(n, Tensor(a, b)))))));
        return Finite("X", Finite("Y", All("M", joint, All("N", joint, Equivalent(condition, Equal(m, n))))));
    }

    private static Formula DarkDefinition()
    {
        var x = F.Id("X");
        var y = F.Id("Y");
        var z = F.Id("Z");
        var a = F.Id("A");
        var b = F.Id("B");
        var weight = Mul(Fraction(Trace(a), Call("card", x)), Fraction(Trace(b), Call("card", y)));
        return Finite("X", Finite("Y", All("Z", F.Id("Type"), Seq(Instance("DecidableEq", z),
            All("A", Matrix(x, Scalar("C")), All("B", Matrix(y, Scalar("C")),
                Equal(Call("T", z, a, b), Call("block", Tensor(a, b), D(0), D(0), Mul(weight, Call("identity", z))))))))));
    }

    private static Formula DarkSector()
    {
        var x = F.Id("X");
        var y = F.Id("Y");
        var z = F.Id("Z");
        var a = F.Id("A");
        var b = F.Id("B");
        var m = F.Id("M");
        var r = F.Id("r");
        var s = F.Id("s");
        var er = Call("E", r);
        var es = Call("E", s);
        Formula T(Formula l, Formula h) => Call("T", z, l, h);
        Formula Tests(Formula proposition) =>
            All("A", Matrix(x, Scalar("C")), All("B", Matrix(y, Scalar("C")), proposition));
        var mixed = Mul(Fraction(D(1), Mul(Call("card", x), Call("card", y))), D(1));
        var result = Conj(Equal(T(D(1), D(1)), D(1)), Tests(Equal(Adjoint(T(a, b)), T(Adjoint(a), Adjoint(b)))),
            All("M", Matrix(Product(x, y), Scalar("C")), Tests(
                Equal(Trace(Mul(Call("block", m, D(0), D(0), D(0)), T(a, b))), Trace(Mul(m, Tensor(a, b)))))),
            NotEqual(er, es), Equal(Adjoint(er), er), Equal(Adjoint(es), es),
            Equal(Trace(er), D(1)), Equal(Trace(es), D(1)), Psd(er), Psd(es), Equal(Mul(er, es), D(0)),
            Tests(And(Equal(Trace(Mul(er, T(a, b))), Trace(Mul(es, T(a, b)))),
                Equal(Trace(Mul(er, T(a, b))), Trace(Mul(mixed, Tensor(a, b)))))));
        return Finite("X", Seq(Instance("DecidableEq", x), Instance("Nonempty", x),
            Finite("Y", Seq(Instance("DecidableEq", y), Instance("Nonempty", y),
                Finite("Z", Seq(Instance("DecidableEq", z),
                    All("r", z, All("s", z, Imp(NotEqual(r, s), result)))))))));
    }

    private static Formula Exchange()
    {
        var x = F.Id("X");
        var v = F.Id("v");
        var p = F.Id("P");
        var q = F.Id("Q");
        var s = F.Id("S");
        var endomorphism = Call("End", Product(x, x), Scalar("C"));
        var w = Call("squareTensor", v);
        Formula Comp(Formula a, Formula b) => Seq(a, Sp, Circ, Sp, b);
        var result = Conj(Equal(Add(p, q), F.Id("id")), Equal(Comp(p, q), D(0)), Equal(Comp(q, p), D(0)),
            Equal(Comp(p, p), p), Equal(Comp(q, q), q), Equal(Comp(s, p), p), Equal(Comp(s, q), Negative(q)),
            All("v", Seq(x, Sp, To, Sp, Scalar("C")), Imp(NotEqual(v, D(0)),
                Conj(Equal(Call("Q", w), D(0)), Equal(Call("P", w), w), NotEqual(w, D(0))))));
        var definitions = Conj(Equal(s, Call("swap", x)),
            Equal(p, Mul(Fraction(D(1), D(2)), Add(F.Id("id"), s))),
            Equal(q, Mul(Fraction(D(1), D(2)), Sub(F.Id("id"), s))));
        return All("X", F.Id("Type"), All("S", endomorphism, All("P", endomorphism,
            All("Q", endomorphism, Imp(definitions, result)))));
    }
}
