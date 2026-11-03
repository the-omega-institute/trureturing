using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class AnticoherenceSpinCovarianceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal Pauli rotations act on collective spins and their quadratic products.",
        H("Spin covariance and Dicke coordinates"),
        Blocks(
            Node("pauli_rotation", "Pauli conjugation gives an orthogonal matrix", PauliRotation(),
                "Conjugation by a special unitary qubit matrix preserves the real space of traceless Hermitian matrices. "
                    + "Expand each conjugated Pauli matrix in the Pauli basis, with coefficient one half of the real part of its trace product with the corresponding Pauli matrix. "
                    + "Preservation of these trace products gives r times its transpose equal to the identity, hence also its transpose times r equal to the identity. "
                    + "The assertion requires orthogonality; it does not assert a determinant condition."),
            Node("orthogonal_sandwich", "An orthogonal change of a sandwich family", OrthogonalSandwich(),
                "For a complex matrix q satisfying q transpose times q equal to the identity, replacing each member of a matrix family s by its q-linear combination leaves the sum of s c times x times s c unchanged. "
                    + "Expand both combinations and contract the two q coefficients by column orthogonality. "
                    + "This is a bilinear identity: the hypothesis uses transpose, and neither occurrence of s c is conjugate-transposed."),
            Node("tensor_unitary", "A tensor power is unitary", TensorUnitary(),
                "The tensor product of n copies of a special unitary qubit matrix is unitary. "
                    + "The constant family has domain Fin n, including the empty tensor product at n equal to zero."),
            Node("local_action", "A local matrix changes one coordinate", LocalAction(),
                "At a computational basis word x, the action of a matrix on site k sums over the replacement bit b. "
                    + "Split a word into its k-th coordinate and the remaining coordinates. The identity factors at the other sites force those coordinates to agree with x."),
            Node("collectiveSpin", "Collective spin operators", CollectiveSpin(),
                "The collective spin in axis a is one half of the sum of the Pauli operator at every site. "
                    + "It acts on computational basis words of length n.", DescribeRole.Definition),
            Node("collective_tensor_rotation", "Collective spins inherit the Pauli rotation", CollectiveTensorRotation(),
                "Assume the same coefficient matrix r expresses each conjugated Pauli matrix in the Pauli basis. "
                    + "Conjugating a local operator by the constant tensor power conjugates its single nonidentity factor. "
                    + "Summing this identity over the sites and interchanging the finite sums gives the collective-spin transformation."),
            Node("quadratic_rotation", "Rotation of quadratic spin products", QuadraticRotation(),
                "Suppose d is unitary, r is real orthogonal, and the family j transforms under conjugation by d with coefficients r. "
                    + "Inserting d adjoint times d between two factors gives the product transformation. "
                    + "Row orthogonality expresses the diagonal correction as the contraction of two r coefficients. "
                    + "Consequently the symmetrized quadratic product, with any complex diagonal correction κ, transforms with two copies of r."),
            Node("dickeIsometry", "Normalized Dicke embedding", DickeIsometry(),
                "The r-th column is supported on bit words with exactly r.val entries equal to one. "
                    + "Each supported entry is the reciprocal of the square root of Nat.choose n r.val. "
                    + "The binomial coefficient is cast from the natural numbers to the reals before taking its square root, and the result is included in the complex numbers before inversion. "
                    + "The spin index therefore counts ones.", DescribeRole.Definition),
            Node("partialTrace_isometries", "Partial trace through a product embedding", PartialTraceIsometries(),
                "Conjugate z by the Kronecker product of v and w, where w adjoint times w is the identity. "
                    + "In the partial trace over the second factor, the sum of a w coefficient times the conjugate of another is a Kronecker delta. "
                    + "Contracting that delta leaves v times the partial trace of z times v adjoint. No isometry hypothesis on v is needed."),
            Node("dickeCoefficient", "Dicke coefficient at a given weight", DickeCoefficient(),
                "For natural numbers n, w and r, this coefficient is zero unless the word weight w equals r. "
                    + "When they agree it is the reciprocal complex inclusion of the square root of the real cast of Nat.choose n r.", DescribeRole.Definition),
            Node("dicke_site_sum", "Summing the single-site Dicke transitions", DickeSiteSum(),
                "The weight of a word is the natural-number sum of its bit values. Updating site k changes that weight by the new bit minus the old bit. "
                    + "Separate the sites at which x k is zero from those at which it is one. There are n minus the weight sites of the first kind and weight sites of the second kind. "
                    + "The two possible replacement bits yield the four displayed matrix entries and Dicke coefficients. "
                    + "Subtraction in the weight-minus-one argument is natural-number subtraction; the multiplicities are cast to complex scalars."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("anticoherence-spin-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula PauliRotation()
    {
        Formula rotation = All("a", FinOf(D(3)), Equal(
            Mul(Mul(Val(V("u")), Pauli(V("a"))), Adj(Val(V("u")))),
            SumOf("c", FinOf(D(3)), Smul(OfReal(At(V("r"), V("a"), V("c"))), Pauli(V("c"))))));
        return All("u", SU2, Some("r", Matrix(FinOf(D(3)), FinOf(D(3)), Real),
            And(Equal(Mul(Transpose(V("r")), V("r")), D(1)), rotation)));
    }

    private static Formula OrthogonalSandwich()
    {
        Formula left = SumOf("a", V("k"), Mul(Mul(
            SumOf("c", V("k"), Smul(At(V("q"), V("a"), V("c")), At(V("s"), V("c")))),
            V("x")), SumOf("e", V("k"), Smul(At(V("q"), V("a"), V("e")), At(V("s"), V("e"))))));
        Formula right = SumOf("c", V("k"), Mul(Mul(At(V("s"), V("c")), V("x")), At(V("s"), V("c"))));
        return All("k", Type, All("n", Type,
            Instances([At(Qualified("Fintype"), V("k")), At(Qualified("Fintype"), V("n")),
                At(Qualified("DecidableEq"), V("k"))],
            All("q", Matrix(V("k"), V("k"), Complex),
            Imp(Equal(Mul(Transpose(V("q")), V("q")), D(1)),
            All("s", Arrow(V("k"), Square(V("n"))), All("x", Square(V("n")), Equal(left, right))))))));
    }

    private static Formula TensorUnitary() => All("n", Nat, All("u", SU2,
        Equal(Mul(Adj(Tensor(V("n"), Val(V("u")))), Tensor(V("n"), Val(V("u")))), D(1))));

    private static Formula LocalAction() => All("n", Nat, All("k", FinOf(V("n")),
        All("a", Square(FinOf(D(2))), All("f", Arrow(Word(V("n")), Complex),
        All("x", Word(V("n")), Equal(
            At(At(Qualified("Matrix", "mulVec"), LocalOp(V("k"), V("a")), V("f")), V("x")),
            SumOf("b", FinOf(D(2)), Mul(At(V("a"), At(V("x"), V("k")), V("b")),
                At(V("f"), At(Qualified("Function", "update"), V("x"), V("k"), V("b")))))))))));

    private static Formula CollectiveSpin() => All("n", Nat, All("a", FinOf(D(3)),
        Equal(Typed(Local("collectiveSpin", V("n"), V("a")), Square(Word(V("n")))),
            Smul(Typed(new Formula.Fraction(D(1), D(2)), Complex),
                SumOf("k", FinOf(V("n")), LocalOp(V("k"), Pauli(V("a"))))))));

    private static Formula CollectiveTensorRotation()
    {
        Formula premise = All("a", FinOf(D(3)), Equal(
            Mul(Mul(Val(V("u")), Pauli(V("a"))), Adj(Val(V("u")))),
            SumOf("c", FinOf(D(3)), Smul(OfReal(At(V("r"), V("a"), V("c"))), Pauli(V("c"))))));
        Formula conclusion = All("a", FinOf(D(3)), Equal(
            Mul(Mul(Tensor(V("n"), Val(V("u"))), Local("collectiveSpin", V("n"), V("a"))),
                Adj(Tensor(V("n"), Val(V("u"))))),
            SumOf("c", FinOf(D(3)), Smul(OfReal(At(V("r"), V("a"), V("c"))),
                Local("collectiveSpin", V("n"), V("c"))))));
        return All("n", Nat, All("u", SU2, All("r", Matrix(FinOf(D(3)), FinOf(D(3)), Real),
            Imp(premise, conclusion))));
    }

    private static Formula QuadraticRotation()
    {
        Formula premise = All("a", FinOf(D(3)), Equal(
            Mul(Mul(V("d"), At(V("j"), V("a"))), Adj(V("d"))),
            SumOf("c", FinOf(D(3)), Smul(OfReal(At(V("r"), V("a"), V("c"))), At(V("j"), V("c"))))));
        Formula conclusion = All("κ", Complex, All("a", FinOf(D(3)), All("b", FinOf(D(3)), Equal(
            Mul(Mul(V("d"), Quadratic(V("a"), V("b"))), Adj(V("d"))),
            SumOf("c", FinOf(D(3)), SumOf("e", FinOf(D(3)), Smul(
                Mul(OfReal(At(V("r"), V("a"), V("c"))), OfReal(At(V("r"), V("b"), V("e")))),
                Quadratic(V("c"), V("e")))))))));
        return All("n", Type, Instances([At(Qualified("Fintype"), V("n")), At(Qualified("DecidableEq"), V("n"))],
            All("d", Square(V("n")), Imp(Equal(Mul(Adj(V("d")), V("d")), D(1)),
            All("r", Matrix(FinOf(D(3)), FinOf(D(3)), Real),
            Imp(Equal(Mul(Transpose(V("r")), V("r")), D(1)),
            All("j", Arrow(FinOf(D(3)), Square(V("n"))), Imp(premise, conclusion))))))));
    }

    private static Formula Quadratic(Formula a, Formula b) => Subtract(
        Smul(Typed(new Formula.Fraction(D(1), D(2)), Complex),
            Add(Mul(At(V("j"), a), At(V("j"), b)), Mul(At(V("j"), b), At(V("j"), a)))),
        Smul(If(Equal(a, b), V("κ"), D(0)), D(1)));

    private static Formula DickeIsometry() => All("n", Nat, Equal(
        Typed(Local("dickeIsometry", V("n")), Matrix(Word(V("n")), FinOf(Add(V("n"), D(1))), Complex)),
        LambdaOf("x", Word(V("n")), LambdaOf("r", FinOf(Add(V("n"), D(1))),
            If(Equal(Weight(V("n"), V("x")), FinVal(V("r"))),
                Inv(OfReal(At(Qualified("Real", "sqrt"), NatReal(At(Qualified("Nat", "choose"), V("n"), FinVal(V("r"))))))), D(0))))));

    private static Formula PartialTraceIsometries()
    {
        Formula product = At(Qualified("Matrix", "kronecker"), V("v"), V("w"));
        Formula conclusion = All("z", Square(Product(V("i"), V("j"))), Equal(
            PartialTrace(Mul(Mul(product, V("z")), Adj(product))),
            Mul(Mul(V("v"), PartialTrace(V("z"))), Adj(V("v")))));
        return All("a", Type, All("b", Type, All("i", Type, All("j", Type,
            Instances([At(Qualified("Fintype"), V("a")), At(Qualified("Fintype"), V("b")),
                At(Qualified("Fintype"), V("i")), At(Qualified("Fintype"), V("j")),
                At(Qualified("DecidableEq"), V("j"))],
            All("v", Matrix(V("a"), V("i"), Complex), All("w", Matrix(V("b"), V("j"), Complex),
            Imp(Equal(Mul(Adj(V("w")), V("w")), D(1)), conclusion))))))));
    }

    private static Formula DickeCoefficient() => All("n", Nat, All("w", Nat, All("r", Nat,
        Equal(Typed(Local("dickeCoefficient", V("n"), V("w"), V("r")), Complex),
            If(Equal(V("w"), V("r")), Inv(OfReal(At(Qualified("Real", "sqrt"),
                NatReal(At(Qualified("Nat", "choose"), V("n"), V("r")))))), D(0))))));

    private static Formula DickeSiteSum()
    {
        Formula weight = Weight(V("n"), V("x"));
        Formula coefficient = Local("dickeCoefficient", V("n"), weight, FinVal(V("r")));
        Formula plus = Local("dickeCoefficient", V("n"), Add(weight, D(1)), FinVal(V("r")));
        Formula minus = Local("dickeCoefficient", V("n"), Typed(Subtract(weight, D(1)), Nat), FinVal(V("r")));
        Formula left = SumOf("k", FinOf(V("n")), SumOf("b", FinOf(D(2)),
            Mul(At(V("a"), At(V("x"), V("k")), V("b")), Local("dickeIsometry", V("n"),
                At(Qualified("Function", "update"), V("x"), V("k"), V("b")), V("r")))));
        Formula right = Add(
            Mul(Subtract(NatComplex(V("n")), NatComplex(weight)),
                Add(Mul(At(V("a"), D(0), D(0)), coefficient), Mul(At(V("a"), D(0), D(1)), plus))),
            Mul(NatComplex(weight),
                Add(Mul(At(V("a"), D(1), D(0)), minus), Mul(At(V("a"), D(1), D(1)), coefficient))));
        return All("n", Nat, All("a", Square(FinOf(D(2))), All("x", Word(V("n")),
            All("r", FinOf(Add(V("n"), D(1))), Equal(left, right)))));
    }

    private static Formula V(string name) => name == "κ" ? Kappa : F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(name));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula Local(string name, params Formula[] args) => At(Qualified(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Type => Seq(Qualified("Type"), Star);
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Arrow(Formula domain, Formula range) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(range));
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b)));
    private static Formula Matrix(Formula rows, Formula columns, Formula field) => At(Qualified("Matrix"), rows, columns, field);
    private static Formula Square(Formula index) => Matrix(index, index, Complex);
    private static Formula Word(Formula n) => Arrow(FinOf(n), FinOf(D(2)));
    private static Formula SU2 => At(Qualified("CoeSort", "coe"),
        At(Qualified("Matrix", "specialUnitaryGroup"), FinOf(D(2)), Complex));
    private static Formula Val(Formula x) => At(Qualified("Subtype", "val"), x);
    private static Formula FinVal(Formula x) => At(Qualified("Fin", "val"), x);
    private static Formula OfReal(Formula x) => At(Qualified("Complex", "ofReal"), x);
    private static Formula NatReal(Formula x) => Typed(At(Qualified("Nat", "cast"), x), Real);
    private static Formula NatComplex(Formula x) => Typed(At(Qualified("Nat", "cast"), x), Complex);
    private static Formula Adj(Formula x) => At(Qualified("Matrix", "conjTranspose"), x);
    private static Formula Transpose(Formula x) => At(Qualified("Matrix", "transpose"), x);
    private static Formula Inv(Formula x) => At(Qualified("Inv", "inv"), x);
    private static Formula Mul(Formula x, Formula y) => Multiply(Parenthesized(x), Parenthesized(y));
    private static Formula Smul(Formula x, Formula y) => At(Qualified("HSMul", "hSMul"), x, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => Arrow(x, y);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) => Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula SumOf(string name, Formula type, Formula body) => Parenthesized(Seq(Sum, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body)));
    private static Formula If(Formula condition, Formula yes, Formula no) => Parenthesized(Seq(
        Qualified("if"), Sp, condition, Sp, Qualified("then"), Sp, yes, Sp, Qualified("else"), Sp, no));
    private static Formula Instances(Formula[] types, Formula body)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var type in types) parts.Add(Seq(OpenBracket, type, CloseBracket, Comma, Sp));
        parts.Add(Parenthesized(body));
        return Seq([.. parts]);
    }
    private static Formula Pauli(Formula a) => At(Qualified("pauli"), a);
    private static Formula LocalOp(Formula k, Formula a) => At(Qualified("localOp"), k, a);
    private static Formula Tensor(Formula n, Formula u) => At(Qualified("tensorOp"), At(Qualified("Function", "const"), FinOf(n), u));
    private static Formula PartialTrace(Formula x) => At(Qualified("partialTraceRight"), x);
    private static Formula Weight(Formula n, Formula x) => SumOf("k", FinOf(n), At(Qualified("Fin", "val"), At(x, V("k"))));
}
