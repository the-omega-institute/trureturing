using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class ThreeQubitStabilizerPolarEscapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/rubboli2024magicadditivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven anticommuting Pauli operators give positive three-qubit polar elements whose tensor product exceeds one on a stabilizer state.",
        H("Three-qubit stabilizer polar elements"), Blocks(
            Node("bits", "Computational basis indices", "Bits",
                All("n", Naturals(), Equal(Local("Bits", X("n")), Arrow(Fin(X("n")), Fin(Num(2))))),
                "An n-qubit computational basis index assigns a bit in Fin 2 to every coordinate in Fin n.",
                DescribeRole.Definition),
            Node("op", "Complex operators", "Op",
                All("n", Naturals(), Equal(Op(X("n")), At(Qualified("D5", "S3", "Quantum", "Measurement",
                    "StabilizerPovmMaximalEntanglementRefutation", "Operator"), X("n")))),
                "Op refers to D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.Operator: complex square matrices indexed by the computational basis.",
                DescribeRole.Definition),
            Node("is-state", "Density matrices", "IsState",
                All("n", Naturals(), All("rho", Op(X("n")),
                    IffOf(Local("IsState", X("rho")), At(Qualified("D5", "S3", "Quantum", "Information",
                        "SLDSpectralEnergy", "IsDensity"), X("rho"))))),
                "IsState refers to D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity: positive semidefiniteness and complex trace one, as in §2.",
                DescribeRole.Definition, Literature()),
            Node("tr", "Real part of the trace", "tr",
                All("n", Naturals(), All("A", Op(X("n")),
                    Equal(Local("tr", X("A")), At(Qualified("RHLinalg", "rtrace"), X("A"))))),
                "The real-valued trace refers to RHLinalg.rtrace, the real part of Matrix.trace. It is defined for every operator.",
                DescribeRole.Definition),
            Node("conjugate", "Entrywise complex conjugation", "conjugate",
                All("n", Naturals(), All("A", Op(X("n")), All("x", Bits(X("n")),
                    All("y", Bits(X("n")), Equal(At(Local("conjugate", X("A")), X("x"), X("y")),
                        Call("star", At(X("A"), X("x"), X("y")))))))),
                "Conjugation applies star to each complex entry without exchanging the row and column indices.",
                DescribeRole.Definition),
            Node("tensor", "Tensor products in bit coordinates", "tensor", TensorFormula(),
                "Matrix.kronecker initially uses pairs of basis indices. Matrix.submatrix reindexes both rows and columns by restriction to the first n and last m bits, using Fin.castAdd and Fin.natAdd respectively.",
                DescribeRole.Definition),
            Node("gate-h", "The Hadamard gate", "gateH",
                Equal(Name("gateH"), Information("BinaryStabilizerLocalInequivalence", "hadamard")),
                "The Hadamard gate is the matrix D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard. It is one of the Clifford generators in §2.",
                DescribeRole.Definition, Literature()),
            Node("gate-s", "The phase gate", "gateS",
                Equal(Name("gateS"), At(Qualified("Matrix", "diagonal"),
                    Vector(Typed(Num(1), Complexes()), Qualified("Complex", "I")))),
                "The phase gate is diagonal with entries 1 and Complex.I, the single-qubit phase gate of §2.",
                DescribeRole.Definition, Literature()),
            Node("gate-cnot", "Controlled addition of a bit", "gateCNOT", CnotFormula(),
                "The target bit is replaced by its sum with the control bit in Fin 2. The matrix entry is one exactly when this update sends the column index to the row index. Distinct control and target coordinates are required when choosing generators, as in §2.",
                DescribeRole.Definition, Literature()),
            Node("gates", "The generating gates", "gates", GatesFormula(),
                "The generating set consists of local Hadamard gates, local phase gates, and controlled-not gates with distinct control and target coordinates, as in §2.",
                DescribeRole.Definition, Literature()),
            Node("clifford", "The generated Clifford submonoid", "Clifford",
                All("n", Naturals(), Equal(Local("Clifford", X("n")),
                    At(Qualified("Submonoid", "closure"), At(Qualified("Set", "union"),
                        Local("gates", X("n")), At(Qualified("Set", "image"),
                            LambdaOf("U", Op(X("n")), Adjoint(X("U"))), Local("gates", X("n"))))))),
                "Section 2 defines the Clifford group by the Hadamard, phase and controlled-not generators. Here Submonoid.closure includes the generators and their conjugate transposes; it is a submonoid of the matrix monoid.",
                DescribeRole.Definition, Literature()),
            Node("vacuum", "The zero-bit projector", "vacuum", VacuumFormula(),
                "Matrix.single gives the projector onto the all-zero computational basis vector used in §2. Fin.castSucc (Fin.last 0) is the zero element of Fin 2.",
                DescribeRole.Definition, Literature()),
            Node("pure-stabilizer", "Pure stabilizer projectors", "PureStabilizer", PureFormula(),
                "The pure stabilizer projectors of §2 are conjugates of the zero-bit projector by elements of the Clifford submonoid.",
                DescribeRole.Definition, Literature()),
            Node("stab", "Mixed stabilizer states", "STAB",
                All("n", Naturals(), Equal(Local("STAB", X("n")),
                    Call("convexHull", Reals(), Local("PureStabilizer", X("n"))))),
                "The mixed stabilizer states in §2 form the convex hull over the real numbers of the pure stabilizer projectors.",
                DescribeRole.Definition, Literature()),
            Node("gamma-words", "The seven Pauli words", "gammaWords",
                Equal(Name("gammaWords"), GammaWordsFormula()),
                "The seven three-qubit words are XII, YII, ZXI, ZYI, ZZX, ZZY and ZZZ.",
                DescribeRole.Definition),
            Node("local-adjoint", "Adjoints of local gates", "local_adjoint", LocalAdjointFormula(),
                "Taking the adjoint commutes with embedding a single-qubit operator at a fixed coordinate.",
                DescribeRole.Theorem),
            Node("local-product", "Local gates preserve products", "local_product", LocalProductFormula(),
                "Embedding two single-qubit operators at the same coordinate preserves their product.",
                DescribeRole.Theorem),
            Node("local-identity", "The local identity gate", "local_identity", LocalIdentityFormula(),
                "Embedding the single-qubit identity at any coordinate gives the identity on the full register.",
                DescribeRole.Theorem),
            Node("s", "Seven anticommuting Pauli terms", "S", SFormula(),
                "The seven words are XII, YII, ZXI, ZYI, ZZX, ZZY and ZZZ. Their Pauli operators anticommute pairwise, so the cross terms in the square cancel.",
                DescribeRole.Definition),
            Node("sigma", "A three-qubit state", "sigma",
                Equal(Name("sigma"), Smul(Typed(Fraction(Num(1), Num(56)), Reals()),
                    Add(Smul(Typed(Num(7), Reals()), Identity(3)), Name("S")))),
                "This state is one seventh of the sum of the seven states obtained from the identity plus each Pauli term, divided by eight. Its expectation of S is one.",
                DescribeRole.Definition),
            Node("bell", "Three Bell pairs", "bell", BellFormula(),
                "The projector has entry 1/8 when the two three-bit halves of each basis index coincide, and zero otherwise. It is the maximally entangled state between the two three-qubit factors.",
                DescribeRole.Definition),
            Node("w", "Positive polar elements", "W",
                All("s", Reals(), Equal(Local("W", X("s")),
                    Smul(Typed(Fraction(Num(1), Add(Num(1), X("s"))), Reals()),
                        Add(Identity(3), Smul(X("s"), Name("S")))))),
                "For the parameter range in the theorem, this operator and its entrywise conjugate are positive definite and have expectation at most one on every three-qubit stabilizer state.",
                DescribeRole.Definition),
            Node("stabilizer-polar-tensor-escape", "The tensor product exceeds the polar bound",
                "stabilizer_polar_tensor_escape", EscapeFormula(),
                "For 1/3 < s and 7s² < 1, the two positive definite three-qubit operators each have expectation at most one on STAB 3. Their tensor product has expectation (1 + 7s²)/(1 + s)², strictly greater than one, on the six-qubit stabilizer state of three Bell pairs. The same statement supplies the state property of every stabilizer mixture, the expectation of S in sigma, the adjoint, square and trace of S, and the trace pairing for arbitrary three-qubit operators.",
                DescribeRole.Theorem)
        )));

    private static Formula TensorFormula()
    {
        Formula restriction = LambdaOf("x", Bits(Add(X("n"), X("m"))), Pair(
            LambdaOf("i", Fin(X("n")), At(X("x"), At(Qualified("Fin", "castAdd"), X("m"), X("i")))),
            LambdaOf("j", Fin(X("m")), At(X("x"), At(Qualified("Fin", "natAdd"), X("n"), X("j"))))));
        return All("n", Naturals(), All("m", Naturals(), All("A", Op(X("n")), All("B", Op(X("m")),
            Equal(Local("tensor", X("A"), X("B")), At(Qualified("Matrix", "submatrix"),
                At(Qualified("Matrix", "kronecker"), X("A"), X("B")), restriction, restriction))))));
    }

    private static Formula CnotFormula() => All("n", Naturals(), All("c", Fin(X("n")),
        All("t", Fin(X("n")), All("x", Bits(X("n")), All("y", Bits(X("n")),
            Equal(At(Local("gateCNOT", X("c"), X("t")), X("x"), X("y")),
                Call("ite", Equal(X("x"), At(Qualified("Function", "update"), X("y"), X("t"),
                    Add(At(X("y"), X("t")), At(X("y"), X("c"))))),
                    Typed(Num(1), Complexes()), Typed(Num(0), Complexes()))))))));

    private static Formula GatesFormula() => All("n", Naturals(),
        Equal(Local("gates", X("n")), SetOf("U", Op(X("n")),
            Or(Ex("i", Fin(X("n")), Equal(X("U"), At(Information("StabilizerPairLocalUnitaryInequivalence", "localOp"), X("i"), Name("gateH")))),
                Or(Ex("i", Fin(X("n")), Equal(X("U"), At(Information("StabilizerPairLocalUnitaryInequivalence", "localOp"), X("i"), Name("gateS")))),
                    Ex("c", Fin(X("n")), Ex("t", Fin(X("n")), And(NE(X("c"), X("t")),
                        Equal(X("U"), Local("gateCNOT", X("c"), X("t")))))))))));

    private static Formula VacuumFormula()
    {
        Formula zeroBits = At(Qualified("Function", "const"), Fin(X("n")),
            At(Qualified("Fin", "castSucc"), At(Qualified("Fin", "last"), Num(0))));
        return All("n", Naturals(), Equal(Local("vacuum", X("n")),
            At(Qualified("Matrix", "single"), zeroBits, zeroBits, Typed(Num(1), Complexes()))));
    }

    private static Formula PureFormula() => All("n", Naturals(),
        Equal(Local("PureStabilizer", X("n")), SetOf("rho", Op(X("n")),
            Ex("U", Op(X("n")), And(Mem(X("U"), Local("Clifford", X("n"))),
                Equal(X("rho"), Mul(Mul(X("U"), Local("vacuum", X("n"))), Adjoint(X("U")))))))));

    private static Formula GammaWordsFormula() => Vector(
        PauliWord("X", "I", "I"), PauliWord("Y", "I", "I"),
        PauliWord("Z", "X", "I"), PauliWord("Z", "Y", "I"),
        PauliWord("Z", "Z", "X"), PauliWord("Z", "Z", "Y"), PauliWord("Z", "Z", "Z"));

    private static Formula LocalAdjointFormula() => All("n", Naturals(), All("i", Fin(X("n")),
        All("A", QubitOp(), Equal(Adjoint(LocalOp(X("i"), X("A"))), LocalOp(X("i"), Adjoint(X("A")))))));

    private static Formula LocalProductFormula() => All("n", Naturals(), All("i", Fin(X("n")),
        All("A", QubitOp(), All("B", QubitOp(),
            Equal(Mul(LocalOp(X("i"), X("A")), LocalOp(X("i"), X("B"))),
                LocalOp(X("i"), Mul(X("A"), X("B"))))))));

    private static Formula LocalIdentityFormula() => All("n", Naturals(), All("i", Fin(X("n")),
        Equal(LocalOp(X("i"), Typed(Num(1), QubitOp())), Typed(Num(1), Op(X("n"))))));

    private static Formula QubitOp() => Call("Matrix", Fin(Num(2)), Fin(Num(2)), Complexes());
    private static Formula LocalOp(Formula i, Formula matrix) =>
        At(Information("StabilizerPairLocalUnitaryInequivalence", "localOp"), i, matrix);

    private static Formula SFormula() => Equal(Name("S"), SumOver("j", Fin(Num(7)),
        At(Information("StabilizerPairLocalUnitaryInequivalence", "wordOp"),
            At(GammaWordsFormula(), X("j")))));

    private static Formula BellFormula() => All("x", Bits(Num(6)), All("y", Bits(Num(6)),
        Equal(At(Name("bell"), X("x"), X("y")), Call("ite",
            And(Equal(Half(X("x"), true), Half(X("x"), false)),
                Equal(Half(X("y"), true), Half(X("y"), false))),
            Typed(Fraction(Num(1), Num(8)), Complexes()), Typed(Num(0), Complexes())))));

    private static Formula Half(Formula bits, bool first) => LambdaOf("i", Fin(Num(3)),
        At(bits, At(Qualified("Fin", first ? "castAdd" : "natAdd"), Num(3), X("i"))));

    private static Formula EscapeFormula()
    {
        Formula w = Local("W", X("s"));
        Formula conjugateW = Local("conjugate", w);
        Formula bellValue = Local("tr", Mul(Name("bell"), Local("tensor", w, conjugateW)));
        Formula[] clauses = [
            All("n", Naturals(), All("eta", Op(X("n")),
                Imp(Mem(X("eta"), Local("STAB", X("n"))), Local("IsState", X("eta"))))),
            And(Local("IsState", Name("sigma")), Equal(Local("tr", Mul(Name("sigma"), Name("S"))), Num(1))),
            Equal(Adjoint(Name("S")), Name("S")),
            Equal(Mul(Name("S"), Name("S")), Smul(Typed(Num(7), Complexes()), Identity(3))),
            Equal(Trace(Name("S")), Typed(Num(0), Complexes())),
            All("A", Op(Num(3)), All("B", Op(Num(3)),
                Equal(Local("tr", Mul(Name("bell"), Local("tensor", X("A"), Local("conjugate", X("B"))))),
                    Fraction(Local("tr", Mul(X("A"), Adjoint(X("B")))), Num(8))))),
            Mem(Name("bell"), Local("STAB", Num(6))),
            At(Qualified("Matrix", "PosDef"), w),
            At(Qualified("Matrix", "PosDef"), conjugateW),
            All("eta", Op(Num(3)), Imp(Mem(X("eta"), Local("STAB", Num(3))),
                And(LE(Local("tr", Mul(X("eta"), w)), Num(1)),
                    LE(Local("tr", Mul(X("eta"), conjugateW)), Num(1))))),
            Equal(bellValue, Fraction(Add(Num(1), Mul(Num(7), Power(X("s"), Num(2)))),
                Power(Add(Num(1), X("s")), Num(2)))),
            LT(Num(1), bellValue)
        ];
        Formula conclusion = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--) conclusion = And(clauses[i], conclusion);
        return All("s", Reals(), Imp(LT(Fraction(Num(1), Num(3)), X("s")),
            Imp(LT(Mul(Num(7), Power(X("s"), Num(2))), Num(1)), conclusion)));
    }

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static AssessedProvenance Literature() => AssessedProvenance.FromLiterature(Source);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        Formula value = X(parts[0]);
        for (int i = 1; i < parts.Length; i++) value = Seq(value, Dot, X(parts[i]));
        return Seq(Operatorname, Grp(value));
    }
    private static Formula Name(string name) => Qualified("D5", "S3", "Quantum", "Magic", "ThreeQubitStabilizerPolarEscape", name);
    private static Formula Local(string name, params Formula[] args) => At(Name(name), args);
    private static Formula Information(string module, string name) => Qualified("D5", "S3", "Quantum", "Information", module, name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Bits(Formula n) => Local("Bits", n);
    private static Formula Op(Formula n) => Local("Op", n);
    private static Formula Identity(long n) => Typed(Num(1), Op(Num(n)));
    private static Formula Trace(Formula value) => At(Qualified("Matrix", "trace"), value);
    private static Formula Adjoint(Formula value) => At(Qualified("Matrix", "conjTranspose"), value);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Pair(Formula left, Formula right) => Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Vector(params Formula[] entries)
    {
        Formula content = entries[0];
        for (int i = 1; i < entries.Length; i++) content = Seq(content, Comma, Sp, entries[i]);
        return Seq(Bang, OpenBracket, content, CloseBracket);
    }
    private static Formula PauliWord(string a, string b, string c) => Vector(Pauli(a), Pauli(b), Pauli(c));
    private static Formula Pauli(string letter) => Qualified("D5", "S3", "Quantum", "Information", "StabilizerPairLocalUnitaryInequivalence", "Pauli", letter);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula LambdaOf(string name, Formula domain, Formula body) => Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), domain), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula SumOver(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum, Typed(X(name), domain)), Sp, Parenthesized(body));
    private static Formula SetOf(string name, Formula domain, Formula condition) => Seq(OpenBrace, Typed(X(name), domain), Sp, Mid, Sp, condition, CloseBrace);
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Smul(Formula scalar, Formula value) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula NE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Mem(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
