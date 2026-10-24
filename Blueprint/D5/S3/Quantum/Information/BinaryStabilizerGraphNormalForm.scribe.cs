using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class BinaryStabilizerGraphNormalFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm.";
    private static readonly LibraryNoteRef GraphStates =
        LibraryNoteRef.Create("D5/L/QuantumStates/vandennest2004graphical");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary quadratic phases describe graph states. A Pauli stabilizer line can be put in this form by single-qubit unitaries.",
        H("Quadratic amplitudes and the graph form of stabilizer states"),
        Blocks(
            Entry("sign-representative", "complex_sign_val", "The sign of the binary representative", SignRepresentative(),
                "The complexSign value is −1 raised to the natural representative of a binary residue.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Entry("symplectic-form", "spForm", "The binary symplectic bilinear form", SymplecticForm(),
                "The binary symplectic form pairs the translation coordinates of either vector with the phase coordinates of the other.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Entry("symplectic-alternating", "sp_alt", "Alternation of the binary symplectic form", SymplecticProperty("IsAlt"),
                "Every binary vector has zero symplectic pairing with itself.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Entry("symplectic-nondegenerate", "sp_nondegenerate", "Nondegeneracy of the binary symplectic form", SymplecticProperty("Nondegenerate"),
                "A vector that pairs to zero with every binary vector is the zero vector.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Entry("amplitude", "graphAmp", "The binary graph amplitude", Amplitude(),
                "Each edge contributes its binary quadratic monomial. The ordered upper-triangular sum is normalExponent; graphAmp is the complexSign value of that exponent, equivalently −1 raised to its natural representative. This definition accepts every binary matrix, without a symmetry or diagonal hypothesis.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(GraphStates)),
            Entry("tensor-adjoint", "tensor_adj", "Adjoints of tensor products", TensorAdjoint(),
                "The conjugate transpose of a tensor product is the tensor product of the conjugate transposes of its factors.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Entry("tensor-unitary", "tensor_unitary", "Tensor products of unitary factors", TensorUnitary(),
                "If every single-qubit factor is unitary, their tensor product is unitary on the full binary register.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Entry("tensor-scalar", "tensor_smul", "Scalars in tensor products", TensorScalar(),
                "Scaling each single-qubit factor scales the tensor product by the product of those scalars.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Entry("tensor-weyl", "tensor_weyl", "The tensor action of binary Weyl factors", TensorWeyl(),
                "Each single-qubit matrix translates the binary coordinate by v.fst(i) and multiplies it by the sign of v.snd(i) times the input coordinate. The displayed matrix entries and translated function write out both sides of the tensor action. Fin 2 and ZMod 2 have the same binary representatives; id leaves these representatives unchanged.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Entry("gate", "gate", "Binary choices of Hadamard and phase gates", GateDefinition(),
                "The binary phase choice multiplies the optional Hadamard gate on the left. Zero phase selects the identity and nonzero phase selects the diagonal matrix with entries 1 and i.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Entry("gate-unitary", "gate_unitary", "Unitarity of the binary gate family", GateUnitary(),
                "Every combination of the binary phase choice and the Hadamard choice is a unitary single-qubit matrix.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Entry("normal-form", "stabilizer_graph_normal_form", "A graph amplitude for every stabilizer line", NormalForm(),
                "The Pauli stabilizers of a nonzero common eigenline span a binary Lagrangian subspace. Coordinate swaps and a diagonal shear express that subspace as the graph of a symmetric matrix with zero diagonal. Hadamard and phase gates implement these transformations, and Pauli signs identify the remaining line with the quadratic amplitude. Taking the inverse gates gives the unitaries U and the scalar c in the displayed equation; SMul.smul denotes scalar action on the amplitude vector.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(GraphStates)))));

    private static Formula SignRepresentative() => All(V("a"), Binary,
        Equal(Call("complexSign", V("a")),
            Pow(Typed(Seq(Minus, D(1)), Complex), Property(V("a"), "val"))));

    private static Formula BinaryPhaseSpace => Parenthesized(Seq(
        Arrow(Fin(V("N")), Binary), Sp, Times, Sp, Arrow(Fin(V("N")), Binary)));

    private static Formula SymplecticForm() => All(V("N"), Nat,
        All(V("u"), BinaryPhaseSpace, All(V("v"), BinaryPhaseSpace,
            Equal(Apply(Call("spForm", V("N")), V("u"), V("v")),
                Qualified("BinaryLagrangianGraphForm", "sp", V("u"), V("v"))))));

    private static Formula SymplecticProperty(string property) => All(V("N"), Nat,
        Property(Call("spForm", V("N")), property));

    private static Formula Amplitude() => All(V("N"), Nat,
        All(Gamma, Matrix(Fin(V("N")), Binary), All(V("x"), Arrow(Fin(V("N")), Fin(D(2))),
            Equal(Call("graphAmp", Gamma, V("x")),
                Pow(Typed(Seq(Minus, D(1)), Complex),
                    Property(Call("normalExponent", Gamma, Typed(V("x"), Arrow(Fin(V("N")), Binary))), "val"))))));

    private static Formula TensorAdjoint() => All(V("N"), Nat,
        All(V("A"), Arrow(Fin(V("N")), Matrix(Fin(D(2)), Complex)),
            Equal(Qualified("Matrix", "conjTranspose", TensorOperator(V("A"))),
                TensorOperator(Seq(LambdaLower, Sp, Typed(V("i"), Fin(V("N"))), Sp, Mapsto, Sp,
                    Qualified("Matrix", "conjTranspose", Apply(V("A"), V("i"))))))));

    private static Formula TensorUnitary() => All(V("N"), Nat,
        All(V("A"), Arrow(Fin(V("N")), Matrix(Fin(D(2)), Complex)),
            Imp(Parenthesized(All(V("i"), Fin(V("N")),
                    Seq(Apply(V("A"), V("i")), Sp, InMacro, Sp,
                        Qualified("Matrix", "unitaryGroup", Fin(D(2)), Complex)))),
                Seq(TensorOperator(V("A")), Sp, InMacro, Sp,
                    Qualified("Matrix", "unitaryGroup", Arrow(Fin(V("N")), Fin(D(2))), Complex)))));

    private static Formula TensorScalar()
    {
        Formula factors = Seq(LambdaLower, Sp, Typed(V("i"), Fin(V("N"))), Sp, Mapsto, Sp,
            Qualified("SMul", "smul", Apply(V("r"), V("i")), Apply(V("A"), V("i"))));
        Formula coefficient = Seq(new Formula.Subscript(Prod, Seq(V("i"), Sp, InMacro, Sp, Fin(V("N")))),
            Sp, Apply(V("r"), V("i")));
        return All(V("N"), Nat, All(V("r"), Arrow(Fin(V("N")), Complex),
            All(V("A"), Arrow(Fin(V("N")), Matrix(Fin(D(2)), Complex)),
                Equal(TensorOperator(factors),
                    Qualified("SMul", "smul", coefficient, TensorOperator(V("A")))))));
    }

    private static Formula TensorWeyl()
    {
        Formula bitVector = Arrow(Fin(V("N")), Binary);
        Formula pair = Parenthesized(Seq(bitVector, Sp, Times, Sp, bitVector));
        Formula LambdaOf(string name, Formula type, Formula body) =>
            Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body);
        Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
        Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
        Formula x = Apply(Property(V("v"), "fst"), V("i"));
        Formula z = Apply(Property(V("v"), "snd"), V("i"));
        Formula s = Call("id", Typed(V("s"), Binary)), t = Call("id", Typed(V("t"), Binary));
        Formula entry = Parenthesized(Seq(V("if"), Sp, Equal(s, Add(t, x)), Sp, V("then"), Sp,
            Call("complexSign", Mul(z, s)), Sp, V("else"), Sp, D(0)));
        Formula factors = LambdaOf("i", Fin(V("N")), Qualified("Matrix", "of",
            LambdaOf("t", Fin(D(2)), LambdaOf("s", Fin(D(2)), entry))));
        Formula exponent = Seq(Sum, Underscore, Grp(V("i"), Colon, Sp, Fin(V("N"))), Sp,
            Parenthesized(Mul(z, Parenthesized(Add(Apply(V("t"), V("i")), x)))));
        Formula translated = LambdaOf("t", bitVector,
            Mul(Call("complexSign", exponent), Apply(V("f"), Add(V("t"), Property(V("v"), "fst")))));
        return All(V("N"), Nat, All(V("v"), pair, All(V("f"), Arrow(bitVector, Complex),
            Equal(Qualified("Matrix", "mulVec", TensorOperator(factors), V("f")),
                translated))));
    }

    private static Formula GateDefinition() => All(V("h"), V("Bool"), All(V("d"), Binary,
        Equal(Call("gate", V("h"), V("d")),
            Seq(Parenthesized(Seq(V("if"), Sp, Equal(V("d"), D(0)), Sp, V("then"), Sp,
                    D(1), Sp, V("else"), Sp, Qualified("Matrix", "diagonal",
                        Seq(Bang, OpenBracket, D(1), Comma, Sp, Qualified("Complex", "I"), CloseBracket)))), Sp, Star, Sp,
                Parenthesized(Seq(V("if"), Sp, V("h"), Sp, V("then"), Sp,
                    Qualified("BinaryStabilizerLocalInequivalence", "hadamard"), Sp,
                    V("else"), Sp, D(1)))))));

    private static Formula GateUnitary() => All(V("h"), V("Bool"), All(V("d"), Binary,
        Seq(Call("gate", V("h"), V("d")), Sp, InMacro, Sp,
            Qualified("Matrix", "unitaryGroup", Fin(D(2)), Complex))));

    private static Formula TensorOperator(Formula a) => Seq(V("D5"), Dot, V("S3"), Dot,
        V("Quantum"), Dot, V("Information"), Dot,
        V("StabilizerPairLocalUnitaryInequivalence"), Dot, Call("tensorOp", a));

    private static Formula NormalForm() => All(V("N"), Nat,
        All(Psi, Arrow(Arrow(Fin(V("N")), Fin(D(2))), Complex),
            Imp(Call("StabilizedBy", V("pauliSet"), Psi),
                Some(V("U"), Arrow(Fin(V("N")), Matrix(Fin(D(2)), Complex)),
                    Some(Gamma, Matrix(Fin(V("N")), Binary), Some(V("c"), Complex,
                        Conj(Parenthesized(All(V("i"), Fin(V("N")),
                                Seq(Call("U", V("i")), Sp, InMacro, Sp, Call("unitaryGroup", Fin(D(2)), Complex)))),
                            Conj(Property(Gamma, "IsSymm"),
                                Conj(Parenthesized(All(V("i"), Fin(V("N")), Equal(Apply(Gamma, V("i"), V("i")), D(0)))),
                                    Equal(Psi, Qualified("SMul", "smul", V("c"), Parenthesized(
                                        Seq(Call("tensorOp", V("U")), Sp, Star, Underscore, Grp(V("v")), Sp,
                                            Call("graphAmp", Gamma))))))))))))));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula statement,
        string explanation, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), provenance,
            Blocks(Paragraph(Text(explanation))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Binary => Call("ZMod", D(2));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Matrix(Formula index, Formula field) => Call("Matrix", index, index, field);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula name, Formula type) => Parenthesized(Seq(name, Sp, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, bodyGroup(b));
    private static Formula bodyGroup(Formula x) => Parenthesized(x);
    private static Formula Conj(Formula a, Formula b) => Seq(a, Sp, Land, Sp, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Property(Formula x, string property) => Seq(Parenthesized(x), Dot, V(property));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) => Seq(V(owner), Dot, Call(name, args));
    private static Formula Apply(Formula f, params Formula[] args) => Seq(f, Parenthesized(Arguments(args)));
    private static Formula Arguments(Formula[] args) => Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x })]);
}
