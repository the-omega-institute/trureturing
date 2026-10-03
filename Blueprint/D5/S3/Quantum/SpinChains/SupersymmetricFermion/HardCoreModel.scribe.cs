using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains.SupersymmetricFermion;

internal sealed class HardCoreModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/SupersymmetricFermion/HardCoreModel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/beccaria2012staggered");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jordan-Wigner fermions, hard-core compression and the M1 boundary sum rule.",
        H("Supersymmetric fermion chain: HardCoreModel"),
        Blocks(
            Paragraph(Text("Nat, Real, Complex and Bool denote the natural numbers, real numbers, complex numbers and the two occupation values false and true. Assignment(N) is Fin N → Bool. All finite-type sums and products range over the displayed type; range(N) is {0,...,N−1}. Subtraction in Nat is truncated at zero; mod is natural remainder, inv is field inverse, smul is scalar multiplication and div is field division. asReal and the annotation Complex retain scalar casts. val denotes the value of a Fin index or subtype; mk displays a Fin value with its proof component suppressed. adjoint is the conjugate transpose on matrices and the genuine Hilbert adjoint on linear operators. A mapsto denotes a function; const denotes a constant function with the domain supplied by its type. Lambda applications express local let substitutions. spinZ denotes qubitZ transported through finTwoEquiv : Fin 2 ≃ Bool; spinP is 1−visibleProjector. Matrixsingle(false,true,1) is Mathlib’s elementary matrix on Boolean indices, with entry 1 at the empty-row/occupied-column pair and 0 elsewhere. tensorOp(w) is the tensor product transported to Boolean coordinates: its entry at s,t is ∏_(i : Fin N) w(i)(s(i))(t(i)). These are local notations, not additional operators. boolReindex transports a matrix from Fin N → Fin 2 to Fin N → Bool through the pointwise finTwoEquiv. finTwoReindex transports the Boolean visibleProjector to Fin 2 indices; localOp is the existing single-site tensor operator. submatrix(A,Subtypeval,Subtypeval) restricts both matrix indices to the hard-core subtype. All other names refer to the displayed definitions or Mathlib operations; function names omit dots and underscores.")),
            Node("HardCore", "HardCore", F1(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. HardCore is the subtype defined by Adm(N,s), the admissible-word predicate of AdmissibleCount. ForbiddenNeighbourDeterminant.adm_iff_no_adjacent_true identifies that predicate with nearest-neighbour exclusion.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("HardCoreSpace", "HardCoreSpace", F2(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines HardCoreSpace.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Operator", "Operator", F3(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines Operator.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("occupied", "occupied", F4(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines occupied.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("annihilationAt", "annihilationAt", F5(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines annihilationAt.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("c", "c", F6(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines c.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("number", "number", F7(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines number.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("P", "P", F8(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines P.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("d", "d", F9(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines d.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("periodThree", "periodThree", F10(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines periodThree.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("stagII", "stagII", F11(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines stagII.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Qmat", "Qmat", F12(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines Qmat.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Q", "Q", F13(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines Q.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("H", "H", F14(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines H.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("density", "density", F15(),
                "Section 2.1, printed page 3: “nearest-neighbour exclusion: at most one of two adjacent sites may be occupied.” “We shall work with free boundary conditions what is equivalent to add two inaccessible but empty sites at j = 0 and j = N + 1.” The operators use the supercharge, projectors and Hamiltonian of that section. The displayed equation defines density.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Rmat", "Rmat", F16(),
                "The displayed equation defines Rmat.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("annihilator_number", "Occupation from fermion annihilation", F17(),
                "The product c(j)†c(j) is the occupation diagonal, including the zero operator outside the chain. Erasing an occupied site preserves nearest-neighbour exclusion. Erasure is injective on configurations with that site occupied, and the Jordan-Wigner signs cancel between the adjoint and annihilator. Hence the projector P(j) equals 1 minus the fermion number c(j)†c(j) used in the source model.", DescribeRole.Theorem, AssessedProvenance.FromRepo()))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("m1-hardcoremodel-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula N(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula F1() =>
        Disp(All("N", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("HardCore", N("N")), Colon, N("Type"))),
        FormulaRelationOperator.Equal, Call("Subtype", Seq(N("s"), Colon, Call("Assignment", N("N")), Mapsto,
        Parenthesized(Call("Adm", N("N"), N("s"))))))));

    private static Formula F2() =>
        Disp(All("N", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("HardCoreSpace", N("N")), Colon,
        N("Type"))), FormulaRelationOperator.Equal, Call("EuclideanSpace", N("Complex"), Call("HardCore", N("N"))))));

    private static Formula F3() =>
        Disp(All("N", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("Operator", N("N")), Colon, N("Type"))),
        FormulaRelationOperator.Equal, Call("Matrix", Call("HardCore", N("N")), Call("HardCore", N("N")),
        N("Complex")))));

    private static Formula F4() =>
        Disp(All("N", N("Nat"), All("s", Call("Assignment", N("N")), All("j", N("Nat"), new
        Formula.Relation(Parenthesized(Seq(Call("occupied", N("N"), N("s"), N("j")), Colon, N("Bool"))),
        FormulaRelationOperator.Equal, Call("ite", new Formula.Logic(Parenthesized(new Formula.Relation(D(0),
        FormulaRelationOperator.LessThan, N("j"))), FormulaLogicOperator.And, Parenthesized(new
        Formula.Relation(N("j"), FormulaRelationOperator.LessThanOrEqual, N("N")))), new Formula.Apply(N("s"),
        [Call("mk", new Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Subtract, Parenthesized(D(1))))]),
        N("false")))))));

    private static Formula F5() =>
        Disp(All("N", N("Nat"), All("i", Call("Fin", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("annihilationAt", N("N"), N("i")), Colon, Call("Operator", N("N")))),
        FormulaRelationOperator.Equal, Seq(N("s"), Comma, N("t"), Mapsto, Parenthesized(Call("ite", new
        Formula.Logic(Parenthesized(new Formula.Relation(Call("val", N("t"), N("i")), FormulaRelationOperator.Equal,
        N("true"))), FormulaLogicOperator.And, Parenthesized(new Formula.Relation(Call("val", N("s")),
        FormulaRelationOperator.Equal, Call("Functionupdate", Call("val", N("t")), N("i"), N("false"))))), new
        Formula.Power(Parenthesized(Parenthesized(Seq(new Formula.Negate(D(1)), Colon, N("Complex")))),
        Call("prefixCount", Call("val", N("t")), N("i"))), D(0))))))));

    private static Formula F6() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("c", N("N"), N("j")),
        Colon, Call("Operator", N("N")))), FormulaRelationOperator.Equal, Call("ite", new
        Formula.Logic(Parenthesized(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, N("j"))),
        FormulaLogicOperator.And, Parenthesized(new Formula.Relation(N("j"), FormulaRelationOperator.LessThanOrEqual,
        N("N")))), Call("annihilationAt", Call("mk", new Formula.Binary(Parenthesized(N("j")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1))))), D(0))))));

    private static Formula F7() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("number", N("N"),
        N("j")), Colon, Call("Operator", N("N")))), FormulaRelationOperator.Equal, Call("Matrixdiagonal", Seq(N("s"),
        Mapsto, Parenthesized(Call("ite", Call("occupied", Call("val", N("s")), N("j")), D(1), D(0)))))))));

    private static Formula F8() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("P", N("N"), N("j")),
        Colon, Call("Operator", N("N")))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(D(1)),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("number", N("j"))))))));

    private static Formula F9() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), new Formula.Relation(Parenthesized(Seq(Call("d", N("N"), N("j")),
        Colon, Call("Operator", N("N")))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("P", new Formula.Binary(Parenthesized(N("j")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("c", N("j"))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("P", new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))))));

    private static Formula F10() =>
        Disp(All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), All("j", N("Nat"), new
        Formula.Relation(Call("asReal", Call("periodThree", N("a"), N("b"), N("cc"), N("j"))),
        FormulaRelationOperator.Equal, Call("ite", new Formula.Relation(Call("mod", N("j"), D(3)),
        FormulaRelationOperator.Equal, D(1)), N("a"), Call("ite", new Formula.Relation(Call("mod", N("j"), D(3)),
        FormulaRelationOperator.Equal, D(2)), N("b"), N("cc")))))))));

    private static Formula F11() =>
        Disp(All("y", N("Real"), new Formula.Relation(Parenthesized(Seq(Call("stagII", N("y")), Colon, new
        Formula.TypeArrow(N("Nat"), N("Real")))), FormulaRelationOperator.Equal, Call("periodThree", N("y"), N("y"),
        D(1)))));

    private static Formula F12() =>
        Disp(All("N", N("Nat"), All("coupling", new Formula.TypeArrow(N("Nat"), N("Real")), new
        Formula.Relation(Parenthesized(Seq(Call("Qmat", N("N"), N("coupling")), Colon, Call("Operator", N("N")))),
        FormulaRelationOperator.Equal, Seq(Sum, Underscore, Grp(Seq(N("j"), InMacro, Call("Finsetrange", N("N")))),
        Parenthesized(Call("smul", Parenthesized(Seq(new Formula.Apply(N("coupling"), [new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(1)))]), Colon,
        N("Complex"))), Call("d", new Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add,
        Parenthesized(D(1)))))))))));

    private static Formula F13() =>
        Disp(All("N", N("Nat"), All("coupling", new Formula.TypeArrow(N("Nat"), N("Real")), new
        Formula.Relation(Parenthesized(Seq(Call("Q", N("N"), N("coupling")), Colon, Call("LinearMap", N("Complex"),
        Call("HardCoreSpace", N("N")), Call("HardCoreSpace", N("N"))))), FormulaRelationOperator.Equal,
        Call("MatrixtoEuclideanLin", Call("Qmat", N("N"), N("coupling")))))));

    private static Formula F14() =>
        Disp(All("N", N("Nat"), All("coupling", new Formula.TypeArrow(N("Nat"), N("Real")), new
        Formula.Relation(Parenthesized(Seq(Call("H", N("N"), N("coupling")), Colon, Call("LinearMap", N("Complex"),
        Call("HardCoreSpace", N("N")), Call("HardCoreSpace", N("N"))))), FormulaRelationOperator.Equal, new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("Q", N("N"), N("coupling"))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("adjoint", Call("Q", N("N"), N("coupling")))))),
        FormulaBinaryOperator.Add, Parenthesized(new Formula.Binary(Parenthesized(Call("adjoint", Call("Q", N("N"),
        N("coupling")))), FormulaBinaryOperator.Multiply, Parenthesized(Call("Q", N("N"), N("coupling"))))))))));

    private static Formula F15() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"), All("psi", Call("HardCoreSpace", N("N")), new
        Formula.Relation(Parenthesized(Seq(Call("density", N("N"), N("j"), N("psi")), Colon, N("Complex"))),
        FormulaRelationOperator.Equal, Call("div", Call("inner", N("Complex"), N("psi"), Call("MatrixtoEuclideanLin",
        Call("number", N("j")), N("psi"))), Call("inner", N("Complex"), N("psi"), N("psi"))))))));

    private static Formula F16() =>
        Disp(All("N", N("Nat"), All("a", N("Real"), All("b", N("Real"), All("cc", N("Real"), new
        Formula.Relation(Parenthesized(Seq(Call("Rmat", N("N"), N("a"), N("b"), N("cc")), Colon, Call("Operator",
        N("N")))), FormulaRelationOperator.Equal, new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(Call("smul",
        Call("asReal", new Formula.Binary(Parenthesized(N("a")), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(N("cc")), D(2))))), Call("adjoint", Call("d", D(1))))),
        FormulaBinaryOperator.Subtract, Parenthesized(Call("smul", Call("asReal", new Formula.Binary(Parenthesized(new
        Formula.Power(Parenthesized(N("a")), D(2))), FormulaBinaryOperator.Multiply, Parenthesized(N("cc")))),
        Call("adjoint", Call("d", N("N"))))))), FormulaBinaryOperator.Add, Parenthesized(Seq(Sum, Underscore,
        Grp(Seq(N("k"), InMacro, Call("Finsetrange", new Formula.Binary(Parenthesized(N("N")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(2)))))), Parenthesized(new
        Formula.Apply(Parenthesized(Seq(N("j"), Mapsto, Parenthesized(Call("smul", Call("asReal", new
        Formula.Binary(Parenthesized(Call("periodThree", N("a"), N("b"), N("cc"), N("j"))),
        FormulaBinaryOperator.Multiply, Parenthesized(new Formula.Power(Parenthesized(Call("periodThree", N("a"),
        N("b"), N("cc"), new Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(1))))), D(2))))), new Formula.Binary(Parenthesized(Call("number", new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Subtract, Parenthesized(D(2))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("adjoint", Call("d", N("j"))))))))), [new
        Formula.Binary(Parenthesized(N("k")), FormulaBinaryOperator.Add, Parenthesized(D(3)))])))))),
        FormulaBinaryOperator.Subtract, Parenthesized(Seq(Sum, Underscore, Grp(Seq(N("k"), InMacro,
        Call("Finsetrange", new Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract,
        Parenthesized(D(2)))))), Parenthesized(new Formula.Apply(Parenthesized(Seq(N("j"), Mapsto,
        Parenthesized(Call("smul", Call("asReal", new Formula.Binary(Parenthesized(Call("periodThree", N("a"), N("b"),
        N("cc"), N("j"))), FormulaBinaryOperator.Multiply, Parenthesized(new
        Formula.Power(Parenthesized(Call("periodThree", N("a"), N("b"), N("cc"), new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(1))))), D(2))))), new
        Formula.Binary(Parenthesized(Call("number", new Formula.Binary(Parenthesized(N("j")),
        FormulaBinaryOperator.Add, Parenthesized(D(2))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("adjoint", Call("d", N("j"))))))))), [new Formula.Binary(Parenthesized(N("k")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))])))))), FormulaBinaryOperator.Add, Parenthesized(Call("smul",
        Call("asReal", new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(N("a")),
        FormulaBinaryOperator.Multiply, Parenthesized(N("b")))), FormulaBinaryOperator.Multiply,
        Parenthesized(N("cc")))), Seq(Sum, Underscore, Grp(Seq(N("k"), InMacro, Call("Finsetrange", new
        Formula.Binary(Parenthesized(N("N")), FormulaBinaryOperator.Subtract, Parenthesized(D(2)))))),
        Parenthesized(new Formula.Apply(Parenthesized(Seq(N("j"), Mapsto, Parenthesized(new
        Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new Formula.Binary(Parenthesized(new
        Formula.Binary(Parenthesized(Call("P", new Formula.Binary(Parenthesized(N("j")),
        FormulaBinaryOperator.Subtract, Parenthesized(D(1))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("adjoint", Call("c", N("j")))))), FormulaBinaryOperator.Multiply,
        Parenthesized(Call("adjoint", Call("c", new Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add,
        Parenthesized(D(2)))))))), FormulaBinaryOperator.Multiply, Parenthesized(Call("c", new
        Formula.Binary(Parenthesized(N("j")), FormulaBinaryOperator.Add, Parenthesized(D(1))))))),
        FormulaBinaryOperator.Multiply, Parenthesized(Call("P", new Formula.Binary(Parenthesized(N("j")),
        FormulaBinaryOperator.Add, Parenthesized(D(3))))))))), [new Formula.Binary(Parenthesized(N("k")),
        FormulaBinaryOperator.Add, Parenthesized(D(1)))]))))))))))));


    private static Formula F17() =>
        Disp(All("N", N("Nat"), All("j", N("Nat"),
            new Formula.Relation(
                new Formula.Binary(Parenthesized(Call("adjoint", Call("c", N("N"), N("j")))),
                    FormulaBinaryOperator.Multiply, Parenthesized(Call("c", N("N"), N("j")))),
                FormulaRelationOperator.Equal, Call("number", N("N"), N("j"))))));

}
