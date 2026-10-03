using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class WignerDistanceMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/WignerDistanceMinimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/dutta2026wignerdistance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The free Wigner polytopes are compact and nonempty, so the source minimum defining C is attained and minimal in the L1 norm.",
        H("Wigner distance minimum attainment"),
        Blocks(
            Definition("PhasePoint", "The phase-point carrier",
                Equal(V("PhasePoint"), Product(Fin(2), Fin(2))),
                "A phase point is a pair (q,p) of binary indices, with Fin 2 representing the elements 0 and 1 of the paper's F₂."),
            Definition("phasePoint", "The Wootters phase-point operator", PhaseFormula(),
                "Page 3: \"The single-qubit phase-point operators are indexed by αₖ = (qₖ, pₖ) ∈ F₂²:\" followed by A_(qₖ,pₖ) = ½(I + (−1)^pₖ X + (−1)^(qₖ+pₖ) Y + (−1)^qₖ Z). Here q = fst(a), p = snd(a), and val reads their natural-number representatives. The coefficient ½ and the sign powers are complex scalars; 1 inside the matrix sum is the identity matrix."),
            Definition("phasePointTwo", "The product frame",
                All("a", Product(Pt(), Pt()), Equal(Call("phasePointTwo", V("a")),
                    Tensor(Call("phasePoint", Call("fst", V("a"))), Call("phasePoint", Call("snd", V("a")))))),
                "Page 3: \"For n qubits, A_α = A_α₁ ⊗ ··· ⊗ A_αₙ, and the discrete Wigner function is\" W_ρ(α) = (1/2ⁿ) tr(ρ A_α). phasePointTwo uses n = 2. kronecker denotes the matrix tensor product in the product computational basis."),
            Definition("Wigner", "The Wigner transform", WignerFormula(),
                "Page 3: \"For n qubits, A_α = A_α₁ ⊗ ··· ⊗ A_αₙ, and the discrete Wigner function is\" W_ρ(α) = (1/2ⁿ) tr(ρ A_α). The generic transform divides the real part of the trace by the Hilbert-space dimension, card(ι); for one and two qubits this is 2 and 4. The trace is real on Hermitian states. The division is real division after casting card(ι) to R."),
            Definition("WignerOne", "One-qubit Wigner coordinates",
                All("rho", Qubit(), Equal(Call("WignerOne", V("rho")), Call("Wigner", V("phasePoint"), V("rho")))),
                "WignerOne is the transform in the four-point single-qubit frame."),
            Definition("WignerTwo", "Two-qubit Wigner coordinates",
                All("rho", TwoQubit(), Equal(Call("WignerTwo", V("rho")), Call("Wigner", V("phasePointTwo"), V("rho")))),
                "WignerTwo is the transform in the sixteen-point product frame."),
            Definition("pauliTwo", "The phased Pauli group on two qubits", PauliFormula(true),
                "Page 3: \"The n-qubit Pauli group Pₙ consists of n-fold tensor products of {I, X, Y, Z} with phases {±1, ±i}.\" These are the actual phased tensor-product matrices, including all four phases."),
            Definition("Stab", "Stabilizer states from their subgroups", StabilizerFormula(),
                "Page 3: \"A stabilizer state is the unique +1 eigenstate of an abelian subgroup S ≤ Pₙ of size 2ⁿ.\" Stab(P) requires an actual subgroup of the matrix unitary group whose matrices belong to P, with cardinality equal to the Hilbert-space dimension. The subgroup is abelian, ψ is normalized, and its common +1 eigenspace is exactly the complex line spanned by ψ. The density is the outer product ψψ*. NatCard denotes Nat.card; card denotes Fintype.card. The two val calls unwrap the subgroup and unitary subtypes. mulVec is matrix action, smul is scalar multiplication, and vecMulVec is the outer product."),
            Definition("Wfree", "The free Wigner polytope", FreeFormula(),
                "Page 3: \"The stabilizer Wigner polytope is Wfree := conv{W_σ : σ ∈ Stabₙ} ⊂ R^(4ⁿ).\" The imported pauliSet is the phased one-qubit Pauli group. Wfree(A,P) takes the real convex hull of the image of the subgroup-defined stabilizer set under Wigner(A). image is set image, so the representation includes every free mixture."),
            Definition("COne", "The single-qubit Wigner distance", CFormula(false),
                "Page 3, Definition 3.1 (Wigner distance): \"C(ρ) := min_{W_f ∈ Wfree} ‖W_ρ − W_f‖₁.\" COne uses the paper's four-point frame and actual local stabilizer polytope. COne_min proves attainment and minimality for every qubit matrix."),
            Definition("CTwo", "The two-qubit Wigner distance", CFormula(true),
                "Page 3, Definition 3.1 (Wigner distance): \"C(ρ) := min_{W_f ∈ Wfree} ‖W_ρ − W_f‖₁.\" CTwo uses the sixteen-point frame and actual two-qubit stabilizer polytope, including entangled stabilizers. CTwo_min proves attainment and minimality for every two-qubit matrix."),
            Auxiliary("spectral", "Pauli spectral projectors", SpectralFormula(), DescribeRole.Definition,
                "For a nonidentity Pauli p, spectral(p,epsilon) is the rank-one projector onto its eigenvalue (-1)^epsilon. The identity case is included in the definition."),
            Auxiliary("eigenVector", "Explicit Pauli eigenvectors", EigenVectorFormula(), DescribeRole.Definition,
                "The bracket notation denotes a two-component complex vector. The scalar r is the complex cast of the inverse square root of 2, and t = (-1)^epsilon. The four cases are I: [1,0], X: [r,tr], Y: [r,itr], and Z: [1,0] for epsilon = 0 and [0,1] otherwise."),
            Auxiliary("spectral_stabilizer", "Actual local stabilizer subgroups", SpectralStabilizerFormula(), DescribeRole.Theorem,
                "Each nonidentity Pauli spectral projector is an actual stabilizer state. An injective homomorphism from the multiplicative cyclic group of order two supplies its subgroup. Its nonidentity matrix has trace zero, its eigenvector is normalized, and its group average is exactly the eigenvector's outer product."),
            Auxiliary("spectral_product_stabilizer", "Actual product stabilizer subgroups", ProductStabilizerFormula(), DescribeRole.Theorem,
                "Tensoring two Pauli spectral projectors gives a stabilizer state in the full phased two-qubit Pauli group. The construction uses the product of the two local cyclic subgroups and the tensor eigenvector."),
            MinimumTheorem("COne_min", "The single-qubit Wigner distance attains the source minimum", MinimumFormula(false),
                "For every qubit matrix rho, the source formula C(rho) := min_{W_f ∈ Wfree} ‖W_rho − W_f‖₁ is attained by some f in the compact nonempty free polytope, and COne rho is no larger than every free candidate.") ,
            MinimumTheorem("CTwo_min", "The two-qubit Wigner distance attains the source minimum", MinimumFormula(true),
                "For every two-qubit matrix rho, the same source minimum C(rho) := min_{W_f ∈ Wfree} ‖W_rho − W_f‖₁ is attained by some f in the compact nonempty two-qubit free polytope, and CTwo rho is no larger than every free candidate."))));

    private static DocumentBlock Auxiliary(string name, string title, Formula formula, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("dutta-minimum-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula SpectralFormula() => All("p", V("Pauli"), All("epsilon", Fin(2),
        Equal(Call("spectral", V("p"), V("epsilon")), Smul(new Formula.Fraction(D(1), D(2)),
            Parenthesized(Add(D(1), Smul(Pow(NegativeOne(), Call("val", V("epsilon"))), Call("pauliMatrix", V("p")))))))));

    private static Formula Vec2(Formula a, Formula b) => Seq(OpenBracket, a, Comma, b, CloseBracket);
    private static Formula EigenVectorFormula()
    {
        var epsilon = V("epsilon");
        var r = Call("complexCast", Call("inv", Call("sqrt", D(2))));
        var t = Pow(NegativeOne(), Call("val", epsilon));
        var z = Call("ite", Equal(epsilon, D(0)), Vec2(D(1), D(0)), Vec2(D(0), D(1)));
        return All("epsilon", Fin(2), Conjoin(
            Equal(Call("eigenVector", V("I"), epsilon), Vec2(D(1), D(0))),
            Equal(Call("eigenVector", V("X"), epsilon), Vec2(r, Multiply(t, r))),
            Equal(Call("eigenVector", V("Y"), epsilon), Vec2(r, Multiply(Multiply(V("i"), t), r))),
            Equal(Call("eigenVector", V("Z"), epsilon), z)));
    }
    private static Formula LocalGroup() => Call("Multiplicative", Call("ZMod", D(2)));
    private static Formula SpectralStabilizerFormula()
    {
        var p = V("p"); var epsilon = V("epsilon"); var u = V("U");
        var matrix = (Formula x) => Call("val", At(u, x));
        var psi = Call("eigenVector", p, epsilon);
        var outer = Call("vecMulVec", psi, Call("star", psi));
        var conditions = Conjoin(
            Call("Injective", u),
            All("x", LocalGroup(), Member(matrix(V("x")), V("pauliSet"))),
            All("x", LocalGroup(), Equal(Call("trace", matrix(V("x"))),
                Call("ite", Equal(V("x"), D(1)), D(2), D(0)))),
            Equal(SumOver("j", Fin(2), Pow(Call("norm", At(psi, V("j"))), D(2))), D(1)),
            Equal(Smul(Call("inv", Call("complexCast", Call("card", LocalGroup()))),
                SumOver("x", LocalGroup(), matrix(V("x")))), outer),
            Equal(Call("spectral", p, epsilon), outer));
        var hom = Call("MonoidHom", LocalGroup(), Call("unitaryGroup", Fin(2), ComplexNumbers()));
        return All("p", V("Pauli"), All("epsilon", Fin(2), Imp(
            Rel(p, FormulaRelationOperator.NotEqual, V("I")),
            And(Member(Call("spectral", p, epsilon), Call("Stab", V("pauliSet"))),
                ExistsOne("U", hom, conditions)))));
    }
    private static Formula ProductStabilizerFormula() =>
        All("p", V("Pauli"), All("q", V("Pauli"), All("epsilon", Fin(2), All("delta", Fin(2),
            Imp(Rel(V("p"), FormulaRelationOperator.NotEqual, V("I")),
                Imp(Rel(V("q"), FormulaRelationOperator.NotEqual, V("I")),
                    Member(Tensor(Call("spectral", V("p"), V("epsilon")),
                        Call("spectral", V("q"), V("delta"))), Call("Stab", V("pauliTwo")))))))));

    private static DocumentBlock MinimumTheorem(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(new DocumentBlock.DisplayFormula(SourceMinimum(name == "CTwo_min")), Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula SourceMinimum(bool two)
    {
        var free = Call("Wfree", V(two ? "phasePointTwo" : "phasePoint"),
            V(two ? "pauliTwo" : "pauliSet"));
        var objective = Call("norm", Call("toLp", D(1),
            Subtract(Call(two ? "WignerTwo" : "WignerOne", V("rho")), V("f"))));
        return Equal(Call(two ? "CTwo" : "COne", V("rho")),
            Seq(Min, Underscore, Grp(V("f"), InMacro, free), Sp, objective));
    }

    private static Formula MinimumFormula(bool two)
    {
        var point = two ? Product(Pt(), Pt()) : Pt();
        var value = two ? Call("WignerTwo", V("rho")) : Call("WignerOne", V("rho"));
        var free = two ? Call("Wfree", V("phasePointTwo"), V("pauliTwo")) : Call("Wfree", V("phasePoint"), V("pauliSet"));
        var distance = two ? Call("CTwo", V("rho")) : Call("COne", V("rho"));
        var candidate = (Formula x) => Call("norm", Call("toLp", D(1), Subtract(value, x)));
        var membership = (Formula x) => Member(x, free);
        var body = And(membership(V("f")), And(
            Equal(distance, candidate(V("f"))),
            All("g", Arrow(point, Real()), Imp(membership(V("g")),
                Rel(distance, FormulaRelationOperator.LessThanOrEqual, candidate(V("g")))))));
        return All("rho", two ? TwoQubit() : Qubit(),
            ExistsOne("f", Arrow(point, Real()), body));
    }

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static string NodeId(string name) => name switch
    {
        "PhasePoint" => "dutta-phase-carrier", "phasePoint" => "dutta-phase-operator",
        "phasePointTwo" => "dutta-product-frame", "Wigner" => "dutta-transform",
        "WignerOne" => "dutta-one-transform", "WignerTwo" => "dutta-two-transform",
        "pauliTwo" => "dutta-two-paulis",
        "Stab" => "dutta-stabilizers", "Wfree" => "dutta-free-polytope",
        "COne" => "dutta-one-distance", "CTwo" => "dutta-two-distance",
        "COne_min" => "dutta-one-distance-minimum", "CTwo_min" => "dutta-two-distance-minimum",
        "bloch" => "dutta-bloch", "claimEquatorial" => "dutta-equatorial-claim",
        "claimSelfTensor" => "dutta-self-claim", "resultEquatorial" => "dutta-equatorial-result",
        _ => "dutta-self-result"
    };
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Conjoin(params Formula[] items)
    {
        var result = items[0];
        for (var i = 1; i < items.Length; i++) result = And(result, items[i]);
        return result;
    }
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula ComplexNumbers() => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Pt() => V("PhasePoint");
    private static Formula Qubit() => V("QubitMatrix");
    private static Formula TwoQubit() => V("TwoQubitMatrix");
    private static Formula Mat(Formula i) => Call("Matrix", i, i, ComplexNumbers());
    private static Formula Vector(Formula i) => Arrow(i, ComplexNumbers());
    private static Formula SetOf(Formula t) => Call("Set", Parenthesized(t));
    private static Formula Tensor(Formula a, Formula b) => Call("kronecker", a, b);
    private static Formula At(Formula f, Formula a) => new Formula.Apply(f, [a]);
    private static Formula TrRe(Formula m) => Call("re", Call("trace", m));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula NegativeOne() => Subtract(D(0), D(1));
    private static Formula Pauli(string p) => V(p);
    private static Formula Instance(string cls, Formula i, Formula body) =>
        Seq(OpenBracket, Call(cls, i), CloseBracket, Comma, Sp, body);
    private static Formula FiniteContext(Formula body) => All("iota", V("Type"), All("alpha", V("Type"), Instance("Fintype", V("iota"), body)));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(name), Colon, type), Sp, body);
    private static Formula Member(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Smul(Formula a, Formula b) => Call("smul", a, b);

    private static Formula PhaseFormula()
    {
        var a = V("a");
        var q = Call("val", Call("fst", a));
        var p = Call("val", Call("snd", a));
        var expression = Add(Add(Add(D(1), Smul(Pow(NegativeOne(), p), Call("pauliMatrix", Pauli("X")))),
            Smul(Pow(NegativeOne(), Add(q, p)), Call("pauliMatrix", Pauli("Y")))),
            Smul(Pow(NegativeOne(), q), Call("pauliMatrix", Pauli("Z"))));
        return All("a", Pt(), Equal(Call("phasePoint", a), Smul(new Formula.Fraction(D(1), D(2)), Parenthesized(expression))));
    }
    private static Formula WignerFormula() => FiniteContext(All("A", Arrow(V("alpha"), Mat(V("iota"))),
        All("rho", Mat(V("iota")), All("a", V("alpha"), Equal(At(Call("Wigner", V("A"), V("rho")), V("a")),
            new Formula.Fraction(TrRe(Multiply(V("rho"), At(V("A"), V("a")))), Call("realCast", Call("card", V("iota")))))))));
    private static Formula PhaseSet() => Seq(OpenBrace, D(1), Comma, NegativeOne(), Comma, V("i"), Comma, Subtract(D(0), V("i")), CloseBrace);
    private static Formula PauliFormula(bool two)
    {
        var p = V("P"); var c = V("c");
        Formula word = Call("pauliMatrix", V("p"));
        if (two) word = Tensor(word, Call("pauliMatrix", V("q")));
        Formula body = Equal(p, Smul(c, word));
        if (two) body = ExistsOne("q", V("Pauli"), body);
        body = ExistsOne("p", V("Pauli"), body);
        body = ExistsOne("c", ComplexNumbers(), And(Member(c, PhaseSet()), body));
        return All("P", two ? TwoQubit() : Qubit(), Iff(Member(p, V(two ? "pauliTwo" : "pauliSet")), body));
    }
    private static Formula StabilizerFormula()
    {
        var i = V("iota"); var p = V("P"); var rho = V("rho"); var s = V("S"); var psi = V("psi");
        var matrix = Call("val", Call("val", V("g")));
        var fixedSpace = All("v", Vector(i), Iff(All("g", s, Equal(Call("mulVec", matrix, V("v")), V("v"))),
            ExistsOne("c", ComplexNumbers(), Equal(V("v"), Smul(V("c"), psi)))));
        var conditions = Conjoin(
            All("g", s, Member(matrix, p)),
            Equal(Call("NatCard", s), Call("card", i)),
            All("g", s, All("h", s, Equal(Multiply(V("g"), V("h")), Multiply(V("h"), V("g"))))),
            Equal(SumOver("j", i, Pow(Call("norm", At(psi, V("j"))), D(2))), D(1)),
            fixedSpace,
            Equal(rho, Call("vecMulVec", psi, Call("star", psi))));
        var subgroup = Call("Subgroup", Call("unitaryGroup", i, ComplexNumbers()));
        var body = All("P", SetOf(Mat(i)), All("rho", Mat(i), Iff(Member(rho, Call("Stab", p)),
            ExistsOne("S", subgroup, ExistsOne("psi", Vector(i), conditions)))));
        return All("iota", V("Type"), Instance("Fintype", i, Instance("DecidableEq", i, body)));
    }
    private static Formula FreeFormula() => FiniteContext(Instance("DecidableEq", V("iota"),
        All("A", Arrow(V("alpha"), Mat(V("iota"))), All("P", SetOf(Mat(V("iota"))),
            Equal(Call("Wfree", V("A"), V("P")), Call("convexHull", Real(),
                Call("image", Call("Wigner", V("A")), Call("Stab", V("P")))))))));
    private static Formula CFormula(bool two) => All("rho", two ? TwoQubit() : Qubit(),
        Equal(Call(two ? "CTwo" : "COne", V("rho")), Call("infDist",
            Call("toLp", D(1), Call(two ? "WignerTwo" : "WignerOne", V("rho"))),
            Call("image", Call("toLp", D(1)),
                Call("Wfree", V(two ? "phasePointTwo" : "phasePoint"), V(two ? "pauliTwo" : "pauliSet"))))));
}
