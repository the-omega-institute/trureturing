using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class FiniteFockBeamSplitterNonExtremalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/vanherstraeten2025extremewigner");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-Fock beam-splitter states need not be extreme Wigner-positive states.",
        H("Finite-Fock beam-splitter non-extremality"),
        Blocks(
            Paragraph(Text("Fock cutoff K is represented by Matrix (Fin (K+1)) (Fin (K+1)) Complex. Real coefficients are explicitly mapped by Complex.ofReal; natural coefficients use Nat.cast into Real. The complex order is Mathlib ComplexOrder: a complex value is non-negative precisely when its imaginary part is zero and its real part is non-negative. Nat.sub denotes truncated natural subtraction. Finite indices are sent to their natural values by val. Scalar multiplication uses the Lean scalar action. Proof arguments to beamSplitter are omitted; its transmissivity is one half.")),
            Node("genLaguerre", All("k", Nat(), All("m", Nat(), All("x", Real(),
                Eqn(Call("genLaguerre", Id("k"), Id("m"), Id("x")),
                    SumRange("i", Add(Id("m"), D(1)),
                        Div(Mul(Mul(Pow(Neg(D(1)), Id("i")),
                            RealCast(Call("Nat.choose", Add(Id("m"), Id("k")), Call("Nat.sub", Id("m"), Id("i"))))),
                            Pow(Id("x"), Id("i"))), RealCast(Call("Nat.factorial", Id("i"))))))))),
                "The generalized Laguerre polynomial uses the explicit finite sum with real argument x and natural indices k and m.", AssessedProvenance.FromLiterature(Source)),
            Node("wignerFock", All("m", Nat(), All("n", Nat(), All("alpha", Complex(),
                Eqn(Call("wignerFock", Id("m"), Id("n"), Id("alpha")),
                    Call("ite", Leqn(Id("m"), Id("n")),
                        FockUpper(Id("m"), Id("n"), Id("alpha")),
                        Call("starRingEnd", Complex(), FockUpper(Id("n"), Id("m"), Id("alpha")))))))),
                "Appendix A.1, page 18, equation (48), gives the Fock transition Wigner function. Its continuation is stated verbatim: “for m≤n, otherwise use the relation W|n⟩⟨m|=W*|m⟩⟨n|.” The displayed formula includes the real prefactor, complex power, Laguerre polynomial and Gaussian envelope; the reverse branch is complex conjugation.", AssessedProvenance.FromLiterature(Source)),
            Node("wigner", All("K", Nat(), All("A", MatrixType(Id("K")), All("alpha", Complex(),
                Eqn(Call("wigner", Id("A"), Id("alpha")),
                    FiniteSum("m", Fin(Add(Id("K"), D(1))), FiniteSum("n", Fin(Add(Id("K"), D(1))),
                        Mul(At(Id("A"), Id("m"), Id("n")), Call("wignerFock", Call("val", Id("m")), Call("val", Id("n")), Id("alpha"))))))))),
                "Page 6, Section 3.1, equation (16): “Consider a quasi-state Â∈𝒜ⁿ, with Fock matrix elements Aₖℓ=⟨k|Â|ℓ⟩. The Wigner function of Â is here expressed as:” The displayed expansion retains every matrix entry, including off-diagonal entries, and includes both endpoints of the Fock cutoff.", AssessedProvenance.FromLiterature(Source)),
            Node("WPS", All("K", Nat(), Eqn(Call("WPS", Id("K")),
                SetOf("A", MatrixType(Id("K")), And(Call("Matrix.PosSemidef", Id("A")),
                    And(Eqn(Call("Matrix.trace", Id("A")), D(1)),
                        All("alpha", Complex(), Leqn(D(0), Call("wigner", Id("A"), Id("alpha"))))))))),
                "Page 1, the introduction describes WPS as “quantum states with non-negative Wigner function”. Page 3, Section 2 specifies: “We denote by 𝒟⊂ℬ₁ the set of Hermitian positive semi-definite (PSD) operators of unit trace and refer to operators in 𝒟 as states.” Matrix.PosSemidef includes Hermitian symmetry. The finite-matrix set implements these conditions without an additional restriction on phase-space points.", AssessedProvenance.FromLiterature(Source)),
            Node("IsExtremeWPS", All("K", Nat(), All("sigma", MatrixType(Id("K")),
                Eqn(Call("IsExtremeWPS", Id("K"), Id("sigma")),
                    And(Member(Id("sigma"), Call("WPS", Id("K"))),
                        All("x", MatrixType(Id("K")), Imp(Member(Id("x"), Call("WPS", Id("K"))),
                            All("y", MatrixType(Id("K")), Imp(Member(Id("y"), Call("WPS", Id("K"))),
                                Imp(Eqn(Id("sigma"), Smul(Div(D(1), D(2)), Add(Id("x"), Id("y")))),
                                    And(Eqn(Id("x"), Id("sigma")), Eqn(Id("y"), Id("sigma")))))))))))),
                "Page 4, Definition 2: “Given a convex set 𝒞, the point a∈𝒞 is an extreme point of 𝒞 if and only if ∀x,y∈𝒞:a=½(x+y)⇔x=y=a.” Membership and the forward midpoint implication are explicit. The reverse implication is automatic when both endpoints equal sigma.", AssessedProvenance.FromLiterature(Source)),
            Node("bsState", BeamStateFormula(),
                "Page 4, Definition 1: “A beam-splitter state σ̂ is the single-mode output of a balanced beam-splitter acting on a separable state ρ̂ₛₑₚ, i.e. σ̂=Tr₂[Û₁/₂ ρ̂ₛₑₚ Û†₁/₂].” Here the separable input is a product of finite pure vectors. The second-mode sum is a tsum over all natural occupations. The repository rotation differs from the paper's by second-mode parity before and after the rotation. Output parity disappears under the partial trace; input parity permutes the finite-Fock pure states and fixes the even-supported inputs used below. Thus the universal question and the counterexample agree with the paper's convention.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", Eqn(Id("claim"), All("N", Nat(), All("psi", VectorType(Id("N")), All("phi", VectorType(Id("N")),
                Imp(Eqn(FiniteSum("i", Fin(Add(Id("N"), D(1))), Pow(new Formula.Norm(At(Id("psi"), Id("i"))), D(2))), D(1)),
                    Imp(Eqn(FiniteSum("i", Fin(Add(Id("N"), D(1))), Pow(new Formula.Norm(At(Id("phi"), Id("i"))), D(2))), D(1)),
                        Call("IsExtremeWPS", Mul(D(2), Id("N")), Call("bsState", Id("psi"), Id("phi"))))))))),
                "Page 15, Section 6: “This leads us to formulate the following open problem: for any two Fock-bounded pure states |ψ⟩,|φ⟩ is the beamsplitter state σ̂(ψ,φ) an extreme WPS?” N is any natural cutoff; psi and phi are arbitrary complex vectors on Fin (N+1), each with squared norm sum one. The output cutoff is 2*N. A midpoint decomposition in this finite WPS set also disproves extremality in the full WPS set.", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("finitefock-bs-nonextremality-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Refutation"), StatementSource.FromAuthor(Disp(new Formula.Not(Id("claim")))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every positive real a, the inputs (|0>+a|2>)/sqrt(1+a^2) and (|0>-a|2>)/sqrt(1+a^2) give a non-extreme state supported on levels zero through four. After the positive Gaussian factor is removed, the output Wigner polynomial splits as the square of a real radial polynomial plus 32*a^2*Re(alpha)^2*Im(alpha)^2. A perturbation carries just the second square. Subtracting its trace multiple of the output produces a nonzero traceless direction; sufficiently small displacements in both signs remain positive semidefinite and Wigner-positive. Their midpoint is the output state, and the level-four diagonal entry separates the positive endpoint from it. The family at a=1/2 refutes the universal claim. The paper's extremality theorem for two Fock-state inputs and its Vertigo-map results remain compatible with this conclusion."))), DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string name, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("finitefock-bs-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(name), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Qualified(string name)
    {
        var parts = name.Split('.');
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Seq(Operatorname, Grp(Id(part))));
        }
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Qualified(name), [.. args]);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Neg(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Nat() => Seq(Mathbb, Grp(Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(Id("C")));
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula ComplexCast(Formula value) => Call("Complex.ofReal", value);
    private static Formula RealCast(Formula value) => Call("Nat.cast", value);
    private static Formula MatrixType(Formula k) => Call("Matrix", Fin(Add(k, D(1))), Fin(Add(k, D(1))), Complex());
    private static Formula VectorType(Formula n) => Seq(Fin(Add(n, D(1))), Sp, To, Sp, Complex());
    private static Formula FiniteSum(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Id(name), Colon, type), Parenthesized(body));
    private static Formula SumRange(string name, Formula bound, Formula body) =>
        Seq(Sum, Underscore, Grp(Id(name), Colon, Nat(), Comma, Id(name), Sp, InMacro, Sp, Call("Finset.range", bound)), Parenthesized(body));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, Id(name), Colon, type, Mid, Sp, body, CloseBrace);
    private static Formula FockUpper(Formula m, Formula n, Formula alpha)
    {
        var prefactor = Mul(Mul(Div(D(2), Qualified("Real.pi")), Pow(Neg(D(1)), m)),
            Call("Real.sqrt", Div(RealCast(Call("Nat.factorial", m)), RealCast(Call("Nat.factorial", n)))));
        var norm = new Formula.Norm(alpha);
        return Mul(Mul(Mul(ComplexCast(prefactor), Pow(Mul(D(2), alpha), Call("Nat.sub", n, m))),
            ComplexCast(Call("genLaguerre", Call("Nat.sub", n, m), m, Mul(D(4), Pow(norm, D(2)))))),
            ComplexCast(Call("Real.exp", Mul(Neg(D(2)), Pow(norm, D(2))))));
    }
    private static Formula BeamStateFormula()
    {
        var n = Id("N"); var psi = Id("psi"); var phi = Id("phi");
        var j = Id("j"); var k = Id("k"); var v = Id("Psi");
        var input = FiniteSum("j", Fin(Add(n, D(1))), FiniteSum("k", Fin(Add(n, D(1))),
            Smul(Mul(At(psi, j), At(phi, k)), Call("fockPair", Call("val", j), Call("val", k)))));
        var output = Call("beamSplitter", Div(D(1), D(2)), input);
        var partialTrace = All("m", Fin(Add(Mul(D(2), n), D(1))), All("mp", Fin(Add(Mul(D(2), n), D(1))),
            Eqn(At(Call("bsState", psi, phi), Id("m"), Id("mp")),
                Call("tsum", Seq(Parenthesized(Seq(Id("ell"), Colon, Nat())), Mapsto,
                    Mul(At(At(v, Id("ell")), Call("val", Id("m"))),
                        Call("starRingEnd", Complex(), At(At(v, Id("ell")), Call("val", Id("mp"))))))))));
        return All("N", Nat(), All("psi", VectorType(n), All("phi", VectorType(n),
            Seq(Qualified("let"), Sp, v, Sp, Eq, Sp, output, Semi, Sp, partialTrace))));
    }
}
