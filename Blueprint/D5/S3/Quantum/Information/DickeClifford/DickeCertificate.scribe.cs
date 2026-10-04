using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.DickeClifford;

internal sealed class DickeCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/DickeClifford/DickeCertificate.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every nontrivial Dicke state with more than two qubits, all Pauli expectations have binomial common denominator, and at most two Hermitian Pauli words have unit-modulus expectation, or at most four on the balanced layer.",
        H("A Pauli certificate for Dicke states"), Blocks(
            Node("pauliMatrices", "Pauli matrices with phases", PauliMatrices(),
                "The existing n-qubit Pauli subgroup is represented in the matrix algebra through the value map on units. Its matrices are i^c times a tensor product of I, X, Y and Z, with c in Fin 4. The reused State(n) is (Fin n -> Fin 2) -> C, and Operator(n) is the square complex matrix algebra indexed by those bitstrings."),
            Node("Clifford", "Clifford normalizer", Clifford(),
                "Page 11, Definition A.1: \"The n-qubit Clifford group is defined as the normalizer of the n-qubit Pauli group (P_n) in SU(2^n), C_n := N_{SU(2^n)}(P_n): C_n := {U ∈ SU(2^n) : U P U† ∈ P_n, ∀P ∈ P_n}.\" The carrier Fin n -> Fin 2 has cardinality 2^n. Conjugate transpose encodes the dagger, and specialUnitaryGroup requires unitarity and determinant one."),
            Node("dicke", "Normalized Dicke vector", Dicke(),
                "Page 16, Appendix F.2: \"Dicke states are defined as [46, 47] |D^n_k⟩ = (1/√(n choose k)) Σ_{w(x)=k} |x⟩, where w(x) is the Hamming weight of the bitstring x.\" The imported Mathlib hammingNorm counts the nonzero bits, which is the Hamming weight on Fin 2. Qubits are indexed from zero by Fin n. In the computational basis this has amplitude the complex cast of the reciprocal real square root of n.choose k on weight k, and zero elsewhere."),
            Node("productVector", "Total product vector", Product(),
                "The amplitude of the total product at a bitstring x is the product of the local amplitudes phi(j)(x(j))."),
            Node("LocalNormalized", "Local normalization", Normalized(),
                "Local normalization means that the sum of the two squared complex norms is one. This is the unit-norm condition on C^2."),
            Node("expectation", "Pauli expectation", Expectation(),
                "The complex expectation is the dot product of the conjugated state and the matrix acting on the state. star acts pointwise on state coefficients, and mulVec is matrix-vector multiplication."),
            Node("pauliUnitCount", "Number of unit-modulus expectations", Count(),
                "Count each Hermitian Pauli word in {I,X,Y,Z}^n once, including the identity and excluding scalar phase copies. The count selects exactly the expectations whose complex norm is one."),
            Node("HasIntegerPauliDenominator", "Integral scaled expectations", Denominator(),
                "All expectations, multiplied by the natural number B cast into C, are integer casts. This asserts that B is a common denominator; it makes no least-denominator assertion."),
            Describe.Lean(DescribeId.Create("dicke-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/DickeClifford/DickeCertificate.dicke_certificate"),
                H("Dicke denominator and unit count"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(DickeFormula.Source), Blocks(Paragraph(Text(
                    "A Pauli word acts by a bit flip and a phase. A unit-modulus expectation means that the normalized state is an eigenvector. Exchanging one selected and one unselected bit in the weight-k layer forces every flip bit to agree and every sign bit to agree. Therefore only the identity and the all-Z word can occur, with the all-X and all-Y words also possible when n = 2k. Counting this list gives the stated upper bounds, without claiming equality. The unnormalized weight-layer indicator has squared norm n.choose k. Its expectations are Gaussian integers; Hermiticity makes them real integers, so multiplication of a normalized expectation by n.choose k is an integer. Both invariants concern the same Dicke vector."))), DescribeRole.Theorem)), []));

    private static Formula Statement()
    {
        var n = F.Id("n"); var k = F.Id("k");
        return DickeFormula.All("n", DickeFormula.Naturals, DickeFormula.All("k", DickeFormula.Naturals,
            DickeFormula.Implies(DickeFormula.Hypotheses(n, k), DickeFormula.And(
                Call("HasIntegerPauliDenominator", Call("choose", n, k), Call("dicke", n, k)),
                DickeFormula.CountBound(n, k)))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("dicke-model-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            name is "pauliUnitCount" or "HasIntegerPauliDenominator"
                ? AssessedProvenance.FromRepo(DickeFormula.Source)
                : AssessedProvenance.FromLiterature(DickeFormula.Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula PauliMatrices() => DickeFormula.All("n", DickeFormula.Naturals,
        Equal(Call("pauliMatrices", F.Id("n")), new Formula.SetBuilder(
            Call("val", F.Id("u")), F.Id("u"), Call("pauliGroup", F.Id("n")))));

    private static Formula Clifford()
    {
        var n = F.Id("n"); var u = F.Id("U"); var p = F.Id("P");
        return DickeFormula.All("n", DickeFormula.Naturals,
            DickeFormula.All("U", Call("Operator", n), DickeFormula.Iff(
                DickeFormula.Member(u, Call("Clifford", n)), DickeFormula.And(
                    DickeFormula.Member(u, Call("specialUnitaryGroup", DickeFormula.Bits(n), DickeFormula.Complexes)),
                    DickeFormula.All("P", Call("Operator", n), DickeFormula.Implies(
                        DickeFormula.Member(p, Call("pauliMatrices", n)),
                        DickeFormula.Member(Multiply(Multiply(u, p), Call("conjTranspose", u)),
                            Call("pauliMatrices", n))))))));
    }

    private static Formula Dicke()
    {
        var n = F.Id("n"); var k = F.Id("k"); var x = F.Id("x");
        return DickeFormula.All("n", DickeFormula.Naturals, DickeFormula.All("k", DickeFormula.Naturals,
            DickeFormula.All("x", DickeFormula.Bits(n), Equal(Call("dicke", n, k, x),
                Call("ite", Equal(Call("hammingNorm", x), k),
                    Call("asComplex", Call("inv", Call("sqrt", Call("asReal", Call("choose", n, k))))), D(0))))));
    }

    private static Formula Product()
    {
        var n = F.Id("n"); var phi = F.Id("phi"); var x = F.Id("x"); var j = F.Id("j");
        return DickeFormula.All("n", DickeFormula.Naturals,
            DickeFormula.All("phi", DickeFormula.Locals(n), DickeFormula.All("x", DickeFormula.Bits(n),
                Equal(Call("productVector", phi, x),
                    DickeFormula.Product("j", Call("Fin", n), new Formula.Apply(F.Id("phi"), [j, new Formula.Apply(F.Id("x"), [j])]))))));
    }

    private static Formula Normalized() => DickeFormula.All("phi", DickeFormula.Qubit,
        DickeFormula.Iff(Call("LocalNormalized", F.Id("phi")),
            Equal(DickeFormula.Sum("b", Call("Fin", D(2)), Call("normSq", new Formula.Apply(F.Id("phi"), [F.Id("b")]))), D(1))));

    private static Formula Expectation()
    {
        var n = F.Id("n"); var psi = F.Id("psi"); var p = F.Id("P");
        return DickeFormula.All("n", DickeFormula.Naturals,
            DickeFormula.All("psi", Call("State", n), DickeFormula.All("P", Call("Operator", n),
                Equal(Call("expectation", psi, p), Call("dotProduct", Call("star", psi), Call("mulVec", p, psi))))));
    }

    private static Formula Count()
    {
        var n = F.Id("n"); var psi = F.Id("psi"); var p = F.Id("p");
        var selected = Seq(OpenBrace, p, Colon, DickeFormula.Words(n), Sp, Mid, Sp,
            Equal(new Formula.Norm(Call("expectation", psi, Call("wordOp", p))), D(1)), CloseBrace);
        return DickeFormula.All("n", DickeFormula.Naturals, DickeFormula.All("psi", Call("State", n),
            Equal(Call("pauliUnitCount", psi), Call("card", selected))));
    }

    private static Formula Denominator()
    {
        var n = F.Id("n"); var b = F.Id("B"); var psi = F.Id("psi"); var p = F.Id("p");
        return DickeFormula.All("n", DickeFormula.Naturals, DickeFormula.All("B", DickeFormula.Naturals,
            DickeFormula.All("psi", Call("State", n), DickeFormula.Iff(Call("HasIntegerPauliDenominator", b, psi),
                DickeFormula.All("p", DickeFormula.Words(n), DickeFormula.Some("a", DickeFormula.Integers,
                    Equal(Multiply(Call("asComplex", b), Call("expectation", psi, Call("wordOp", p))),
                        Call("asComplex", F.Id("a")))))))));
    }
}

internal static class DickeFormula
{
    internal static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/bordakuhlmannrincon2026magic");
    internal static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    internal static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));
    internal static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    internal static Formula Qubit => new Formula.TypeArrow(Call("Fin", D(2)), Complexes);
    internal static Formula Bits(Formula n) => new Formula.TypeArrow(Call("Fin", n), Call("Fin", D(2)));
    internal static Formula Locals(Formula n) => new Formula.TypeArrow(Call("Fin", n), Parenthesized(Qubit));
    internal static Formula Words(Formula n) => new Formula.TypeArrow(Call("Fin", n), F.Id("Pauli"));
    internal static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    internal static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    internal static Formula Some(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    internal static Formula And(Formula left, Formula right) => new Formula.Logic(
        Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    internal static Formula Implies(Formula left, Formula right) => new Formula.Logic(
        Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    internal static Formula Iff(Formula left, Formula right) => new Formula.Logic(
        left, FormulaLogicOperator.Iff, Parenthesized(right));
    internal static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    internal static Formula Sum(string name, Formula type, Formula body) => Seq(
        new Formula.Subscript(FormulaDsl.Sum, Seq(F.Id(name), Colon, type)), Parenthesized(body));
    internal static Formula Product(string name, Formula type, Formula body) => Seq(
        new Formula.Subscript(Prod, Seq(F.Id(name), Colon, type)), Parenthesized(body));
    internal static Formula Hypotheses(Formula n, Formula k) => And(
        new Formula.Relation(D(2), FormulaRelationOperator.LessThan, n), And(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, k),
            new Formula.Relation(k, FormulaRelationOperator.LessThan, n)));
    internal static Formula CountBound(Formula n, Formula k) => new Formula.Relation(
        Call("pauliUnitCount", Call("dicke", n, k)), FormulaRelationOperator.LessThanOrEqual,
        Call("ite", Equal(n, Multiply(D(2), k)), D(4), D(2)));
    internal static Formula ClaimBody()
    {
        var n = F.Id("n"); var k = F.Id("k"); var u = F.Id("U"); var phi = F.Id("phi");
        return All("n", Naturals, All("k", Naturals, Implies(Hypotheses(n, k),
            All("U", Call("Operator", n), Implies(Member(u, Call("Clifford", n)),
                All("phi", Locals(n), Implies(All("j", Call("Fin", n),
                    Call("LocalNormalized", new Formula.Apply(F.Id("phi"), [F.Id("j")]))),
                    NotEqual(Call("mulVec", u, Call("dicke", n, k)), Call("productVector", phi)))))))));
    }
}
