using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class BinaryStabilizerLocalInequivalenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/descamps2024stabilizer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-qubit state v = sum over j of (|e_j> - |complement of e_j>) is, up to a factor, the only common +1 eigenvector of four tensor products of binary operators, yet no Pauli stabilizer state is locally equivalent to it. This refutes the conjecture of E. Descamps and B. Dakic (arXiv:2309.09815) that every state stabilized by binary operators and the identity is locally equivalent to a standard stabilizer state.",
        H("A state stabilized by binary operators that is not locally a stabilizer state"),
        Blocks(
            Node("binary-op", "Binary operators", BinaryOpFormula(),
                "The binary operator A(theta, phi) = cos(theta) Z + sin(theta) (cos(phi) X + sin(phi) Y), a Hermitian involution whose Bloch vector is the unit vector with polar angle theta and azimuth phi; X, Y and Z are the Pauli matrices.",
                "binaryOp", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("binary-set", "The binary stabilizing set", BinarySetFormula(),
                "The stabilizing set of the conjecture: all binary operators A(theta, phi) together with the identity.",
                "binarySet", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pauli-set", "The Pauli stabilizing set", PauliSetFormula(),
                "The stabilizing set of the standard stabilizer formalism: the Pauli matrices 1, X, Y, Z multiplied by a phase in {1, -1, i, -i}.",
                "pauliSet", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("stabilized", "Stabilized states", StabilizedFormula(),
                "A nonzero state psi of N qubits is stabilized by a stabilizing set S when finitely many operators O_1, ..., O_k, each a tensor product of N elements of S, have psi as their unique common +1 eigenvector up to a complex factor. No commutativity is required.",
                "StabilizedBy", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("local", "Local equivalence", LocalFormula(),
                "Two N-qubit states are locally equivalent when psi = (U_1 x ... x U_N) phi for single-qubit unitaries U_1, ..., U_N.",
                "LocallyEquivalent", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "The conjecture of the paper: for every number N of qubits, every state stabilized by the binary operators and the identity is locally equivalent to a state stabilized by the Pauli set.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A six-qubit counterexample", Disp(new Formula.Not(F.Id("claim"))),
                "Let v be the vector with coefficient 1 on the six labels of Hamming weight one, -1 on the six labels of weight five and 0 elsewhere, and take O_1 = (-X) x X x X x X x X x X, O_2 = (-Z) x Z x Z x Z x Z x Z, O_3 = H x ... x H and O_4 = K x ... x K with H = (X + Z)/sqrt(2) and K = (X + Y)/sqrt(2), all tensor products of binary operators. The diagonal operator O_2 forces the coefficients of even weight to vanish, O_1 makes the coefficients of complementary labels opposite, O_4 then forces the weight-three coefficients to vanish, and O_3 evaluated on six weight-three labels forces the six weight-one coefficients to be equal; conversely all four fix v, so v is stabilized. For a state phi stabilized by phased Pauli words, every Pauli word P either anticommutes with some stabilizer T, and then <phi, P phi> = <T phi, P T phi> = -<phi, P phi> = 0, or commutes with all of them, and then P phi is again a common +1 eigenvector, so P phi = c phi with c = 1 or c = -1. Hence the pair purity, the sum over the sixteen words g x h x 1 x 1 x 1 x 1 of |<phi, (g x h x 1 x 1 x 1 x 1) phi>|^2, is an integer multiple of |phi|^4. The pair purity equals 4 times the squared Frobenius norm of the reduced state of qubits 1 and 2, which local unitaries conjugate by a unitary, so it is invariant under local equivalence, and so is |phi|. For v the pair purity is 192 while |v|^4 = 144, and 192 is not an integer multiple of 144.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("descamps-2024-binary-stabilizer-local-equivalence"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("binstab-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula AllOf(Formula variables, Formula body) =>
        Seq(Forall, Sp, variables, Comma, Sp, body);
    private static Formula SomeOf(Formula variables, Formula body) =>
        Seq(Exists, Sp, variables, Comma, Sp, body);
    private static Formula Pauli(Formula letter) => Seq(Mathrm, Grp(letter));
    private static Formula Scaled(Formula scalar, Formula matrix) =>
        new Formula.Binary(scalar, FormulaBinaryOperator.Multiply, matrix);
    private static Formula Plus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula BinaryOpFormula()
    {
        Formula cosT = Call(F.Id("cos"), Theta), sinT = Call(F.Id("sin"), Theta);
        Formula cosP = Call(F.Id("cos"), Varphi), sinP = Call(F.Id("sin"), Varphi);
        Formula inner = Parenthesized(Plus(Scaled(cosP, Pauli(F.Id("X"))), Scaled(sinP, Pauli(F.Id("Y")))));
        Formula body = Plus(Scaled(cosT, Pauli(F.Id("Z"))), Scaled(sinT, inner));
        return Disp(Equal(Call(F.Id("binaryOp"), Theta, Varphi), body));
    }

    private static Formula BinarySetFormula()
    {
        Formula a = F.Id("A");
        Formula body = Or(SomeOf(Seq(Theta, Sp, Varphi), Equal(a, Call(F.Id("binaryOp"), Theta, Varphi))),
            Equal(a, D(1)));
        return Disp(Iff(Member(a, Named(F.Id("binarySet"))), body));
    }

    private static Formula PauliSetFormula()
    {
        Formula a = F.Id("A"), c = F.Id("c"), p = F.Id("p");
        Formula phases = Seq(OpenBrace, D(1), Comma, Sp, new Formula.Negate(D(1)), Comma, Sp,
            F.Id("i"), Comma, Sp, new Formula.Negate(F.Id("i")), CloseBrace);
        Formula body = Seq(Exists, Sp, c, Sp, InMacro, Sp, phases, Comma, Sp,
            SomeOf(p, Equal(a, Scaled(c, Call(F.Id("pauliMatrix"), p)))));
        return Disp(Iff(Member(a, Named(F.Id("pauliSet"))), body));
    }

    private static Formula StabilizedFormula()
    {
        Formula s = F.Id("S"), psi = Psi, w = F.Id("w"), o = F.Id("O"), a = F.Id("a"), i = F.Id("i"),
            c = F.Id("c"), k = F.Id("k");
        Formula fixedAll = AllOf(a, Equal(Seq(Call(F.Id("tensorOp"), new Formula.Apply(o, [a])), Sp, w), w));
        Formula unique = AllOf(w, Iff(Parenthesized(fixedAll), SomeOf(c, Equal(w, Scaled(c, psi)))));
        Formula members = AllOf(Seq(a, Sp, i), Member(new Formula.Apply(o, [a, i]), s));
        Formula body = And(Rel(psi, FormulaRelationOperator.NotEqual, D(0)),
            SomeOf(Seq(k, Sp, o), And(members, unique)));
        return Disp(Iff(Call(F.Id("StabilizedBy"), s, psi), body));
    }

    private static Formula LocalFormula()
    {
        Formula psi = Psi, phi = Phi, u = F.Id("U"), i = F.Id("i");
        Formula unitary = AllOf(i, Member(new Formula.Apply(u, [i]), Call(F.Id("U"), D(2))));
        Formula body = SomeOf(u, And(unitary, Equal(psi, Seq(Call(F.Id("tensorOp"), u), Sp, phi))));
        return Disp(Iff(Call(F.Id("LocallyEquivalent"), psi, phi), body));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("N"), psi = Psi, phi = Phi;
        Formula conclusion = SomeOf(phi, And(Call(F.Id("StabilizedBy"), Named(F.Id("pauliSet")), phi),
            Call(F.Id("LocallyEquivalent"), psi, phi)));
        Formula body = AllOf(Seq(n, Sp, psi),
            Implies(Call(F.Id("StabilizedBy"), Named(F.Id("binarySet")), psi), conclusion));
        return Disp(Iff(F.Id("claim"), body));
    }
}
