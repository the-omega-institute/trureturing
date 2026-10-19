using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class QubitIncompatibilityRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/torii2025comparing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restricted-state compatibility determines incompatible unbiased qubit pairs.",
        H("Qubit Incompatibility Rigidity"), Blocks(
            Node("effect", "Unbiased effects", "FourQubitParentConstruction.B expands a Bloch vector in the three Pauli matrices. Outcome zero uses that expansion and outcome one uses its negative. One half is a complex scalar.",
                DescribeRole.Definition, All("v", BlochSpace(), All("s", Fin(2),
                    Equal(Call("effect", X("v"), X("s")),
                        Smul(Typed(Fraction(Num(1), Num(2)), Complexes()), Add(
                            Typed(Num(1), X("QubitMatrix")), Smul(
                                Call("ite", Equal(X("s"), Typed(Num(0), Fin(2))),
                                    Typed(Num(1), Complexes()), Typed(Negate(Num(1)), Complexes())),
                                At(Qualified("FourQubitParentConstruction", "B"), X("v"))))))))),
            Node("marginal", "Marginal effects", "The first marginal sums over the second outcome, and the second marginal sums over the first outcome.",
                DescribeRole.Definition, All("G", Parents(), All("i", Fin(2), All("s", Fin(2),
                    Equal(Call("marginal", X("G"), X("i"), X("s")),
                        Call("ite", Equal(X("i"), Typed(Num(0), Fin(2))),
                            SumOver("t", Fin(2), At(X("G"), Pair(X("s"), X("t")))),
                            SumOver("t", Fin(2), At(X("G"), Pair(X("t"), X("s")))))))))),
            Node("SCompatible", "Compatibility on a state set", "ConcealmentKernelNecessityRefutation.IsPOVM requires positive semidefinite effects summing to the identity. States use FiniteStateChannel.DensityState on Fin 2, whose underlying matrices are positive semidefinite with trace one. A joint POVM reproduces both observable distributions on every state in the given set. CStarMatrix.ofMatrix.symm returns the underlying matrix, and bornProbability is the complex trace of the matrix product.",
                DescribeRole.Definition, All("S", StateSets(), All("a", Vectors(),
                    Equivalence(Call("SCompatible", X("S"), X("a")), Ex("G", Parents(), And(
                        At(Qualified("ConcealmentKernelNecessityRefutation", "IsPOVM"), X("G")), All("rho", At(Qualified("FiniteStateChannel", "DensityState"), Fin(2)), Implication(
                            Member(X("rho"), X("S")), All("i", Fin(2), All("s", Fin(2),
                                Equal(Call("bornProbability", At(At(Qualified("Equiv", "symm"), Qualified("CStarMatrix", "ofMatrix")),
                                        Call("val", X("rho"))),
                                    Call("marginal", X("G"), X("i"), X("s"))),
                                    Call("bornProbability", At(At(Qualified("Equiv", "symm"), Qualified("CStarMatrix", "ofMatrix")),
                                        Call("val", X("rho"))),
                                        Call("effect", At(X("a"), X("i")), X("s")))))))))))))),
            Node("Incompatible", "Incompatibility", "No joint POVM reproduces both observables on the set of all density matrices.",
                DescribeRole.Definition, All("a", Vectors(), Equivalence(Call("Incompatible", X("a")),
                    new Formula.Not(Parenthesized(Call("SCompatible",
                        Typed(Qualified("Set", "univ"), StateSets()), X("a"))))))),
            Node("SignedPermutation", "Signs and exchange", "Each vector may be negated independently, and the two observables may be exchanged.",
                DescribeRole.Definition, All("a", Vectors(), All("b", Vectors(),
                    Equivalence(Call("SignedPermutation", X("a"), X("b")),
                        Ex("pi", At(Qualified("Equiv", "Perm"), Fin(2)), Ex("eps", Arrow(Fin(2), Reals()), And(
                            All("i", Fin(2), Or(Equal(At(X("eps"), X("i")), Num(1)),
                                Equal(At(X("eps"), X("i")), Negate(Num(1))))),
                            All("i", Fin(2), Equal(At(X("b"), X("i")),
                                Smul(At(X("eps"), X("i")), At(X("a"), At(X("pi"), X("i"))))))))))))),
            Node("claim", "Rigidity statement", "In §IV.A, Proposition 7 of Torii, Takakura and Imamura states: “Let A_ub = {A^{a_1}_ub, A^{a_2}_ub} and B_ub = {A^{b_1}_ub, A^{b_2}_ub} be pairs of unbiased qubit observables satisfying |a_1|=|a_2|=t, |b_1|=|b_2|=u for some t,u ∈ (1/√2,1]. If A_ub ∼_inc B_ub, then either (b_1,b_2) = (±a_1,±a_2) or (b_1,b_2) = (±a_2,±a_1) holds.” The statement here allows arbitrary individual lengths at most one and assumes that each pair is incompatible.",
                DescribeRole.Definition, Equivalence(X("claim"), Claim()), AssessedProvenance.FromLiterature(Source)),
            Node("result", "Rigidity without equal-length constraints", "In §V, the authors ask: “Future work will also address the generalization of Proposition 7, as it remains an open problem whether the result holds without the constraints of |a_1|=|a_2| and |b_1|=|b_2|.” For incompatible pairs, equality of compatibility on every state set determines the two Bloch vectors up to independent signs and exchange. Central Bloch disks determine a quartic boundary. Equality of these boundaries forces a common plane, and polynomial identities force the coordinate change to be a signed permutation. Conversely, outcome relabelling and exchange preserve compatibility on every state set.",
                DescribeRole.Theorem, X("claim"), AssessedProvenance.FromRepo(Source))
        ), []));

    private static Formula Claim() => All("a", Vectors(), All("b", Vectors(),
        Implication(All("i", Fin(2), LE(Norm(At(X("a"), X("i"))), Num(1))),
        Implication(All("i", Fin(2), LE(Norm(At(X("b"), X("i"))), Num(1))),
        Implication(Call("Incompatible", X("a")), Implication(Call("Incompatible", X("b")),
            Equivalence(All("S", StateSets(), Equivalence(Call("SCompatible", X("S"), X("a")),
                Call("SCompatible", X("S"), X("b")))), Call("SignedPermutation", X("a"), X("b")))))))));
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role,
        Formula formula, AssessedProvenance? provenance = null) => Describe.Lean(
        DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role,
        name == "result" ? new OpenProblemResolutionClaim(
            ProblemSlugRef.Create("torii-takakura-imamura-2025-proposition-7-generalization"),
            ResolutionKind.Proved) : null);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Outcomes() => Seq(Fin(2), Sp, Times, Sp, Fin(2));
    private static Formula Parents() => Arrow(Parenthesized(Outcomes()), X("QubitMatrix"));
    private static Formula BlochSpace() => Call("EuclideanSpace", Reals(), Fin(3));
    private static Formula Vectors() => Arrow(Fin(2), BlochSpace());
    private static Formula StateSets() => Call("Set", At(Qualified("FiniteStateChannel", "DensityState"), Fin(2)));
    private static Formula At(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula All(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Ex(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Smul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Implication(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equivalence(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula SumOver(string v, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(v), domain)), Sp, Parenthesized(body));
}
