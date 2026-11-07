using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class WeylCliffordDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/WeylCliffordDescent.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/andersonweippert2024controlled");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated commutators with a Pauli terminate in the Clifford hierarchy.", H("Termination of Pauli commutators in the Clifford hierarchy"), Blocks(
            Node("pauli-set", "Pauli operators with unit-modulus phase", "pauli", PauliFormula(),
                "Section 2, p. 2: \"The elements form a group and consist of Pauli strings i.e. tensor products of single-qubit Pauli matrices times a U (1) phase (usually restricted to i^k or ±1). The details of this phase are not important here and any of these definitions of CH1 will suffice for our proofs below.\" The complex scalar has norm one, and the Weyl labels range independently over all coordinates.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("clifford-levels", "The finite Clifford hierarchy", "cliffordHierarchy", HierarchyFormula(),
                "Equation (1), p. 1: \"The n-qubit Clifford Hierarchy [1, 7] is recursively defined as CHk ≡ {U |U P U † ⊆ CHk−1 , ∀P ∈ Pn } with the first level (k = 1) defined as CH1 ≡ Pn , the n-qubit Pauli group.\" The formulas use prime-dimensional Weyl operators. Level zero is empty; levels at least two require unitarity.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("matrix-commutator", "A star commutator", "commutator", CommutatorFormula(),
                "The expression is defined for arbitrary square matrices. On unitary matrices it is the multiplicative group commutator.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("hierarchy-termination", "Commutators with a Pauli reach the identity", "hierarchy_terminates", TerminationFormula(),
                "If V is in level k and Q is Pauli, k plus one repeated commutators give the identity. Right multiplication by a Pauli preserves each level, a Pauli commutator is scalar, and the next commutator of that scalar is the identity.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula C() => Seq(Mathbb, Grp(V("C")));
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula head, params Formula[] args)
        {
            var items = new List<Formula>();
            for (var i = 0; i < args.Length; i += 1)
            {
                if (i > 0) { items.Add(Comma); items.Add(Sp); }
                items.Add(args[i]);
            }
            return Seq(head, Parenthesized(Seq([.. items])));
        }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Rightarrow, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Bracket(Formula type) => Seq(OpenBracket, type, CloseBracket);
    private static Formula Instance(Formula type, Formula body) => Seq(Bracket(type), Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) => Seq(LambdaLower, Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body);
    private static Formula Const(Formula type, Formula body) => Seq(LambdaLower, Sp, Underscore, Colon, Sp, type, Sp, Mapsto, Sp, body);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Zm(Formula p) => Call("ZMod", p);
    private static Formula Basis(Formula p, Formula n) => Arrow(Fin(n), Zm(p));
    private static Formula Mat(Formula p, Formula n) => Call("Matrix", Basis(p, n), Basis(p, n), C());
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Unitary(Formula p, Formula n) => App(Q("Matrix", "unitaryGroup"), Basis(p, n), C());
    private static Formula StarOf(Formula a) => Call("star", a);
    private static Formula Norm(Formula a) => Seq(Vert, Sp, a, Sp, Vert);
    private static Formula Ctx(Formula body) => All("p", N(), Instance(Call("NeZero", V("p")), All("n", N(), body)));
    private static Formula SetOf(string name, Formula type, Formula body) => Seq(OpenBrace, V(name), Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
            Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
                StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula PauliFormula()
    {
        Formula p = V("p"), n = V("n"), a = V("a"), b = V("b"), c = V("c"), matrix = V("A");
        Formula label = Arrow(Fin(n), Zm(p));
        Formula predicate = Ex("c", C(), Ex("a", label, Ex("b", label,
            And(Eqn(Norm(c), D(1)), Eqn(matrix, App(Q("SMul", "smul"), c, App(Q("ProductPrefixRigidity", "productMap"), Const(Fin(n), Zm(p)), Lam("k", Fin(n), Call("displacement", p, App(a, V("k")), App(b, V("k")))))))))));
        return Disp(Ctx(Eqn(Call("pauli", p, n), SetOf("A", Mat(p, n), predicate))));
    }
    private static Formula HierarchyFormula()
    {
        Formula p = V("p"), n = V("n"), k = V("k"), v = V("V"), q = V("P");
        Formula conjugate = Mul(Mul(v, q), StarOf(v));
        Formula predicate = And(Member(v, Unitary(p, n)), All("P", Mat(p, n),
            Imp(Member(q, Call("pauli", p, n)), Member(conjugate, Call("cliffordHierarchy", p, n, Add(k, D(1)))))));
        return Disp(new Formula.Aligned([
            Ctx(Eqn(Call("cliffordHierarchy", p, n, D(0)), Emptyset)),
            Ctx(Eqn(Call("cliffordHierarchy", p, n, D(1)), Call("pauli", p, n))),
            Ctx(All("k", N(), Eqn(Call("cliffordHierarchy", p, n, Add(k, D(2))), SetOf("V", Mat(p, n), predicate))))]));
    }
    private static Formula CommutatorFormula()
    {
        Formula p = V("p"), n = V("n"), v = V("V"), q = V("Q");
        return Disp(Ctx(All("V", Mat(p, n), All("Q", Mat(p, n),
            Eqn(Call("commutator", v, q), Mul(Mul(Mul(v, q), StarOf(v)), StarOf(q)))))));
    }
    private static Formula TerminationFormula()
    {
        Formula p = V("p"), n = V("n"), v = V("V"), q = V("Q"), k = V("k");
        return Disp(Ctx(All("V", Mat(p, n), All("Q", Mat(p, n), All("k", N(),
            Imp(Member(v, Call("cliffordHierarchy", p, n, k)), Imp(Member(q, Call("pauli", p, n)),
                Eqn(App(Q("Function", "iterate"), Lam("A", Mat(p, n), Call("commutator", V("A"), q)), Add(k, D(1)), v), D(1)))))))));
    }
}
