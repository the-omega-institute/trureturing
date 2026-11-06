using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class AndersonWeippertQuditControlledOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/AndersonWeippertQuditControlledOrder.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/andersonweippert2024controlled");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A controlled qudit gate in the Clifford hierarchy has prime-power target order.", H("Controlled qudit gates have prime-power target order"), Blocks(
            Node("controlled-gate", "Control in computational block one", "controlled", ControlledFormula(),
                "Section 1.1, p. 2: \"We will write C(U) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U where the control is on the left side of the tensor product.\". In prime dimension p, the matrix has U in control block one and the identity in every other block. Coordinate zero is the control; Fin.tail gives the n target coordinates.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("controlled-order-claim", "The controlled-qudit order conjecture", "claim", ClaimFormula(),
                "Section 4, p. 7: \"It is tempting to conjecture for the qudit case that C(U) is in the Clifford Hierarchy only if U is order d^m where d is the local qudit dimension and m is a non-negative integer. We leave this as an open problem.\" Here d is the prime p, basis indices are functions from Fin n to ZMod p, and n ranges over all natural numbers, including zero. The phase group of the Pauli operators is the unit circle. The primality hypothesis supplies NeZero p. The existential hierarchy index is finite, and orderOf is the exact multiplicative matrix order.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("controlled-order-result", "The exact target order is a power of the local prime", "result", Disp(ClaimBody()),
                "Repeated commutators with the control shift reach the identity. On the controlled blocks, each commutator takes a cyclic difference of the integer power exponents. Their positive content is a power of p, and the exact order of U divides that content. Thus the conclusion includes the global phase. The converse and the least hierarchy level are not asserted.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

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
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Rightarrow, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Zm(Formula p) => Call("ZMod", p);
    private static Formula Basis(Formula p, Formula n) => Arrow(Fin(n), Zm(p));
    private static Formula Mat(Formula p, Formula n) => Call("Matrix", Basis(p, n), Basis(p, n), C());
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Unitary(Formula p, Formula n) => App(Q("Matrix", "unitaryGroup"), Basis(p, n), C());
    private static Formula Bracket(Formula instance) => Seq(OpenBracket, instance, CloseBracket);
    private static Formula Instance(Formula instance, Formula body) => Seq(Bracket(instance), Comma, Sp, body);
    private static Formula Sizes(Formula body) => All("p", N(), Instance(Call("NeZero", V("p")), All("n", N(), body)));
    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
            Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
                StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula ControlledFormula()
    {
        Formula p = V("p"), n = V("n"), u = V("U"), i = V("i"), j = V("j");
        Formula taili = App(Q("Fin", "tail"), i), tailj = App(Q("Fin", "tail"), j);
        Formula identity = Parenthesized(Seq(D(1), Colon, Sp, Mat(p, n)));
        Formula block = Call("ite", Eqn(App(i, D(0)), D(1)), App(u, taili, tailj), App(identity, taili, tailj));
        Formula body = Call("ite", Eqn(App(i, D(0)), App(j, D(0))), block, D(0));
        return Disp(Sizes(All("U", Mat(p, n), All("i", Basis(p, Add(n, D(1))), All("j", Basis(p, Add(n, D(1))),
            Eqn(Call("controlled", p, u, i, j), body))))));
    }
    private static Formula ClaimBody()
    {
        Formula p = V("p"), n = V("n"), u = V("U"), k = V("k"), m = V("m");
        Formula membership = Ex("k", N(), Member(Call("controlled", p, u), Call("cliffordHierarchy", p, Add(n, D(1)), k)));
        Formula conclusion = Ex("m", N(), Eqn(Call("orderOf", u), Pow(p, m)));
        return All("p", N(), Imp(App(Q("Nat", "Prime"), p), All("n", N(), All("U", Mat(p, n),
            Imp(Member(u, Unitary(p, n)), Imp(membership, conclusion))))));
    }
    private static Formula ClaimFormula() => Disp(Eqn(V("claim"), Parenthesized(ClaimBody())));
}
