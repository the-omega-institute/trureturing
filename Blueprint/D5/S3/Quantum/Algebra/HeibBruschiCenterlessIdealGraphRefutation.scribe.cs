using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class HeibBruschiCenterlessIdealGraphRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Algebra/HeibBruschiCenterlessIdealGraphRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/heib2026structural");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two-dimensional affine Lie algebra refutes Heib–Bruschi Conjecture 83 over every field.",
        H("The affine Lie algebra refutes Heib–Bruschi Conjecture 83"),
        Blocks(
            Node("admissible-basis", "Minimal-graph-admissible bases", "IsAdmissible", AdmissibleFormula(),
                "Definition 16 of arXiv:2601.16161v1 asks for a basis with \"[x_j,x_k]=α_jk x_δ(j,k)\", α antisymmetric and δ symmetric, and sets \"δ(j,k):=0 whenever α_jk=0\" with \"x_0:=0\". The index none plays the role of 0 and elim(δ(j,k), 0, b) is x_δ(j,k).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("graph-edge", "Edges of the minimal graph", "Edge", EdgeFormula(),
                "Algorithm 1 draws an edge from v_j to v_ℓ labelled v_k when \"[x_j,x_k]∝x_ℓ\", and x∝y means x=κy with κ a nonzero field element. A minimal graph is built from a basis, so its vertices are the indices of the basis.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ideal-graph-property", "The ideal-graph-property", "IdealGraphProperty", IdealGraphFormula(),
                "Definition 75: \"A subset W⊆V is said to satisfy the ideal-graph-property if and only if no edge e∈E points from a vertex w∈W to a vertex v∈V∖W.\" Edges with any label count.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("proper-subset", "A proper subset with the ideal-graph-property", "HasProperIdealGraphSubset", ProperSubsetFormula(),
                "This is the negation of condition (i) of Conjecture 83: some proper non-empty vertex subset has the ideal-graph-property.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-over", "Conjecture 83 over a field", "conjectureOver", ConjectureFormula(),
                "Conjecture 83 (§IV.D): for a minimal-graph-admissible Lie algebra with trivial center, either (i) no proper non-empty vertex subset has the ideal-graph-property, or (ii) the algebra is a direct sum of components with trivial center whose every minimal graph has no such subset. The direct sum is an internal direct sum of ideals I(j) indexed by an arbitrary type J, which is a Lie-algebra direct sum because brackets between different ideals lie in their zero intersection; every admissible basis c of a component gives one of its minimal graphs.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 83", "claim", ClaimFormula(),
                "The paper denotes \"any field\" by 𝔽, so the conjecture is read over every field K.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-fails", "Conjecture 83 fails over every field", "conjecture_fails", FailsFormula(),
                "Let A=K×K with bracket [(a,b),(c,d)]=(0,ad−cb) and basis X=(1,0), Y=(0,1), so [X,Y]=Y. The basis is admissible with α(0,1)=1, α(1,0)=−1 and δ(0,1)=δ(1,0)=1. The center is zero since [aX+bY,X]=−bY and [aX+bY,Y]=aY. The singleton {1} is proper and non-empty, and the only edge leaving Y comes from [Y,X]=−Y and returns to Y, so condition (i) fails. Every nonzero ideal contains Y, hence two different components of an internal direct sum cannot both be nonzero; the one nonzero component is all of A, and the basis transported to it keeps the subset {1}, so condition (ii) fails.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("result", "Conjecture 83 is refuted", "result", ResultFormula(),
                "Specializing the previous theorem to the rational numbers refutes the conjecture as stated for every field.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("heib-bruschi-2026-conjecture-83-affine-refutation"),
                    ResolutionKind.Refuted)
))));

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula TypeU() => V("Type");
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula head, Formula arg) => Seq(head, Open, arg, Close);
    private static Formula App(Formula head, Formula first, Formula second) =>
        Seq(head, Open, first, Comma, Sp, second, Close);
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Inst(Formula instance, Formula body) =>
        Seq(OpenBracket, instance, CloseBracket, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula NotEqual(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula Or(Formula left, Formula right) => Seq(left, Sp, Lor, Sp, right);
    private static Formula Not(Formula body) => Seq(Neg, Sp, body);
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
    private static Formula Lie(Formula x, Formula y) => Seq(OpenBracket, x, Comma, Sp, y, CloseBracket);
    private static Formula Smul(Formula c, Formula x) => Seq(c, Sp, Cdot, Sp, x);
    private static Formula Bot() => Perp;
    private static Formula FinN(Formula n) => Call("Fin", n);
    private static Formula BasisType(Formula n, Formula k, Formula l) => Call("Basis", FinN(n), k, l);

    private static Formula OverKL(Formula body)
    {
        Formula k = V("K"), l = V("L");
        return For(Seq(k, Sp, l), TypeU(), Inst(Call("Field", k), Inst(Call("LieRing", l),
            Inst(Call("LieAlgebra", k, l), body))));
    }

    private static Formula OverBasis(Formula body)
    {
        Formula n = V("n");
        return OverKL(For(n, N(), For(V("b"), BasisType(n, V("K"), V("L")), body)));
    }

    private static Formula BasisAt(Formula index) => App(V("b"), index);

    private static Formula AdmissibleFormula()
    {
        Formula n = V("n"), j = V("j"), k = V("k"), fin = FinN(n);
        Formula jk = Seq(j, Sp, k);
        Formula alphaJK = App(Alpha, j, k), deltaJK = App(DeltaLower, j, k);
        Formula antisym = For(jk, fin, Equal(alphaJK, Seq(Minus, App(Alpha, k, j))));
        Formula sym = For(jk, fin, Equal(deltaJK, App(DeltaLower, k, j)));
        Formula zero = For(jk, fin, Parenthesized(IffOf(Equal(deltaJK, V("none")), Equal(alphaJK, D(0)))));
        Formula bracket = For(jk, fin, Equal(Lie(BasisAt(j), BasisAt(k)),
            Smul(alphaJK, Call("elim", deltaJK, D(0), V("b")))));
        Formula body = Some(Alpha, Arrow(fin, Arrow(fin, V("K"))),
            Some(DeltaLower, Arrow(fin, Arrow(fin, Call("Option", fin))),
                And(Parenthesized(antisym), And(Parenthesized(sym),
                    And(Parenthesized(zero), Parenthesized(bracket))))));
        return Disp(OverBasis(IffOf(Call("IsAdmissible", V("b")), Parenthesized(body))));
    }

    private static Formula EdgeFormula()
    {
        Formula n = V("n"), j = V("j"), k = V("k"), l = V("l");
        Formula body = Some(Kappa, V("K"), And(NotEqual(Kappa, D(0)),
            Equal(Lie(BasisAt(j), BasisAt(k)), Smul(Kappa, BasisAt(l)))));
        return Disp(OverBasis(For(Seq(j, Sp, k, Sp, l), FinN(n),
            IffOf(Call("Edge", V("b"), j, k, l), Parenthesized(body)))));
    }

    private static Formula IdealGraphFormula()
    {
        Formula n = V("n"), w = V("W"), j = V("j"), k = V("k"), l = V("l");
        Formula body = For(Seq(j, Sp, k, Sp, l), FinN(n),
            Imp(Call("Edge", V("b"), j, k, l), Imp(Member(j, w), Member(l, w))));
        return Disp(OverBasis(For(w, Call("Set", FinN(n)),
            IffOf(Call("IdealGraphProperty", V("b"), w), Parenthesized(body)))));
    }

    private static Formula ProperSubsetFormula()
    {
        Formula n = V("n"), w = V("W");
        Formula body = Some(w, Call("Set", FinN(n)), And(Call("Nonempty", w),
            And(NotEqual(w, V("univ")), Call("IdealGraphProperty", V("b"), w))));
        return Disp(OverBasis(IffOf(Call("HasProperIdealGraphSubset", V("b")), Parenthesized(body))));
    }

    private static Formula ConjectureFormula()
    {
        Formula k = V("K"), l = V("L"), n = V("n"), b = V("b"), m = V("m"), c = V("c"),
            jIndex = V("J"), i = V("I"), j = V("j");
        Formula component = App(i, j);
        Formula componentCondition = For(j, jIndex, And(
            Equal(Call("center", k, component), Bot()),
            Parenthesized(For(m, N(), For(c, BasisType(m, k, component),
                Imp(Call("IsAdmissible", c), Not(Call("HasProperIdealGraphSubset", c))))))));
        Formula internalSum = Call("IsInternal",
            Seq(LambdaLower, Sp, j, Sp, Mapsto, Sp, Call("toSubmodule", component)));
        Formula split = Some(jIndex, TypeU(), Some(V("inst"), Call("DecidableEq", jIndex),
            Some(i, Arrow(jIndex, Call("LieIdeal", k, l)),
                And(internalSum, Parenthesized(componentCondition)))));
        Formula conclusion = Or(Not(Call("HasProperIdealGraphSubset", b)), Parenthesized(split));
        Formula body = For(l, TypeU(), Inst(Call("LieRing", l), Inst(Call("LieAlgebra", k, l),
            For(n, N(), For(b, BasisType(n, k, l),
                Imp(Call("IsAdmissible", b), Imp(Equal(Call("center", k, l), Bot()),
                    Parenthesized(conclusion))))))));
        return Disp(For(k, TypeU(), Inst(Call("Field", k),
            IffOf(Call("conjectureOver", k), Parenthesized(body)))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = V("K");
        return Disp(IffOf(V("claim"),
            Parenthesized(For(k, TypeU(), Inst(Call("Field", k), Call("conjectureOver", k))))));
    }

    private static Formula FailsFormula()
    {
        Formula k = V("K");
        return Disp(For(k, TypeU(), Inst(Call("Field", k), Not(Call("conjectureOver", k)))));
    }

    private static Formula ResultFormula() => Disp(Not(V("claim")));
}
