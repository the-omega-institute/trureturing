using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativePositiveBranchReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite canonical native branching before free-shape unification",
        H("The full finite named family"), Blocks(
            Paragraph(Text("X is the entire declared finite family of names, represented by a presentation p. An Equation is a primitive definition z=T(n), a native shift definition z=rho to power a of x, an ordered pair definition z=pair(x,y), or an equality x=y. Every occurrence of a name refers to the same original source value. Unused declared names remain in X. Source consists of arbitrary finite ordered Boolean trees, and rho is the actual native substitution, not a free unary symbol. In the display, canonicalCodes(v)(x)=encode(v(x)), canonicalShapes(v)(x)=shape(encode(v(x))), NativeHolds is Equation.Holds, and BranchHolds is BranchEquation.Holds.")),
            Entry("branches", "Executable finite constructor choices",
                "choices retains primitive, shift and equality equations. For each pair definition it offers exactly an ordinary case and a collapse case. branches forms their finite ordered product over the whole input list, retaining repeated constraints. An ordinary case requires the output code to be the pair of its input codes. A collapse case requires input ranks r+1 and r and output rank r+2 for some unrestricted natural r. That rank is not enumerated or bounded. Every code in the theorem is the actual canonical encode of the same original valuation."),
            Entry("shape", "Erase ranks only after selecting cases",
                "shape replaces each primitive rank by one fixed free primitive leaf and preserves ordered pairs. Primitive definitions and collapse cases become primitive shape equalities. Shift definitions become equalities of shapes. An ordinary pair definition becomes a free binary constructor equation. No interpreted native power is sent to the free occurs check. The exact canonical branch equations are retained alongside these weaker free-shape equations."),
            Describe.Lean(DescribeId.Create("native-canonical-branch-shape-reduction"),
                DeclarationHandle.Create(Prefix + "native_branch_reduction"),
                H("Exact canonical branching with total MGU shape reconstruction"),
                StatementSource.FromAuthor(Disp(Reduction())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every presentation p, finite named equation list E and entire original valuation v, all native equations hold exactly when there is a member B of the computed finite list branches(E) such that all canonical codes are normal, all exact code equations of B hold, and the actual free unifier of shapeEquations(B) succeeds. Evaluating its total action at the original canonical shapes returns the original shape at every declared name. Among its enumerated residual occurrences, connectivity is equivalent to equality of residual sort. ListMem in the display denotes ordinary list membership; sort(x,p,y) is y.")),
                    Paragraph(Text("Canonical encoding commutes with every actual native power. This follows by structural induction from the commutation of smart collapse with a common rank shift. At each pair, the two canonical input codes either have consecutive primitive ranks and collapse, or smart retains the ordinary pair. This gives a complete finite case selection. Conversely, expansion of each selected code equation gives its actual native equation, including the collapse identity. Erasing ranks then supplies a ground solution of every selected free-shape equation. Existing unification completeness gives the actual successful result, its restriction identity reconstructs all named shapes, and the exact residual-occurrence graph theorem gives the connected sort components.")),
                    Paragraph(Text("This is the canonical case reduction for an already named finite system. It does not construct the naming program for arbitrary MixedExpr inputs, solve affine rank equalities, compute minimum block bases, return an executable list of unrestricted native image charts, reconstruct all native outputs from independent bases, or perform signed pullback. The exact code constraints in this intermediate reduction are not a synthesized positive image cover."))), DescribeRole.Theorem)
        )));

    private static DocumentBlock Entry(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("native-branch-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Reduction()
    {
        var code = Call("canonicalCodes", V("v"));
        var s = Call("action", V("p"), V("S"));
        var c = Call("shapeEquations", V("B"));
        var vertices = Call("occurrenceVertices", V("p"), s);
        var normal = All("x", V("X"), Call("Normal", Call("encode", Call("v", V("x")))));
        var branchHolds = All("b", Call("BranchEquation", V("X")),
            Imp(Call("ListMem", V("b"), V("B")), Call("BranchHolds", code, V("b"))));
        var factors = All("x", V("X"), EqOf(
            Call("evaluate", Call("canonicalShapes", V("v")), Call("action", V("p"), V("S"), V("x"))),
            Call("shape", Call("encode", Call("v", V("x"))))));
        var components = All("a", Call("Occurrence", V("X")), All("b", Call("Occurrence", V("X")),
            Imp(Call("ListMem", V("a"), vertices), Imp(Call("ListMem", V("b"), vertices),
                IffOf(Call("Connected", c, s, V("a"), V("b")),
                    EqOf(Call("sort", V("a")), Call("sort", V("b"))))))));
        var unifier = Some("S", V("SubstInfo"), And(
            EqOf(Call("unify", Call("encodeEquations", V("p"), c), V("empty")), Call("ok", V("S"))),
            And(factors, components)));
        var rhs = Some("B", Call("List", Call("BranchEquation", V("X"))),
            And(Call("ListMem", V("B"), Call("branches", V("E"))), And(normal, And(branchHolds, unifier))));
        var lhs = All("e", Call("Equation", V("X")),
            Imp(Call("ListMem", V("e"), V("E")), Call("NativeHolds", V("v"), V("e"))));
        return All("X", V("Type"), All("p", Call("Presentation", V("X")),
            All("E", Call("List", Call("Equation", V("X"))), All("v", Arr(V("X"), V("Source")), IffOf(lhs, rhs)))));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Sp, Land, Sp, Open, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Sp, Implies, Sp, Open, b, Close);
    private static Formula IffOf(Formula a, Formula b) => Seq(Open, a, Close, Sp, Iff, Sp, Open, b, Close);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Open, b, Close);
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Open, b, Close);
}
