using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class BinaryLagrangianGraphFormDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Information/BinaryLagrangianGraphForm.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/vandennest2004graphical");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "After exchanging the two coordinates at a set of positions and a diagonal shear, every Lagrangian subspace of a binary symplectic space is the graph of a symmetric matrix with zero diagonal.",
        H("Binary Lagrangian subspaces in graph form"),
        Blocks(
            Node("symplectic-form", "The binary symplectic form", "sp", SpFormula(),
                "Write V(N) for the functions Fin N → ℤ/2ℤ and E(N) = V(N) × V(N). The form pairs the first coordinate of one vector with the second of the other at every position.",
                DescribeRole.Definition),
            Node("coordinate-swap", "Exchanging coordinates on a set of positions", "swapAt", SwapFormula(),
                "At the positions in H the two coordinates are exchanged and elsewhere they are kept; on a stabilizer symbol this is the action of a Hadamard gate on those qubits.",
                DescribeRole.Definition),
            Node("graph-form", "Every Lagrangian subspace is a graph after a swap and a shear", "lagrangian_graph_form", GraphFormFormula(),
                "Let L be isotropic for the form and of dimension N. Choose a set H maximizing the rank of the first projection of the swapped subspace. If that rank were below N, a vector of L with zero first projection and a nonzero second coordinate at some position i would exist; isotropy keeps the unit vector at i out of the old first projection, so erasing the coordinate i is injective there, and exchanging the coordinates at i adds that unit vector to the new first projection, so the rank strictly increases, against maximality. Hence the first projection is bijective and the swapped subspace is the graph of a linear map A, symmetric by isotropy on the preimages of the unit vectors. With d the diagonal of A and Γ = A minus its diagonal, a vector lies in L exactly when its swapped second coordinate, plus d times the swapped first coordinate, equals Γ applied to the swapped first coordinate; on symbols the shear is the action of phase gates. This is the binary form of Theorem 1 of Van den Nest, Dehaene and De Moor (Phys. Rev. A 69, 022316), which constructs the Hadamard set from a rank decomposition of the generator matrix; the proof here chooses it by maximizing the rank instead.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string title, string declaration, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z2() => Seq(Mathbb, Grp(V("Z")), Slash, D(2), Mathbb, Grp(V("Z")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula head, Formula arg) => Seq(head, Open, arg, Close);
    private static Formula For(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, name, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Imp(Formula premise, Formula body) => Seq(premise, Sp, Rightarrow, Sp, body);
    private static Formula IffOf(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
    private static Formula Plus2(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Times2(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Dot2(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula SumOver(Formula index, Formula body) => Seq(Sum, Underscore, Grp(index), Sp, body);
    private static Formula FinN(Formula n) => Call("Fin", n);
    private static Formula Vec(Formula n) => Parenthesized(Arrow(FinN(n), Z2()));
    private static Formula Sym(Formula n) => Parenthesized(Times2(Vec(n), Vec(n)));
    private static Formula Fst(Formula x) => Call("fst", x);
    private static Formula Snd(Formula x) => Call("snd", x);
    private static Formula Cond(Formula test, Formula yes, Formula no) => Call("ite", test, yes, no);

    private static Formula SpFormula()
    {
        Formula n = V("N"), u = V("u"), v = V("v"), i = V("i");
        Formula body = SumOver(i, Parenthesized(Plus2(
            Dot2(App(Fst(u), i), App(Snd(v), i)), Dot2(App(Snd(u), i), App(Fst(v), i)))));
        return Disp(For(n, N(), For(Seq(u, Sp, v), Sym(n), Equal(Call("sp", u, v), body))));
    }

    private static Formula SwapFormula()
    {
        Formula n = V("N"), h = V("H"), v = V("v"), i = V("i");
        Formula first = Cond(Member(i, h), App(Snd(v), i), App(Fst(v), i));
        Formula second = Cond(Member(i, h), App(Fst(v), i), App(Snd(v), i));
        return Disp(For(n, N(), For(h, Call("Finset", FinN(n)), For(v, Sym(n),
            Equal(Call("swapAt", h, v),
                Parenthesized(Seq(Seq(LambdaLower, Sp, i, Sp, Mapsto, Sp, first), Comma, Sp,
                    Seq(LambdaLower, Sp, i, Sp, Mapsto, Sp, second))))))));
    }

    private static Formula GraphFormFormula()
    {
        Formula n = V("N"), l = V("L"), u = V("u"), v = V("v"), h = V("H"), d = V("d"),
            g = Gamma, i = V("i");
        Formula iso = For(Seq(u, Sp, v), Sym(n),
            Imp(And(Member(u, l), Member(v, l)), Equal(Call("sp", u, v), D(0))));
        Formula dim = Equal(Call("finrank", Z2(), l), n);
        Formula sw = Call("swapAt", h, v);
        Formula shear = Plus2(Snd(sw), Parenthesized(Seq(LambdaLower, Sp, i, Sp, Mapsto, Sp,
            Dot2(App(d, i), App(Fst(sw), i)))));
        Formula graph = For(v, Sym(n), IffOf(Member(v, l),
            Parenthesized(Equal(shear, Call("mulVec", g, Fst(sw))))));
        Formula props = And(Call("IsSymm", g), And(
            Parenthesized(For(i, FinN(n), Equal(App(g, Seq(i, Comma, Sp, i)), D(0)))),
            Parenthesized(graph)));
        Formula conclusion = Some(h, Call("Finset", FinN(n)), Some(d, Vec(n),
            Some(g, Call("Matrix", FinN(n), FinN(n), Z2()), props)));
        return Disp(For(n, N(), For(l, Call("Submodule", Z2(), Sym(n)),
            Imp(Parenthesized(iso), Imp(dim, conclusion)))));
    }
}
