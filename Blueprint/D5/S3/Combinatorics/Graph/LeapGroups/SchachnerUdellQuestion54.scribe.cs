using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LeapGroups;

internal sealed class SchachnerUdellQuestion54Document : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/LeapGroups/SchachnerUdellQuestion54.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact leap subgroups of all prisms and positive-dimensional cubes.",
        H("Schachner–Udell Question 5.4"),
        Blocks(
            Node("prism", "Prism graph", "prism", Prism(),
                "The first factor is the complete graph on the two residues. The circulant on the second factor has step one in either direction. For n at least three this gives the n-cycle, with all wraparound edges.",
                DescribeRole.Definition),
            Node("prism-parity", "Prism parity", "prismParity", PrismParity(),
                "The ring homomorphism reduces the cycle index modulo two. Its existence uses the divisor proof h. On the stated cycle range the formula is the residue of the sum of the two least nonnegative coordinates.",
                DescribeRole.Definition),
            Node("cube-parity", "Cube parity", "cubeParity", CubeParity(),
                "The bit function takes false to zero and true to one in ZMod(2). The resulting sum is the Hamming weight reduced modulo two.",
                DescribeRole.Definition),
            Node("classification", "Exact subgroup equalities on the original vertices", "result", Result(),
                "The three clauses answer both families in Question 5.4 on printed and PDF page 21. In a prism the diagonal advances both coordinates. When n is odd, one extra circuit switches the layer, whereas when n is even the index and the parity determine the layer. In a cube, correcting differing coordinates in pairs gives every same-class transposition. The bipartite equalities use the setwise action on the unordered pair of fibers. Each fiber is inhabited in its stated range.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(
                    "D5/L/FiniteGroups/schachnerudell2026leapgroups"))))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Rel(Formula l, Formula symbol, Formula r) => Seq(l, Sp, symbol, Sp, r);
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula ForDivisorProof(Formula body) =>
        Seq(Forall, Sp, F.Id("h"), Sp, Colon, Sp, Seq(Open, Even, Close), Comma, Sp, body);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);
    private static Formula N => F.Id("n");
    private static Formula X => F.Id("x");
    private static Formula Nat => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Bool => new Formula.NamedConstant(FormulaIdentifier.Create("Bool"));
    private static Formula Zn => Call("ZMod", N);
    private static Formula Ztwo => Call("ZMod", D(2));
    private static Formula PrismVertices => Seq(Ztwo, Sp, Times, Sp, Zn);
    private static Formula CubeVertices => new Formula.TypeArrow(Call("Fin", N), Bool);
    private static Formula Even => Rel(D(2), Mid, N);

    private static Formula Prism() => All("n", Nat, Rel(Call("prism", N), Eq,
        Call("boxProd", Call("complete", Ztwo), Call("circulant", Zn, new Formula.SetLiteral([D(1)])))));

    private static Formula PrismParity() => All("n", Nat, ForDivisorProof(All("x", PrismVertices,
        Rel(Call("prismParity", F.Id("h"), X), Eq,
            Seq(Call("fst", X), Plus, Call("castHom", F.Id("h"), Call("snd", X)))))));

    private static Formula CubeParity()
    {
        var i = F.Id("i");
        return All("n", Nat, All("x", CubeVertices, Rel(Call("cubeParity", X), Eq,
            Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, Call("Fin", N)), Sp,
                Call("bit", Call("x", i))))));
    }

    private static Formula Fiber(Formula color, byte c) => Seq(OpenBrace, X, Sp, Mid, Sp,
        color, Sp, Eq, Sp, D(c), CloseBrace);

    private static Formula Stabilizer(Formula vertices, Formula color) =>
        Call("stabilizer", Call("Perm", vertices), new Formula.SetLiteral([Fiber(color, 0), Fiber(color, 1)]));

    private static Formula Result()
    {
        var prismGroup = Call("leapGroup", Call("prism", N));
        var odd = All("n", Nat, Imp(Rel(D(3), Leq, N), Imp(Call("Odd", N),
            Rel(prismGroup, Eq, Call("Perm", PrismVertices)))));
        var even = All("n", Nat, Imp(Rel(D(4), Leq, N), ForDivisorProof(Rel(prismGroup, Eq,
            Stabilizer(PrismVertices, Call("prismParity", F.Id("h"), X))))));
        var cube = All("n", Nat, Imp(Rel(D(1), Leq, N),
            Rel(Call("leapGroup", Call("hypercube", N)), Eq,
                Stabilizer(CubeVertices, Call("cubeParity", X)))));
        return And(Seq(Open, odd, Close),
            And(Seq(Open, even, Close), Seq(Open, cube, Close)));
    }
}
