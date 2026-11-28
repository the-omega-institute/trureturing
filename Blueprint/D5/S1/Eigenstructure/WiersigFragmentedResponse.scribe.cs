using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class WiersigFragmentedResponseDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S1/Eigenstructure/WiersigFragmentedResponse.sharp_passive_fragmented_response";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/wiersig2026fragmentedresponse");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp linewidth bound and minimum loss rank for each fragmented Jordan partition.",
        H("Passive fragmented response"),
        Blocks(Describe.Lean(
            DescribeId.Create("sharp-passive-fragmented-response"),
            DeclarationHandle.Create(Handle),
            H("Sharp response and simultaneous minimum loss rank"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "The partition is a positive size function m on Fin(b). The largest size p "
                    + "bounds every size and occurs among them. Positions(m) is the dependent sum "
                    + "of Fin(m(j)) over the block labels j. The complex matrices use orthonormal "
                    + "coordinates indexed by Positions(m).")),
                Paragraph(Text(
                    "Write N(H,E) = H − EI, linewidth(E) = −2 Im E, and Γ(H) = i(H − H*), "
                    + "where * denotes conjugate transpose. The chain basis B is a complex linear "
                    + "basis of the coordinate space. The conditional chain step sends B(j,a) "
                    + "to B(j,a+k) when a+k is in the block and to zero otherwise. "
                    + "The function pred is natural predecessor and the matrix norm is the "
                    + "Euclidean operator norm.")),
                Paragraph(Text(
                    "For every passive matrix of the given partition, E is the sole eigenvalue. "
                    + "The resolvent is the finite Laurent sum away from E and its highest-order "
                    + "coefficient N^(p−1) is "
                    + "nonzero. The coefficient norm is at most the linewidth to power p−1 "
                    + "and the loss rank is at least b. One matrix of the same partition "
                    + "attains both bounds.")),
                Paragraph(Text(
                    "The normalized Cayley transform gives the norm bound. Restricting the loss "
                    + "to the eigenspace gives an injective map. For attainment use the "
                    + "orthogonal sum S of lower unit shifts and A = (I−S)^−1 − I. Each normalized "
                    + "loss block is the all-ones matrix. The largest block supplies a unit "
                    + "vector on which A^(p−1) has norm one. Ranks of powers give the "
                    + "prescribed chain multiplicities, and the nilpotent Jordan-chain theorem "
                    + "gives a basis with those sizes."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Admissible(Formula matrix, Formula energy, Formula sizes, Formula blocks)
    {
        Formula basis = F.Id("B"), iterate = F.Id("r"), block = F.Id("j"), position = F.Id("a");
        Formula size = Call("size", sizes, block), next = Call("add", position, iterate);
        Formula chainAction = Equal(
            Call("mulVec", Call("pow", Call("N", matrix, energy), iterate),
                Call("basisAt", basis, block, position)),
            Call("ite",
                new Formula.Relation(next, FormulaRelationOperator.LessThan, size),
                Call("basisAt", basis, block, next), D(0)));
        return And(Call("PosSemidef", Call("Gamma", matrix)),
            new Formula.BindMany(FormulaQuantifier.Exists,
                [Bound("B", Call("Basis", Call("Positions", sizes), Call("Complex")))],
                new Formula.BindMany(FormulaQuantifier.ForAll,
                    [Bound("r", Call("Nat")), Bound("j", Call("Fin", blocks)),
                     Bound("a", Call("Fin", size))], chainAction)));
    }

    private static Formula TheoremFormula()
    {
        Formula b = F.Id("b"), p = F.Id("p"), m = F.Id("m"), e = F.Id("E");
        Formula h = F.Id("H"), w = F.Id("W"), j = F.Id("j"), z = F.Id("z"), k = F.Id("k");
        Formula linewidth = Call("linewidth", e), top = Call("pred", p);
        Formula bound = Call("pow", linewidth, top);
        Formula n = Call("N", h, e);
        Formula matrices = Call("ComplexMatrix", Call("Positions", m));
        Formula size = Call("size", m, j);
        Formula spectralExpansion = Equal(
            Call("inv", Call("sub", Call("scalarMatrix", z), h)),
            Seq(Sum, Underscore, Grp(k, Sp, InMacro, Sp, Call("range", p)), Sp,
                Call("smul", Call("pow", Call("inv", Call("sub", z, e)), Call("succ", k)),
                    Call("pow", n, k))));
        Formula resolvent = new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("z", Call("Complex"))], Implies(Seq(z, Sp, Neq, Sp, e), spectralExpansion));
        Formula spectrum = new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("z", Call("Complex"))],
            new Formula.Logic(Call("not", Call("IsUnit", Call("sub", Call("scalarMatrix", z), h))),
                FormulaLogicOperator.Iff, Equal(z, e)));
        Formula upper = new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("H", matrices)], Implies(Admissible(h, e, m, b),
                And(Seq(Call("pow", n, top), Sp, Neq, Sp, D(0)),
                    And(Seq(Call("opNorm", Call("pow", n, top)), Sp, Le, Sp, bound),
                        And(Seq(b, Sp, Le, Sp, Call("rank", Call("Gamma", h))), And(spectrum, resolvent))))));
        Formula witness = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("W", matrices)],
            And(Admissible(w, e, m, b),
                And(Equal(Call("opNorm", Call("pow", Call("N", w, e), top)), bound),
                    Equal(Call("rank", Call("Gamma", w)), b))));
        Formula sizesBounded = new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("j", Call("Fin", b))], Seq(size, Sp, Le, Sp, p));
        Formula maxOccurs = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("j", Call("Fin", b))], Equal(size, p));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("b", Call("Nat")), Bound("p", Call("Nat")),
             Bound("m", Call("Function", Call("Fin", b), Call("PNat"))),
             Bound("E", Call("Complex"))],
            Implies(And(Seq(D(2), Sp, Le, Sp, b),
                And(Seq(D(2), Sp, Le, Sp, p),
                    And(sizesBounded, And(maxOccurs, Seq(D(0), Sp, Lt, Sp, linewidth))))),
                And(upper, witness))));
    }
}
