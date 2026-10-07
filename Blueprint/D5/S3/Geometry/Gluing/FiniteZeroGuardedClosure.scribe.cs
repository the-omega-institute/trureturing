using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class FiniteZeroGuardedClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero-guarded coordinate permutations have uniform transport conditions and a closed generated relation.",
        H("Finite zero-guarded permutation identifications"),
        Blocks(
            Paragraph(Text("Let T and I be arbitrary finite types. Give T a discrete "
                + "topology, and let A be any Hausdorff topological space with a "
                + "designated element zero. Let S be any subset of the coordinate "
                + "space of maps from I to A, with its relative product topology. "
                + "Assume S is invariant under every coordinate permutation: if z "
                + "belongs to S, then reindex(rho,z), whose i-th coordinate is "
                + "z(rho inverse(i)), also belongs to S. The types T and I and the "
                + "set S may be empty. Neither closedness nor compactness of S is required.")),
            Paragraph(Text("For each pair (t,f) in T times I, fix an arbitrary target "
                + "label next(t,f) and an arbitrary permutation sigma(t,f) of I. "
                + "These data depend only on the label and coordinate index. "
                + "Write K for the subtype of S and permute(rho,z) for reindex(rho,z) "
                + "viewed as a point of K, using the invariance assumption. "
                + "Set X=T times K. A generating identification seam(a,b) holds "
                + "precisely when some coordinate f of a's carrier point is zero "
                + "and b=(next(a's label,f),permute(sigma(a's label,f),a's carrier point)). "
                + "Let R be the equivalence closure of this exact generating relation.")),
            Paragraph(Text("For a finite subset Z of I, zeroOn(z,Z) means that every "
                + "coordinate indexed by Z is zero. Define guard(t,u,rho,Z) to mean "
                + "that R relates (t,z) to (u,permute(rho,z)) for every z in K "
                + "satisfying zeroOn(z,Z). This is a uniform assertion about the "
                + "generated relation, not an additional hypothesis. "
                + "The finite state type is State=T times T times Perm(I) times Finsets(I), "
                + "with the factors associated to the right. Here coord evaluates "
                + "the underlying coordinate of a subtype point; fst and snd are "
                + "product projections. Types denotes the universe of types, Maps "
                + "a function type, Sets a powerset, Subtype the subtype of a set, "
                + "and card the finite cardinality. relationSet(R) is the set of "
                + "pairs related by R, and indexedUnion(pieces,State) is the union "
                + "of the State-indexed sets.")),
            Describe.Lean(
                DescribeId.Create("uniform-zero-guarded-closed-relation"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Gluing/FiniteZeroGuardedClosure.uniform_transport_and_closed_relation"),
                H("Uniform transport, finite closed pieces and exact state count"),
                StatementSource.FromAuthor(F.Disp(new Formula.Aligned(
                    [.. Definitions(), Statement()]))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Induct on the equivalence closure while retaining "
                        + "both a cumulative permutation and a finite set of source "
                        + "coordinates that must be zero. A generating identification "
                        + "uses its supplied permutation and the singleton guard. "
                        + "Reflexivity uses the identity permutation and the empty guard. "
                        + "For symmetry, invert the cumulative permutation and send "
                        + "the guard set through the original permutation. The original "
                        + "uniform assertion then applies to the inverse-permuted point. "
                        + "For transitivity, multiply the two permutations and take "
                        + "the union of the first guard with the second guard pulled "
                        + "back through the first permutation. Both segments are then "
                        + "valid at the same source point and its actual intermediate image.")),
                    Paragraph(Text("Consequently every related pair has one uniform "
                        + "guarded transport description, and applying a guard to the "
                        + "actual source point proves the converse. For each state "
                        + "(t,u,rho,Z), take the set of pairs whose labels are t,u, "
                        + "whose source satisfies zeroOn(z,Z), and whose target carrier "
                        + "is permute(rho,z), provided guard(t,u,rho,Z) holds; otherwise "
                        + "take the empty set. These are the closed pieces in the theorem. "
                        + "The graph condition is closed because the permutation is "
                        + "continuous and K is Hausdorff. The coordinate-zero conditions "
                        + "are closed, and the label conditions are closed in discrete T. "
                        + "Their intersection is therefore closed in X times X.")),
                    Paragraph(Text("The uniform equivalence identifies R exactly with "
                        + "the union of these pieces. The four finite factors give "
                        + "card(State)=card(T) squared times factorial(card(I)) times "
                        + "two to the power card(I). A finite union of closed sets is "
                        + "closed. This closedness is relative to the original subtype "
                        + "carrier and its product topology; no closedness of S in the "
                        + "ambient coordinate space is inferred or needed. "
                        + "No inverse pairing, freeness, nonempty carrier, algebraic "
                        + "operations on A, or manifold structure is assumed."))),
                DescribeRole.Theorem))));

    private static Formula[] Definitions()
    {
        var t = F.Id("t");
        var u = F.Id("u");
        var z = F.Id("z");
        var i = F.Id("i");
        var f = F.Id("f");
        var rho = F.Id("rho");
        var set = F.Id("Z");
        var a = F.Id("a");
        var b = F.Id("b");
        var ab = F.Id("ab");
        var carrier = F.Id("K");
        var space = F.Id("X");
        var permutations = Call("Perm", F.Id("I"));
        var finsets = Call("Finsets", F.Id("I"));
        var pairSpace = Product(space, space);
        return
        [
            All("rho", permutations, All("z", Maps(F.Id("I"), F.Id("A")),
                All("i", F.Id("I"), Eq(Call("coord", Call("reindex", rho, z), i),
                    Call("coord", z, Call("inverse", rho, i)))))),
            Eq(carrier, Call("Subtype", F.Id("S"))),
            All("rho", permutations, All("z", carrier, All("i", F.Id("I"),
                Eq(Call("coord", Call("permute", rho, z), i),
                    Call("coord", z, Call("inverse", rho, i)))))),
            Eq(space, Product(F.Id("T"), carrier)),
            All("a", space, All("b", space, Iff(Call("seam", a, b),
                Exists("f", F.Id("I"), And(
                    Eq(Call("coord", Call("snd", a), f), F.D(0)),
                    Eq(b, Pair(Call("next", Pair(Call("fst", a), f)),
                        Call("permute", Call("sigma", Pair(Call("fst", a), f)),
                            Call("snd", a))))))))),
            Eq(F.Id("R"), Call("EqvGen", F.Id("seam"))),
            All("z", carrier, All("Z", finsets, Iff(Call("zeroOn", z, set),
                All("i", F.Id("I"), Implies(In(i, set),
                    Eq(Call("coord", z, i), F.D(0))))))),
            All("t", F.Id("T"), All("u", F.Id("T"),
                All("rho", permutations, All("Z", finsets,
                    Iff(Call("guard", t, u, rho, set), All("z", carrier,
                        Implies(Call("zeroOn", z, set),
                            Call("R", Pair(t, z), Pair(u, Call("permute", rho, z)))))))))),
            Eq(F.Id("State"), Product(F.Id("T"),
                Product(F.Id("T"), Product(permutations, finsets)))),
            All("ab", pairSpace, Iff(In(ab, Call("relationSet", F.Id("R"))),
                Call("R", Call("fst", ab), Call("snd", ab)))),
            All("pieces", Maps(F.Id("State"), Call("Sets", pairSpace)),
                All("ab", pairSpace, Iff(
                    In(ab, Call("indexedUnion", F.Id("pieces"), F.Id("State"))),
                    Exists("s", F.Id("State"), In(ab, Call("pieces", F.Id("s")))))))
        ];
    }

    private static Formula Statement()
    {
        var t = F.Id("T");
        var i = F.Id("I");
        var a = F.Id("A");
        var s = F.Id("S");
        var coordinates = Maps(i, a);
        var ports = Product(t, i);
        var permutations = Call("Perm", i);
        var invariant = All("rho", permutations, All("z", coordinates,
            Implies(In(F.Id("z"), s),
                In(Call("reindex", F.Id("rho"), F.Id("z")), s))));
        return All("T", F.Id("Types"), All("I", F.Id("Types"),
            All("A", F.Id("Types"), Implies(And(
                Call("Finite", t), Call("Finite", i),
                Call("TopologicalSpace", t), Call("DiscreteTopology", t),
                Call("TopologicalSpace", a), Call("Hausdorff", a), Call("Zero", a)),
                All("S", Call("Sets", coordinates), Implies(invariant,
                    All("next", Maps(ports, t), All("sigma", Maps(ports, permutations),
                        Conclusions()))))))));
    }

    private static Formula Conclusions()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var rho = F.Id("rho");
        var z = F.Id("Z");
        var space = F.Id("X");
        var state = F.Id("State");
        var pieces = F.Id("pieces");
        var relationSet = Call("relationSet", F.Id("R"));
        var uniform = All("a", space, All("b", space,
            Iff(Call("R", a, b), Exists("rho", Call("Perm", F.Id("I")),
                Exists("Z", Call("Finsets", F.Id("I")), And(
                    Call("guard", Call("fst", a), Call("fst", b), rho, z),
                    Call("zeroOn", Call("snd", a), z),
                    Eq(Call("snd", b), Call("permute", rho, Call("snd", a)))))))));
        var count = Multiply(Multiply(new Formula.Power(Call("card", F.Id("T")), F.D(2)),
            Call("factorial", Call("card", F.Id("I")))),
            new Formula.Power(F.D(2), Call("card", F.Id("I"))));
        var closedPieces = Exists("pieces", Maps(state, Call("Sets", Product(space, space))),
            And(All("s", state, Call("IsClosed", Call("pieces", F.Id("s")))),
                Eq(relationSet, Call("indexedUnion", pieces, state)),
                Eq(Call("card", state), count)));
        return And(uniform, closedPieces, Call("IsClosed", relationSet));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Maps(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Product(Formula left, Formula right) =>
        F.Seq(left, F.Sp, F.Times, F.Sp, F.Open, right, F.Close);
    private static Formula Pair(Formula left, Formula right) =>
        F.Seq(F.Open, left, F.Comma, right, F.Close);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula In(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
