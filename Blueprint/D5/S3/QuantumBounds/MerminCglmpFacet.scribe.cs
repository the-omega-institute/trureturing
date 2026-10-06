using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class MerminCglmpFacetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/MerminCglmpFacet.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/grandjean2012mermincglmpfacet");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Mermin-CGLMP inequality has a saturating face of affine codimension one for every K >= 2.",
        H("The Mermin-CGLMP facet conjecture"),
        Blocks(
            Node("vertex", "Deterministic full behaviours", VertexFormula(),
                "Section II, PDF p. 1, states: “We consider a scenario involving three spatially separated parties (henceforth referred as Alice, Bob and Charlie), and with each of them performing 2 alternative K-outcome measurements.” Input 0 is source setting 1 and input 1 is source setting 2. Each of the three components of s assigns an output to both settings. The value of vertex is one exactly when all three observed outputs match these assignments, and is zero otherwise. The coordinates include all eight setting triples and all K-cubed output triples.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("L", "The local polytope", LocalFormula(),
                "Section II, PDF p. 2, states: “It suffices to consider deterministic classical strategies for determining the minimal value of S^(K) allowed in a local theory”. A local behaviour is a shared-randomness mixture of product response functions. Each response function is a mixture of deterministic assignments to its two settings; distributing these finite mixtures gives precisely the convex hull of the deterministic full behaviours. Thus L is the source's local polytope, with its normalisation and no-signalling relations inherited from those generators.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("bracket", "Least nonnegative residues", BracketFormula(),
                "Section II, PDF p. 1, states: “where [X]_K stands for X modulo K”. Int.emod is integer Euclidean remainder, with K first cast to the integers and the remainder then cast to the reals. For K >= 2 the value is in the interval from 0 through K-1, including for negative arguments.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("I", "The literal Bell functional", FunctionalFormula(),
                "Section II, PDF p. 1, gives (1): “S^(K) = ⟨[A_2−B_1+C_1]_K⟩ + ⟨[A_1+B_2−C_1]_K⟩ + ⟨[−A_1+B_1+C_2]_K⟩ + ⟨[−A_2−B_2−C_2−1]_K⟩ ≥ K−1”. Equation (2) defines ⟨[X]_K⟩ = ∑_{j=0}^{K−1} j P(X = j mod K). Summing each residue against the full joint probabilities groups exactly into these residue events. The four input triples are respectively (1,0,0), (0,1,0), (0,0,1) and (1,1,1); these encode (2,1,1), (1,2,1), (1,1,2) and (2,2,2) in the source. All integer output casts and all four signs and offsets are retained.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture for every K", ClaimFormula(true),
                "Section II, PDF p. 2, states verbatim: “We conjecture that inequality (1) is indeed facet-defining for all K ≥ 2.” The parameter K is natural-valued, so this is exactly the stated integer range. The first conjunct is validity on the entire local polytope. The second uses vectorSpan, the direction space of the affine span, so its finrank is affine dimension. The saturating face has dimension one less than L. The carrier is the full behaviour space; there is no projection to correlators or restriction to a family of strategies.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The inequality defines a facet", ClaimFormula(false),
                "Fixing Charlie's two outputs relabels each slice to CGLMP. The short-arc rigidity theorem supplies a multiplier for each slice. Additive separability in Charlie's outputs imposes a rectangular identity. Strategies with A_1+A_2+B_2−B_1 equal to 0 or −1 force each multiplier to be independent of both Charlie outputs. The common multiplier gives global rigidity. The convex-geometric bridge then proves the affine-dimension equation, while linearity extends validity from deterministic generators to their convex hull.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("mermin-facet-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Sub(Formula a, Formula b) => Subtract(a, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), To, b);
    private static Formula Product(Formula a, Formula b) => Seq(a, Times, b);
    private static Formula TripleType(Formula type) => Product(type, Product(type, type));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Fin(Formula k) => Call("Fin", k);
    private static Formula BehaviourType(Formula k) => Arrow(
        Product(Parenthesized(TripleType(Fin(D(2)))), Parenthesized(TripleType(Fin(k)))), Reals());
    private static Formula StrategyType(Formula k) => TripleType(Parenthesized(Arrow(Fin(D(2)), Fin(k))));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Call(name, args));
    private static Formula Tuple(params Formula[] items) =>
        Parenthesized(Seq(items.SelectMany((item, i) => i == 0 ? new[] { item } : new[] { Comma, item }).ToArray()));
    private static Formula Apply(Formula function, params Formula[] args) =>
        Seq(function, Tuple(args));
    private static Formula Projection(Formula value, params byte[] indices)
    {
        foreach (byte index in indices) value = Seq(value, Dot, D(index));
        return value;
    }
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Seq(Call("if", condition), Call("then", yes), Call("else", no));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Colon, type)), Parenthesized(body));

    private static Formula VertexFormula()
    {
        Formula k = F.Id("K"), s = F.Id("s"), q = F.Id("q");
        Formula matches = Logic(
            Equal(Apply(Projection(s, 1), Projection(q, 1, 1)), Projection(q, 2, 1)),
            FormulaLogicOperator.And,
            Logic(Equal(Apply(Projection(s, 2, 1), Projection(q, 1, 2, 1)), Projection(q, 2, 2, 1)),
                FormulaLogicOperator.And,
                Equal(Apply(Projection(s, 2, 2), Projection(q, 1, 2, 2)), Projection(q, 2, 2, 2))));
        Formula qt = Product(Parenthesized(TripleType(Fin(D(2)))), Parenthesized(TripleType(Fin(k))));
        return Disp(All("K", Nats(), All("s", StrategyType(k), All("q", qt,
            Equal(Call("vertex", k, s, q), If(matches, D(1), D(0)))))));
    }

    private static Formula LocalFormula()
    {
        Formula k = F.Id("K");
        return Disp(All("K", Nats(), Equal(Call("L", k),
            Call("convexHull", Reals(), Qualified("Set", "range", Call("vertex", k))))));
    }

    private static Formula BracketFormula()
    {
        Formula k = F.Id("K"), t = F.Id("t");
        return Disp(All("K", Nats(), All("t", Ints(), Equal(Call("bracket", k, t),
            Cast(Qualified("Int", "emod", t, Cast(k, Ints())), Reals())))));
    }

    private static Formula FunctionalFormula()
    {
        Formula k = F.Id("K"), p = F.Id("p");
        Formula a = Cast(F.Id("a"), Ints()), b = Cast(F.Id("b"), Ints()), c = Cast(F.Id("c"), Ints());
        Formula[] arguments = [Add(Sub(a, b), c), Sub(Add(a, b), c),
            Add(Add(Negate(a), b), c), Sub(Sub(Sub(Negate(a), b), c), D(1))];
        Formula[] settings = [Tuple(D(1), D(0), D(0)), Tuple(D(0), D(1), D(0)),
            Tuple(D(0), D(0), D(1)), Tuple(D(1), D(1), D(1))];
        Formula[] sums = arguments.Select((argument, i) => SumOver("a", Fin(k),
            SumOver("b", Fin(k), SumOver("c", Fin(k), Mul(Call("bracket", k, argument),
                Apply(p, Tuple(settings[i], Tuple(F.Id("a"), F.Id("b"), F.Id("c"))))))))).ToArray();
        return Disp(All("K", Nats(), All("p", BehaviourType(k),
            Equal(Call("I", k, p), Add(Add(Add(sums[0], sums[1]), sums[2]), sums[3])))));
    }

    private static Formula ClaimFormula(bool defining)
    {
        Formula k = F.Id("K"), p = F.Id("p"), local = Call("L", k), bound = Sub(Cast(k, Reals()), D(1));
        Formula valid = All("p", BehaviourType(k), Logic(Mem(p, local), FormulaLogicOperator.Implies,
            Le(bound, Call("I", k, p))));
        Formula face = Seq(OpenBrace, p, Mid, Logic(Mem(p, local), FormulaLogicOperator.And,
            Equal(Call("I", k, p), bound)), CloseBrace);
        Formula dimension = Equal(Add(Qualified("Module", "finrank", Reals(),
            Call("vectorSpan", Reals(), face)), D(1)), Qualified("Module", "finrank", Reals(),
            Call("vectorSpan", Reals(), local)));
        Formula body = All("K", Nats(), Logic(Le(D(2), k), FormulaLogicOperator.Implies,
            Logic(valid, FormulaLogicOperator.And, dimension)));
        return Disp(defining ? Logic(F.Id("claim"), FormulaLogicOperator.Iff, body) : body);
    }
}
