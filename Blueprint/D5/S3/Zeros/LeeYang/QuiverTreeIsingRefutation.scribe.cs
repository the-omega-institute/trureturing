using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class QuiverTreeIsingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fiolmartinezmontoyariosfukelman2020quiver");
    private const string Conjecture =
        "For any tree with e edges, any fixed positive integers n₁,…,nₑ and arbitrary "
        + "ρ(kᵢ,nᵢ)>0 the polynomials P(τ,x, n₁,…,nₑ) have all their x roots on the unit circle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive joint split weights refute the tree Lee-Yang conjecture.",
        H("A tree Ising polynomial with an off-circle root"),
        Blocks(
            Node("splits", "The positive edge splits", SplitsFormula(),
                "Section 2.2, printed p. 13 (PDF p. 14): “Assign a positive integer nᵢ to each "
                + "of the e edges of the tree graph.” “For every edge, split nᵢ into two positive "
                + "integers, nᵢ=kᵢ+(nᵢ−kᵢ) and assign each of these two integers to one of the "
                + "vertices at the ends of that edge.” Fintype.piFinset gives exactly the "
                + "configuration functions in the product of Finset.Icc 1 (n i − 1). Nat.sub "
                + "is natural-number subtraction, truncated at zero."),
            Node("mass", "Vertex masses", MassFormula(),
                "Section 2.2, printed p. 13 (PDF p. 14): “Then, if a vertex has degree dⱼ this "
                + "procedure assigns to that vertex dⱼ integers. Let mⱼ be the sum of these "
                + "integers at a given vertex; the magnetic field at that vertex is then mⱼ H.” "
                + "The source endpoint receives k i and the target endpoint receives n i − k i. "
                + "The formula displays both filtered finite sums; subtraction is Nat.sub."),
            Node("treePoly", "The weighted tree Ising polynomial", PolynomialFormula(),
                "Section 2.2, printed p. 13 (PDF p. 14), equation (2.30), defines P by summing "
                + "over all splits and all spin states, with factors ρ(kᵢ,nᵢ), τ raised to the "
                + "number of opposite-spin edges, and x raised to the sum of spin-up vertex "
                + "masses. The source says: “where ρ(kᵢ,nᵢ) is a distribution that weights "
                + "different configurations.” The coefficient type is ℝ; Polynomial.C embeds "
                + "coefficients and Polynomial.X is the indeterminate. Spins have type V → Bool, "
                + "and true means spin up. The weight rho depends jointly on the whole split."),
            Node("claim", "Conjecture 1 with its binding conventions", ClaimFormula(),
                "Section 2.2, Conjecture 1, printed p. 14 (PDF p. 15): “" + Conjecture + "” "
                + "The displayed tree condition is NamedTreePhaseTransport.NamedSpanningTree src tgt Set.univ in Lean: all edges are selected, and its nonloop, distinct and isTree fields give precisely this condition. The orientation records which endpoint receives the split parameter. The convention uses n i ≥ 2, excluding the empty split sum at n i = 1, "
                + "and τ ∈ Set.Icc (−1) 1. The source's one-edge argument uses |τ| ≤ 1. "
                + "Every allowed joint weight is strictly positive. Polynomial.map along "
                + "algebraMap ℝ ℂ is the complex coefficient polynomial; IsRoot means its "
                + "evaluation is zero. The conclusion is the complex norm ‖z‖ = 1."),
            Node("result", "Conjecture 1 is refuted for joint weights", Seq(Neg, Sp, Op("claim")),
                "The witness is the path 0 → 1 ← 2 with totals (4,4), τ = −1, and weights "
                + "W₃₁ = ((1,1,1),(1,10,1),(1,1,31)), indexed by the two splits in {1,2,3}. "
                + "Its masses are (k₁,8−k₁−k₂,k₂). The same polynomial arises from "
                + "0 → 1 → 2 with the second weight index reversed. Exact state and split "
                + "enumeration gives 48−6X+8X²−62X³+24X⁴−62X⁵+8X⁶−6X⁷+48X⁸. "
                + "It equals 2(X−1)²X³q(X+X⁻¹), where q(y)=24y³+45y²−2y−26. "
                + "The cubic discriminant is −16404; Cubic.discr_eq_prod_three_roots "
                + "would make it a square, so q cannot split over ℝ. Algebraic "
                + "closure and descent of splitting give a nonreal complex root w. A root z "
                + "of z²−wz+1=0 is nonzero and satisfies w=z+z⁻¹. It is an octic root; "
                + "if ‖z‖=1, then z⁻¹=conj z, forcing w to be real. The product-weight "
                + "and physical-weight versions remain open.", true))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool theorem = false) => Describe.Lean(
            DescribeId.Create("quiver-tree-ising-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(DefinitionDsl.Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            theorem ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("fiol-martinezmontoya-riosfukelman-2020-tree-lee-yang"),
                ResolutionKind.Refuted) : null);

    private static Formula Id(string value) => F.Id(value);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Id(name)));
    private static Formula Q(string owner, string member) => Seq(Op(owner), Dot, Op(member));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] args)
    {
        var items = new List<Formula>();
        foreach (var arg in args) { if (items.Count > 0) items.Add(Comma); items.Add(arg); }
        return Seq(function, Parenthesized(Seq([.. items])));
    }
    private static Formula Var(string name, Formula type) => Parenthesized(Seq(Id(name), Colon, type));
    private static Formula Inst(string name, string type) =>
        Seq(OpenBracket, Call(name, Id(type)), CloseBracket);
    private static Formula Nat => Op("Nat");
    private static Formula Real => Op("Real");
    private static Formula Complex => Op("Complex");
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Var(name, type), Comma, body);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Seq(Op("fun"), Sp, Var(name, type), Mapsto, Sp, body);
    private static Formula Binders(bool vertices = true) => vertices
        ? Seq(Forall, Sp, Var("V", Op("Type")), Var("E", Op("Type")),
            Inst("Fintype", "V"), Inst("DecidableEq", "V"),
            Inst("Fintype", "E"), Inst("DecidableEq", "E"),
            Var("src", Arrow(Id("E"), Id("V"))), Var("tgt", Arrow(Id("E"), Id("V"))))
        : Seq(Forall, Sp, Var("E", Op("Type")), Inst("Fintype", "E"), Inst("DecidableEq", "E"));
    private static Formula Edge(string map) => Call(map, Id("i"));
    private static Formula Pair() => Call("s", Edge("src"), Edge("tgt"));
    private static Formula NatSub(Formula a, Formula b) => App(Q("Nat", "sub"), a, b);
    private static Formula Unfiltered(string type) =>
        Parenthesized(Seq(Q("Finset", "univ"), Colon, Call("Finset", Id(type))));
    private static Formula Filter(string type, string name, Formula condition) =>
        App(Seq(Unfiltered(type), Dot, Op("filter")), Fun(name, Id(type), condition));
    private static Formula SumOver(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Mem(Id(name), set)), body);
    private static Formula SplitsFormula() => Seq(Binders(false), Var("n", Arrow(Id("E"), Nat)), Comma,
        Eqn(Call("splits", Id("n")), App(Q("Fintype", "piFinset"), Fun("i", Id("E"),
            App(Q("Finset", "Icc"), D(1), NatSub(Call("n", Id("i")), D(1)))))));
    private static Formula MassFormula() => Seq(Binders(),
        Var("n", Arrow(Id("E"), Nat)), Var("k", Arrow(Id("E"), Nat)), Var("v", Id("V")), Comma,
        Eqn(Call("mass", Id("src"), Id("tgt"), Id("n"), Id("k"), Id("v")),
            Seq(Parenthesized(SumOver("i", Filter("E", "i", Eqn(Edge("src"), Id("v"))), Call("k", Id("i")))),
                Plus, Parenthesized(SumOver("i", Filter("E", "i", Eqn(Edge("tgt"), Id("v"))),
                    NatSub(Call("n", Id("i")), Call("k", Id("i"))))))));
    private static Formula PolynomialFormula()
    {
        var states = Arrow(Id("V"), Op("Bool"));
        var opposite = Filter("E", "i", new Formula.Relation(
            App(Id("st"), Edge("src")), FormulaRelationOperator.NotEqual, App(Id("st"), Edge("tgt"))));
        var count = Seq(Parenthesized(opposite), Dot, Op("card"));
        var exponent = SumOver("v", Filter("V", "v", Eqn(Call("st", Id("v")), Op("true"))),
            Call("mass", Id("src"), Id("tgt"), Id("n"), Id("k"), Id("v")));
        var stateSum = Seq(new Formula.Subscript(Sum, Seq(Id("st"), Colon, states)),
            App(Q("Polynomial", "C"), new Formula.Power(Id("tau"), count)), Cdot, Sp,
            new Formula.Power(Q("Polynomial", "X"), exponent));
        return Seq(Binders(), Var("n", Arrow(Id("E"), Nat)),
            Var("rho", Arrow(Parenthesized(Arrow(Id("E"), Nat)), Real)), Var("tau", Real), Comma,
            Eqn(Call("treePoly", Id("src"), Id("tgt"), Id("n"), Id("rho"), Id("tau")),
                SumOver("k", Call("splits", Id("n")), Seq(App(Q("Polynomial", "C"), Call("rho", Id("k"))),
                    Cdot, Sp, Parenthesized(stateSum)))));
    }
    private static Formula ClaimFormula()
    {
        var positiveTotals = All("i", Id("E"),
            new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, Call("n", Id("i"))));
        var positiveWeights = All("k", Arrow(Id("E"), Nat), Imp(Mem(Id("k"), Call("splits", Id("n"))),
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Call("rho", Id("k")))));
        var poly = Call("treePoly", Id("src"), Id("tgt"), Id("n"), Id("rho"), Id("tau"));
        var mapped = App(Seq(Parenthesized(poly), Dot, Op("map")), Call("algebraMap", Real, Complex));
        var root = App(Seq(Parenthesized(mapped), Dot, Op("IsRoot")), Id("z"));
        var norm = new Formula.Norm(Id("z"));
        var zeros = All("tau", Real, Imp(Mem(Id("tau"), App(Q("Set", "Icc"),
            Parenthesized(Seq(Minus, D(1), Colon, Real)), D(1))),
            All("z", Complex, Imp(root, Eqn(norm, D(1))))));
        var body = Seq(Binders(), Comma, Imp(Parenthesized(And(Parenthesized(All("i", Id("E"), new Formula.Relation(
                    Edge("src"), FormulaRelationOperator.NotEqual, Edge("tgt")))),
                And(App(Q("Function", "Injective"), Fun("i", Id("E"), Pair())),
                    Seq(Parenthesized(App(Q("SimpleGraph", "fromEdgeSet"),
                        App(Q("Set", "range"), Fun("i", Id("E"), Pair())))), Dot, Op("IsTree"))))),
            All("n", Arrow(Id("E"), Nat), Imp(Parenthesized(positiveTotals),
                All("rho", Arrow(Parenthesized(Arrow(Id("E"), Nat)), Real),
                    Imp(Parenthesized(positiveWeights), zeros))))));
        return Eqn(Op("claim"), Parenthesized(body));
    }
}
