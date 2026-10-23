using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class SymmetricGHZResourceLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/deoliveira2024symmetricghz");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For 2 ≤ k ≤ n, every symmetric integer lift of C^k_n requires a selected size j with k / 2 ≤ j and j ≤ n - k / 2.",
        H("A lower bound for symmetric GHZ resources"), Blocks(
            Paragraph(Text(
                "The input type is Fin n → Bool. Natural numbers start at zero. "
                + "Annotations with ℤ or ℝ denote the corresponding casts of natural or integer values. "
                + "Nat.div is natural-number division and Int.emod is the nonnegative remainder. "
                + "The exponent in claim is an integer, so for k=1 it is −1. "
                + "All local names below belong to D5.S3.Quantum.Contextuality.SymmetricGHZResourceLowerBound.")),
            Node("layer", "All parity bits of a fixed size", "layer", LayerFormula(),
                "Definition 16, pp. 26–27: “A symmetric measurement assignment for an NMQC⊕ computation "
                + "is composed of a set of linear functions L, which is limited to having either all parity bases "
                + "of a specific size or none,” followed by Equation (71). The layer is the sum over all "
                + "subsets of the specified size, as in Equation (72).",
                AssessedProvenance.FromLiterature(Source)),
            Node("csf", "The complete symmetric Boolean function", "csf", CsfFormula(),
                "Definition 5, p. 13: “The complete symmetric function (CSF) of dimension k, "
                + "Cᵏ(x) : {0, 1}ⁿ → {0, 1} is defined as the sum, modulo 2, of all terms with degree "
                + "equal to k, i.e.” Equation (27) counts exactly the k-element subsets whose inputs are all true.",
                AssessedProvenance.FromLiterature(Source)),
            Node("computes", "Integer lifts with one coefficient per size", "ComputesSym", ComputesFormula(),
                "Definition 15, p. 26: “The minimum number of qubits necessary for the deterministic "
                + "evaluation of a Boolean function f : {0, 1}ⁿ → {0, 1} in the NMQC⊕ model can be defined "
                + "as the sparsest multi-linear polynomial equivalent to the function, i.e.” Equation (70) "
                + "requires an integer lift modulo two. Definition 16 continues on p. 27: “and the corresponding "
                + "dichotomic measurement operators, which have to be equal for all parity bases of the same size, "
                + "i.e.” Together with Equation (72), this gives a real coefficient a i for each size i∈T. "
                + "Selected sizes lie between one and n. There is no constant term.",
                AssessedProvenance.FromLiterature(Source)),
            Node("qubits", "The number of selected parity measurements", "qubits", QubitsFormula(),
                "Equations (71)–(72) select every parity basis of each size in T. There are Nat.choose n i "
                + "subsets of size i, and one qubit for each basis. The sum counts every selected layer, "
                + "including a layer whose coefficient is zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 2 as a quantified asymptotic bound", "claim", ClaimFormula(),
                "Section 4.2, Conjecture 2, p. 27: “The number of qubits in a GHZ state necessary for the "
                + "deterministic evaluation of a complete symmetric function Cᵏ, of constant degree k, with an "
                + "n bit input string and a symmetric measurement assignment, scales as Ω(n^{⌊k/2⌋−1}).” "
                + "For each k≥1, the positive constant c and threshold N may depend on k, and work uniformly for all "
                + "larger input sizes, all selected size sets and all real coefficient functions that satisfy ComputesSym.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("symmetric-ghz-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The asymptotic lower bound"), StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text(
                        "For 2≤k≤n, put m=⌊k/2⌋ and r=k−2m. The signed layer polynomial at Hamming weight w is "
                        + "(1−X)^w(1+X)^(n−w). The coefficients d_u=(−1)^(m−u) Nat.choose m u, "
                        + "for 0≤u≤m, at weights 2u+r, have sum zero. Their weighted sum of these polynomials is "
                        + "(−4)^m X^m (1−X)^r (1+X)^(n−2m−r). Its coefficients vanish below m "
                        + "and above n−m, so the same weighted sum annihilates every parity layer "
                        + "outside that interval. An integer lift of csf is even at all the earlier "
                        + "weights and odd at weight k; its weighted sum is therefore odd. "
                        + "Consequently some selected layer lies between m and n−m, and its cost "
                        + "is at least Nat.choose n m. This proves the finite bound for 2≤k≤n. "
                        + "For n≥2k, the binomial lower estimate n^m/(2^m m!) gives the requested asymptotic "
                        + "bound with c=1/(2^m m!) and N=2k. For k=1 and n≥1, a computing assignment has a nonempty selected size set, so it gives "
                        + "at least one qubit, which bounds n^(−1) for n≥1."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("de-oliveira-barbosa-galvao-2024-symmetric-ghz-resource"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("symmetric-ghz-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula LayerFormula() => All("n", N(), All("i", N(), All("x", Input(),
        Equal(LocalCall("layer", X("n"), X("i"), X("x")), SumIn("S", FinsetOf(FinOf(X("n"))),
            SubsetsOfSize(X("i")),
            Call("ite", Call("Odd", Call("Finset", "card",
                Filter(X("S"), "l", FinOf(X("n")), Equal(App(X("x"), X("l")), Q("true"))))),
                Typed(D(1), Z()), Typed(D(0), Z())))))));

    private static Formula CsfFormula()
    {
        var selected = Filter(AllSubsets(), "S", FinsetOf(FinOf(X("n"))),
            And(Equal(Call("Finset", "card", X("S")), X("k")),
                All("l", FinOf(X("n")), ImpliesF(Member(X("l"), X("S")),
                    Equal(App(X("x"), X("l")), Q("true"))))));
        return All("n", N(), All("k", N(), All("x", Input(),
            Equal(LocalCall("csf", X("n"), X("k"), X("x")),
                Call("Int", "emod", Typed(Call("Finset", "card", selected), Z()), D(2))))));
    }

    private static Formula ComputesFormula()
    {
        var sizes = All("i", N(), ImpliesF(Member(X("i"), X("T")),
            And(LE(D(1), X("i")), LE(X("i"), X("n")))));
        var lift = All("x", Input(), Ex("z", Z(),
            And(Equal(SumIn("i", N(), X("T"), Multiply(App(X("a"), X("i")),
                    Typed(LocalCall("layer", X("n"), X("i"), X("x")), R()))), Typed(X("z"), R())),
                Equal(Call("Int", "emod", X("z"), D(2)), LocalCall("csf", X("n"), X("k"), X("x"))))));
        return All("n", N(), All("k", N(), All("T", FinsetOf(N()), All("a", Arrow(N(), R()),
            IffF(LocalCall("ComputesSym", X("n"), X("k"), X("T"), X("a")), And(sizes, lift))))));
    }

    private static Formula QubitsFormula() => All("n", N(), All("T", FinsetOf(N()),
        Equal(LocalCall("qubits", X("n"), X("T")), SumIn("i", N(), X("T"),
            Call("Nat", "choose", X("n"), X("i"))))));

    private static Formula ClaimFormula()
    {
        var exponent = Subtract(Typed(Call("Nat", "div", X("k"), D(2)), Z()), D(1));
        var bound = LE(Multiply(X("c"), new Formula.Power(Typed(X("n"), R()), exponent)),
            Typed(LocalCall("qubits", X("n"), X("T")), R()));
        var conclusion = All("n", N(),
            ImpliesF(LE(X("N"), X("n")),
                All("T", FinsetOf(N()),
                    All("a", Arrow(N(), R()),
                        ImpliesF(
                            LocalCall("ComputesSym", X("n"), X("k"), X("T"), X("a")),
                            bound)))));
        var threshold = Ex("N", N(), conclusion);
        var constant = Ex("c", R(), And(Less(D(0), X("c")), threshold));
        return IffF(Local("claim"), All("k", N(), ImpliesF(LE(D(1), X("k")), constant)));
    }

    private static Formula SubsetsOfSize(Formula i) => Filter(AllSubsets(), "S", FinsetOf(FinOf(X("n"))),
        Equal(Call("Finset", "card", X("S")), i));
    private static Formula AllSubsets() => Typed(Q("Finset", "univ"), FinsetOf(FinsetOf(FinOf(X("n")))));
    private static Formula Filter(Formula s, string name, Formula type, Formula body) =>
        Call("Finset", "filter", LambdaOf(name, type, body), s);
    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Q("D5", "S3", "Quantum", "Contextuality", "SymmetricGHZResourceLowerBound", name);
    private static Formula LocalCall(string name, params Formula[] args) => App(Local(name), args);
    private static Formula Q(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula Call(string owner, string name, params Formula[] args) => App(Q(owner, name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula Z() => Seq(Mathbb, Grp(X("Z")));
    private static Formula R() => Seq(Mathbb, Grp(X("R")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula FinsetOf(Formula type) => Call("Finset", type);
    private static Formula Input() => Arrow(FinOf(X("n")), Q("Bool"));
    private static Formula Arrow(Formula left, Formula right) => Parenthesized(new Formula.TypeArrow(left, right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumIn(string name, Formula type, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(Typed(X(name), type), set)), Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula ImpliesF(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffF(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
