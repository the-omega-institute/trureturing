using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class SwitchUselessConcatenationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/mitrabadhanighosh2023switch");
    private const string UselessQuote = "A useless channel is completely useless if under both C+ and C− it remains useless.";
    private const string ClaimQuote = "Concatenation of two completely useless channels is always completely useless.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two qubit channels are entanglement breaking before and after each switch branch, while the minus switch branch of their concatenation is not entanglement breaking.",
        H("Completely useless channels and concatenation"),
        Blocks(
            Node("IsKrausChannel", "Kraus normalization", ChannelFormula(),
                "Section II.A, PDF p. 2, gives the completeness identity for a channel's Kraus operators. Matrices have indices Fin 2 and complex entries; the sum is over the finite index type iota. conjTranspose is conjugate transpose.",
                DescribeRole.Definition, Lit()),
            Node("switchPlus", "The plus switch branch", SwitchFormula(false),
                "Section II.C, Eq. (8), PDF p. 4, gives the anticommutator branch. The Kraus operator for p is one half of K(p.1)K(p.2)+K(p.2)K(p.1). The two identical arguments of MatrixMap.of_kraus produce the map X ↦ ∑p Kp X Kpᴴ. The branch is completely positive and need not preserve trace.",
                DescribeRole.Definition, Lit()),
            Node("switchMinus", "The minus switch branch", SwitchFormula(true),
                "Section II.C, Eq. (8), PDF p. 4, gives the commutator branch. The Kraus operator for p is one half of K(p.1)K(p.2)−K(p.2)K(p.1). The two identical MatrixMap.of_kraus arguments give the coefficient one quarter in the map's action.",
                DescribeRole.Definition, Lit()),
            Node("CompletelyUseless", "Complete uselessness", UselessFormula(),
                "Section III.B, PDF p. 8: “" + UselessQuote + "” Uselessness means entanglement breaking. IsEB is the matrix-map predicate requiring separable output from every positive amplified input. The first conjunct includes the original channel; the other two include both switch branches.",
                DescribeRole.Definition, Lit()),
            Node("composeKraus", "Concatenated Kraus family", ComposeFormula(),
                "Section III.B uses concatenation Λ2 ◦ Λ1. The first family K acts first and L acts second, so the pair (i,j) has Kraus operator L(j)K(i). The product index type preserves all terms.",
                DescribeRole.Definition, Lit()),
            Node("claim", "Conjecture 1", ClaimFormula(),
                "Section III.B, Conjecture 1, PDF p. 8: “" + ClaimQuote + "” Both finite Kraus families are normalized qubit channels and completely useless in the sense above. The assertion ranges over every pair of finite index types and every such pair of families, and concludes complete uselessness of L after K.",
                DescribeRole.Definition, Lit()),
            Node("result", "Conjecture 1 is false", Disp(new Formula.Not(V("claim"))),
                "At eta = 24/25, take dephasing axes z and (4/5,0,3/5), mixed with depolarization. The Kraus weights are 7/10, 1/10, 1/10 and 7/10. Six eight-term positive measure-and-prepare decompositions establish entanglement breaking of the factors and all their switch branches. For the concatenation's minus branch, the partial transpose of the unnormalized Choi matrix has quadratic value −2185891/39062500 at (−2,−1,−1,2). Every separable matrix has positive semidefinite partial transpose, so this branch is not entanglement breaking. No statement about classical capacity or perfect deterministic transmission follows.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mitra-badhani-ghosh-2023-completely-useless-concatenation"),
                    ResolutionKind.Refuted)))));

    private static AssessedProvenance Lit() => AssessedProvenance.FromLiterature(Source);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("mbg-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Named(string name) => name.Contains('_')
        ? Seq(Operatorname, Grp(V(name.Split('_')[0])), Underscore, Grp(V(name.Split('_')[1])))
        : Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), C);
    private static Formula Family(string index) => new Formula.TypeArrow(V(index), Mat);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => Seq(left, Sp, Star, Sp, right);
    private static Formula Component(string name, byte index) => Seq(V(name), Dot, D(index));
    private static Formula Fun(string name, Formula type, Formula body) => Seq(Named("fun"), Sp,
        Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Finite(string index, Formula body) => Seq(OpenBracket, Call("Fintype", V(index)), CloseBracket, Sp, body);
    private static Formula OneFamily(Formula body) => All("iota", Named("Type"),
        Finite("iota", All("K", Family("iota"), body)));
    private static Formula PairType => Seq(V("iota"), Sp, Times, Sp, V("iota"));

    private static Formula ChannelFormula()
    {
        Formula ki = App(V("K"), V("i"));
        Formula sum = Seq(Sum, Underscore, Grp(V("i"), Colon, V("iota")), Sp,
            Parenthesized(Mul(App(Q("Matrix", "conjTranspose"), ki), ki)));
        return Disp(OneFamily(Iff(Call("IsKrausChannel", V("K")), Eqn(sum, D(1)))));
    }
    private static Formula SwitchFormula(bool minus)
    {
        Formula first = App(V("K"), Component("p", 1));
        Formula second = App(V("K"), Component("p", 2));
        Formula bracket = Seq(Mul(first, second), Sp, minus ? Minus : Plus, Sp, Mul(second, first));
        Formula half = Seq(Parenthesized(Seq(new Formula.Fraction(D(1), D(2)), Colon, C)), Sp,
            Cdot, Sp, Parenthesized(bracket));
        Formula family = Fun("p", PairType, half);
        return Disp(OneFamily(Eqn(Call(minus ? "switchMinus" : "switchPlus", V("K")),
            App(Q("MatrixMap", "of_kraus"), Parenthesized(family), Parenthesized(family)))));
    }
    private static Formula UselessFormula() => Disp(OneFamily(Iff(Call("CompletelyUseless", V("K")),
        And(Call("IsEB", App(Q("MatrixMap", "of_kraus"), V("K"), V("K"))),
            And(Call("IsEB", Call("switchPlus", V("K"))), Call("IsEB", Call("switchMinus", V("K"))))))));
    private static Formula ComposeFormula() => Disp(All("iota", Named("Type"), All("kappa", Named("Type"),
        All("L", Family("kappa"), All("K", Family("iota"),
            Eqn(Call("composeKraus", V("L"), V("K")), Fun("p", Seq(V("iota"), Sp, Times, Sp, V("kappa")),
                Mul(App(V("L"), Component("p", 2)), App(V("K"), Component("p", 1))))))))));
    private static Formula ClaimFormula() => Disp(Iff(V("claim"),
        All("iota", Named("Type"), All("kappa", Named("Type"), Finite("iota", Finite("kappa",
            All("K", Family("iota"), All("L", Family("kappa"),
                Imp(Call("IsKrausChannel", V("K")), Imp(Call("IsKrausChannel", V("L")),
                    Imp(Call("CompletelyUseless", V("K")), Imp(Call("CompletelyUseless", V("L")),
                        Call("CompletelyUseless", Call("composeKraus", V("L"), V("K")))))))))))))));
}
