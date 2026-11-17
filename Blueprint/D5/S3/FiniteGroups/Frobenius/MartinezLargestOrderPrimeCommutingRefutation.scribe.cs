using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class MartinezLargestOrderPrimeCommutingRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation";
    private static readonly LibraryNoteRef Martinez =
        LibraryNoteRef.Create("D5/L/FiniteGroups/martinez2024pielements");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dihedral product has fixed-element pi-commuting fraction one quarter despite a large prime in the element order.",
        H("The largest-order-prime commuting question"),
        Blocks(
            Node("pi-elements", "piElements", "Elements with prime support in pi", PiElementsFormula(),
                AssessedProvenance.FromLiterature(Martinez),
                "Introduction, printed pages 1–2: “where G_π is the set of all π-elements in G.” "
                + "An element belongs to this set when every prime divisor of its order belongs to pi. "
                + "The identity is included because its order is one. Type* allows an arbitrary carrier universe."),
            Node("pi-subgroup", "isPiSubgroup", "Subgroups with prime support in pi", PiSubgroupFormula(),
                AssessedProvenance.FromLiterature(Martinez),
                "A pi-subgroup has no prime divisor of its cardinality outside pi. This is the standard "
                + "finite-group meaning of the pi-subgroups used in Oπ(G); the source does not separately define this term."),
            Node("pi-core", "piCore", "The normal pi-core", PiCoreFormula(),
                AssessedProvenance.FromLiterature(Martinez),
                "The normal pi-core Oπ(G) is represented as the supremum, in the complete lattice of subgroups, "
                + "of the normal pi-subgroups. The family includes the trivial subgroup. The source uses "
                + "the standard normal pi-core in Theorem A on printed page 2."),
            Node("fixed-fraction", "commutingFraction", "The fixed-element fraction", FractionFormula(),
                AssessedProvenance.FromLiterature(Martinez),
                "Section 2, printed page 4: “It is important to remark that given x, a π-element of G, "
                + "the proportion |C_G(x)_π|/|G_π| is exactly the fixed point ratio of x, "
                + "where we consider the action of G on G_π by conjugation.” "
                + "The numerator counts pi-elements in the singleton centralizer. Both finite cardinalities "
                + "are cast to the rationals before division. The denominator includes the identity and is positive."),
            Node("largest-prime-claim", "claim", "The source's largest-prime question",
                Equal(F.Id("claim"), Parenthesized(ClaimBody())),
                AssessedProvenance.FromLiterature(Martinez),
                "Section 4, printed page 16, immediately after Theorem 4.7: “As we mentioned in the Introduction, "
                + "it remains as an open question whether Theorem A holds with ≤ 1/q, where q is the largest "
                + "prime dividing o(x).” Theorem A, printed page 2: “Let G be a finite group, let π be a set "
                + "of primes and let p be the smallest prime in π. If x ∈ G_π∖O_π(G), then "
                + "|C_G(x)_π|/|G_π| ≤ 1/p.” "
                + "The proposition replaces that last bound by the reciprocal of the largest prime divisor of "
                + "orderOf x. It quantifies over actual finite groups with carrier G : Type and arbitrary nonempty "
                + "sets pi of primes. Existence of the largest prime divisor is included in the conclusion."),
            Describe.Lean(DescribeId.Create("martinez-largest-prime-refuted"),
                DeclarationHandle.Create(Module + ".result"), H("Refutation by a dihedral product"),
                StatementSource.FromAuthor(Disp(Not(ClaimBody()))),
                AssessedProvenance.FromRepo(Martinez),
                Blocks(Paragraph(Text(
                    "Take G = DihedralGroup 3 × DihedralGroup 5, pi = {2,5}, and x = (DihedralGroup.sr 0, "
                    + "DihedralGroup.r 1). The element has order ten and lies outside the normal pi-core. "
                    + "There are forty pi-elements and ten centralizing pi-elements, so the fraction is one quarter, "
                    + "strictly greater than one fifth. The largest prime divisor of ten is five.")),
                    Paragraph(Text(
                    "More generally, for every prime q ≥ 5, the same construction in DihedralGroup 3 × DihedralGroup q "
                    + "has pi-core 1 × DihedralGroup q, pi-element count 8q and centralizing pi-element count 2q. "
                    + "The first-coordinate reflection keeps x outside the pi-core while its second coordinate contributes "
                    + "q to its order. The fraction remains one quarter. The source's smallest-prime bound in Theorem A "
                    + "is not refuted; the separate smallest-prime-dividing-order question and the restricted Theorem B "
                    + "are not proved here."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("op-martinez2307"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string name, string title, Formula formula,
        AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create("martinez-" + id), DeclarationHandle.Create(Module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula G => F.Id("G");
    private static Formula P => Pi;
    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RatType => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula SetNat => Call("Set", NatType);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsQ(Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("q"), NatType, body);
    private static Formula AllPi(Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(P, Sp, Colon, Sp, SetNat)), Comma, Sp, body);
    private static Formula Instances(Formula body) => Seq(
        OpenBracket, Call("Group", G), CloseBracket, Sp,
        OpenBracket, Call("Finite", G), CloseBracket, Comma, Sp, body);
    private static Formula OverGroup(Formula body) =>
        All("G", Seq(F.Id("Type"), Star), Instances(body));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Not(Formula body) => Seq(Neg, Sp, Parenthesized(body));
    private static Formula Prime(Formula p) => App(Q("Nat", "Prime"), p);
    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula PiMembers => Call("piElements", G, P);
    private static Formula Card(Formula type) => App(Q("Nat", "card"), type);
    private static Formula Rational(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, RatType));
    private static Formula SetOf(string name, Formula type, Formula body, bool subtype = false) =>
        Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp,
            subtype ? Seq(Slash, Slash) : Bar, Sp, body, CloseBrace);
    private static Formula PrimeSupport(Formula number) =>
        All("p", NatType, Imp(Prime(F.Id("p")),
            Imp(Divides(F.Id("p"), number), Member(F.Id("p"), P))));

    private static Formula PiElementsFormula() => OverGroup(AllPi(Equal(PiMembers,
        SetOf("x", G, PrimeSupport(Call("orderOf", F.Id("x")))))));

    private static Formula PiSubgroupFormula() => OverGroup(AllPi(All("N", Call("Subgroup", G),
        Equal(Call("isPiSubgroup", P, F.Id("N")), PrimeSupport(Card(F.Id("N")))))));

    private static Formula PiCoreFormula() => OverGroup(AllPi(Equal(Call("piCore", G, P),
        Call("sSup", SetOf("N", Call("Subgroup", G),
            And(App(Q("Subgroup", "Normal"), F.Id("N")), Call("isPiSubgroup", P, F.Id("N"))))))));

    private static Formula FractionFormula()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var singleton = Parenthesized(Seq(OpenBrace, x, CloseBrace, Sp, Colon, Sp, Call("Set", G)));
        var numerator = Card(SetOf("y", G,
            And(Member(y, PiMembers), Member(y, App(Q("Subgroup", "centralizer"), singleton))), true));
        var denominator = Card(SetOf("y", G, Member(y, PiMembers), true));
        return OverGroup(AllPi(All("x", G, Equal(Call("commutingFraction", G, P, x),
            new Formula.Fraction(Rational(numerator), Rational(denominator))))));
    }

    private static Formula ClaimBody()
    {
        var x = F.Id("x");
        var p = F.Id("p");
        var q = F.Id("q");
        var order = Call("orderOf", x);
        var maximum = All("p", NatType, Imp(Prime(p), Imp(Divides(p, order),
            new Formula.Relation(p, FormulaRelationOperator.LessThanOrEqual, q))));
        var bound = new Formula.Relation(Call("commutingFraction", G, P, x),
            FormulaRelationOperator.LessThanOrEqual, new Formula.Fraction(D(1), Rational(q)));
        var conclusion = ExistsQ(And(Prime(q), And(Divides(q, order), And(maximum, bound))));
        var atX = All("x", G, Imp(Member(x, PiMembers),
            Imp(Not(Member(x, Call("piCore", G, P))), conclusion)));
        var primes = All("p", NatType, Imp(Member(p, P), Prime(p)));
        return All("G", F.Id("Type"), Instances(AllPi(
            Imp(primes, Imp(App(Q("Set", "Nonempty"), P), atX)))));
    }
}
