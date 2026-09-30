using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class KauffmanMukherjeeVojtechovskyRCliqueRefutationsDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/KauffmanMukherjeeVojtechovskyRCliqueRefutations.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/kauffman2026multivirtual");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite conjugation racks answer Problems 5.22 and 5.23 negatively and Problem 5.24 positively.",
        H("Maximal R-Cliques in Finite Connected Racks"),
        Blocks(
            LiteratureDefinition("kmv-rack", "Right racks", "IsRack", RackFormula(),
                "On printed page 13 the paper states: \"A magma (Q, ∗) is a right quasigroup "
                + "if for every x ∈ Q the right translation Rₓ is a permutation of Q.\" "
                + "It then states: \"A right quasigroup (Q, ∗) is a rack if it satisfies right "
                + "self-distributivity (x ∗ y) ∗ z = (x ∗ z) ∗ (y ∗ z).\" "
                + "Here mul(x,y) means x ∗ y. Bijective applies to x ↦ mul(x,y), "
                + "for every y; the order of the operands is the paper's right-hand convention."),
            LiteratureDefinition("kmv-r-commute", "Commuting right translations", "RCommute",
                CommuteFormula(),
                "Printed pages 17–18 state: \"Let ∼ be the binary relation on a right "
                + "quasigroup Q defined by a ∼ b if and only if [Ra, Rb] = 1.\" "
                + "\"If a ∼ b, we say that a and b R-commute.\" "
                + "For bijective right translations their commutator is the identity exactly "
                + "when the two compositions agree. The definition expresses that equality "
                + "at every x, without replacing it by commutation of group elements."),
            LiteratureDefinition("kmv-r-clique", "R-cliques", "IsRClique", CliqueFormula(),
                "Printed page 18 states: \"A subset C of a right quasigroup Q is an "
                + "R-clique if a ∼ b for every a, b ∈ C.\" "
                + "C is a Finset Q, representing a subset of a finite carrier. The "
                + "quantifiers include equal members as well as distinct members."),
            LiteratureDefinition("kmv-maximal-r-clique", "Inclusion maximality", "IsMaximalRClique",
                MaximalFormula(),
                "Printed page 19, Proposition 5.15, states: \"Let Q be a rack and let C "
                + "be a maximal R-clique of Q. Then C is a subrack of Q.\" Its proof uses "
                + "\"Since C is maximal, b ∈ C.\" Thus maximal means that every R-clique "
                + "D containing C equals C; it does not mean maximum cardinality."),
            LiteratureDefinition("kmv-connected", "Connected racks", "Connected", ConnectedFormula(),
                "Printed page 17 states: \"Recall that a rack Q is connected if the "
                + "permutation group Mltr(Q) acts transitively on Q.\" Connected is encoded "
                + "by a positive finite word l of right translations carrying each x to each y. "
                + "foldl(mul,x,l) denotes l.foldl mul x: starting at x, apply the right "
                + "translations listed in l in order. On a finite rack each right translation "
                + "is a finite-order permutation, so its inverse is a positive power. "
                + "Consequently positive-word reachability is precisely transitivity of the "
                + "generated right multiplication group in the finite-rack hypotheses below."),
            LiteratureDefinition("kmv-problem-equal-size", "Problem 5.22", "claim22", ClaimFormula(22),
                "Printed page 21: \"Problem 5.22. Do all maximal R-cliques in a finite "
                + "connected rack have the same size?\" claim22 is the universal affirmative "
                + "answer, with two inclusion-maximal finsets C and D and their Finset.card values."),
            LiteratureDefinition("kmv-problem-partition", "Problem 5.23", "claim23", ClaimFormula(23),
                "Printed page 21: \"Problem 5.23. Do maximal R-cliques in a finite connected "
                + "rack Q partition Q?\" claim23 is the universal affirmative answer. It "
                + "requires every x to belong to a maximal R-clique, and any two maximal "
                + "R-cliques with nonempty intersection to be equal. Both conjuncts are included."),
            LiteratureDefinition("kmv-problem-divisibility", "Problem 5.24", "claim24", ClaimFormula(24),
                "Printed page 21: \"Problem 5.24. Does there exist a finite connected rack Q "
                + "and a maximal R-clique C of Q such that |C| does not divide |Q|?\" "
                + "claim24 is the negation of this existence assertion: every maximal R-clique "
                + "in every finite connected rack has cardinality dividing the carrier cardinality. "
                + "Refuting claim24 answers the printed existence question Yes. FinsetCard(C) means C.card, FintypeCard(Q) means Fintype.card Q, and FinsetInter(C,D) means C ∩ D. All three claims "
                + "quantify over Q : Type with Fintype Q and DecidableEq Q and over every binary "
                + "operation mul; these structures impose no additional finite-rack restriction."),
            RepositoryTheorem("kmv-equal-size-refutation", "Unequal maximal R-cliques", "result22",
                ResultFormula(22),
                "Use the conjugation rack of the 105 fixed-point-free involutions in S₈, "
                + "x ∗ y = y⁻¹xy. On points 0 through 7, the seven translations tₐ(x) = x XOR a "
                + "for a = 1 through 7 form a maximal R-clique. The nine permutations pₐᵦ "
                + "for a,b = 1,2,3, acting by x XOR a on the lower block and by "
                + "4 + ((x−4) XOR b) on the upper block, form another maximal R-clique. "
                + "Their cardinalities 7 and 9 differ. Fin 105 indexes the literal permutation "
                + "vectors and conjugation table; positive right-translation words certify connectedness.",
                "kauffman-mukherjee-vojtechovsky-2025-maximal-r-clique-equal-size-refutation"),
            RepositoryTheorem("kmv-partition-refutation", "Overlapping maximal R-cliques", "result23",
                ResultFormula(23),
                "Use the conjugation rack of the ten transpositions in S₅. The two maximal "
                + "R-cliques {(1 2),(3 4)} and {(1 2),(3 5)} are distinct and intersect in "
                + "(1 2). Fin 10 indexes the literal permutation vectors and conjugation table. "
                + "The rack is connected, so these two subsets refute the partition assertion.",
                "kauffman-mukherjee-vojtechovsky-2025-maximal-r-clique-partition-refutation"),
            RepositoryTheorem("kmv-divisibility-refutation", "A size that does not divide the carrier size",
                "result24", ResultFormula(24),
                "Use the conjugation rack of the 70 three-cycles in S₇. The subset "
                + "{(1 2 3),(1 3 2),(4 5 6),(4 6 5)} is a maximal R-clique of size 4, "
                + "and 4 does not divide 70. Fin 70 indexes the literal permutation vectors "
                + "and conjugation table. Positive right-translation words certify connectedness. "
                + "This refutes universal divisibility and supplies the existence requested in Problem 5.24.",
                "kauffman-mukherjee-vojtechovsky-2025-maximal-r-clique-divisibility-refutation"))));

    private static DocumentBlock LiteratureDefinition(
        string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock RepositoryTheorem(
        string id, string title, string declaration, Formula formula, string prose,
        string problemSlug) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create(problemSlug),
                ResolutionKind.Refuted));

    private static Formula Q() => F.Id("Q");
    private static Formula Mul() => F.Id("mul");
    private static Formula Finsets() => Call("Finset", Q());
    private static Formula BinaryType() => new Formula.TypeArrow(Q(), new Formula.TypeArrow(Q(), Q()));
    private static Formula Context(Formula body) =>
        All("Q", F.Id("Type"), All("mul", BinaryType(), body));
    private static Formula RackFormula()
    {
        var translations = All("y", Q(), Call("Bijective",
            Parenthesized(Seq(LambdaLower, Sp, F.Id("x"), Comma, Sp,
                Call("mul", F.Id("x"), F.Id("y"))))));
        var law = All("x", Q(), All("y", Q(), All("z", Q(),
            Equal(Call("mul", Call("mul", F.Id("x"), F.Id("y")), F.Id("z")),
                Call("mul", Call("mul", F.Id("x"), F.Id("z")),
                    Call("mul", F.Id("y"), F.Id("z")))))));
        return Disp(Context(Iff(Call("IsRack", Mul()), And(translations, law))));
    }
    private static Formula CommuteFormula() => Disp(Context(All("a", Q(), All("b", Q(),
        Iff(Call("RCommute", Mul(), F.Id("a"), F.Id("b")), All("x", Q(),
            Equal(Call("mul", Call("mul", F.Id("x"), F.Id("a")), F.Id("b")),
                Call("mul", Call("mul", F.Id("x"), F.Id("b")), F.Id("a")))))))));
    private static Formula CliqueFormula()
    {
        var c = F.Id("C");
        var a = F.Id("a");
        var b = F.Id("b");
        var pairs = All("a", Q(), Implies(Member(a, c),
            All("b", Q(), Implies(Member(b, c), Call("RCommute", Mul(), a, b)))));
        return Disp(Context(All("C", Finsets(), Iff(Call("IsRClique", Mul(), c), pairs))));
    }
    private static Formula MaximalFormula() => Disp(Context(All("C", Finsets(),
        Iff(Maximal(F.Id("C")), And(Call("IsRClique", Mul(), F.Id("C")),
            All("D", Finsets(), Implies(Call("IsRClique", Mul(), F.Id("D")),
                Implies(Rel(F.Id("C"), FormulaRelationOperator.SubsetOf, F.Id("D")),
                    Equal(F.Id("D"), F.Id("C"))))))))));
    private static Formula ConnectedFormula() => Disp(Context(Iff(Call("Connected", Mul()),
        All("x", Q(), All("y", Q(), ExistsOne("l", Call("List", Q()),
            Equal(Call("foldl", Mul(), F.Id("x"), F.Id("l")), F.Id("y"))))))));
    private static Formula ClaimFormula(int number)
    {
        var c = F.Id("C");
        var d = F.Id("D");
        Formula conclusion;
        if (number == 22)
            conclusion = All("C", Finsets(), All("D", Finsets(),
                Implies(Maximal(c), Implies(Maximal(d), Equal(Card(c), Card(d))))));
        else if (number == 23)
            conclusion = And(All("x", Q(), ExistsOne("C", Finsets(),
                    And(Maximal(c), Member(F.Id("x"), c)))),
                All("C", Finsets(), All("D", Finsets(), Implies(Maximal(c),
                    Implies(Maximal(d), Implies(Call("Nonempty", Call("FinsetInter", c, d)), Equal(c, d)))))));
        else
            conclusion = All("C", Finsets(), Implies(Maximal(c),
                Rel(Card(c), FormulaRelationOperator.Divides, Call("FintypeCard", Q()))));
        var universal = All("Q", F.Id("Type"), Implies(Call("Fintype", Q()),
            Implies(Call("DecidableEq", Q()), All("mul", BinaryType(),
                Implies(Call("IsRack", Mul()), Implies(Call("Connected", Mul()), conclusion))))));
        return Disp(Iff(Claim(number), universal));
    }
    private static Formula Claim(int number) => Seq(F.Id("claim"), number switch
    {
        22 => D(2, 2), 23 => D(2, 3), _ => D(2, 4)
    });
    private static Formula ResultFormula(int number) => Disp(new Formula.Not(Claim(number)));
    private static Formula Maximal(Formula c) => Call("IsMaximalRClique", Mul(), c);
    private static Formula Card(Formula c) => Call("FinsetCard", c);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ExistsOne(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Member(Formula left, Formula right) => Rel(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
