using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class BubbleEigenstateDegeneracyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/StatisticalMechanics/mukherjeebanerjeesenguptasen2021fragmentation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A marked-gap count gives the closed formula for labelled bubble configurations on a periodic chain.",
        H("Counting bubble eigenstate configurations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("admissible"),
                DeclarationHandle.Create(Prefix + "Admissible"),
                H("Separated bubble centres"),
                StatementSource.FromAuthor(Disp(AdmissibleFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The sites are Fin L, numbered from zero to L minus one. Admissible L B means "
                    + "that the clockwise distance from a to b is at least five for every ordered "
                    + "pair of distinct centres in B. Thus the condition holds in both directions. "
                    + "A three-site X or Y unit around each centre then leaves at least two down "
                    + "spins between units. This is the separation condition in fragmentation_prb_v2.tex, "
                    + "lines 645–647 and 670–674, of arXiv:2106.14897v3. Empty and singleton sets "
                    + "satisfy the pairwise condition; the counting formula below assumes L at least five."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bubble-count"),
                DeclarationHandle.Create(Prefix + "bubbleCount"),
                H("The energy-resolved configuration count"),
                StatementSource.FromAuthor(Disp(BubbleCountFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each admissible centre set B, a subset x of B specifies the centres "
                    + "labelled X; the remaining centres are labelled Y. Its energy is twice the "
                    + "cardinality of x minus the cardinality of B, evaluated in the integers. "
                    + "The outer sum counts these labellings over all centre sets, with translations "
                    + "counted separately. The empty set contributes the vacuum at energy zero. "
                    + "This is the source's counting definition in fragmentation_prb_v2.tex, "
                    + "lines 670–674; the energies of the X and Y units are described at lines 636–644. "
                    + "Nat.cast in the formulas explicitly embeds each natural cardinality into the integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The closed counting formula"),
                StatementSource.FromAuthor(Disp(Equal(Local("claim"), Parenthesized(ClaimFormula())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural chain length L at least five and every integer energy E, "
                    + "the count is the vacuum contribution plus a sum over positive bubble numbers n "
                    + "up to the natural quotient L / 5. Each summand is the number of n-centre sets "
                    + "times the number of labellings at energy E. The latter vanishes unless n + E "
                    + "is even and the absolute value of E is at most n. Nat.div denotes natural "
                    + "division, Int.ediv integer division, and Int.emod integer remainder; Int.toNat "
                    + "converts the nonnegative label index to a natural number. "
                    + "The source states that a closed form for arbitrary L was not found "
                    + "in fragmentation_prb_v2.tex, lines 729–731. This formula answers that counting "
                    + "question for labelled configurations. It does not assert the Hamiltonian "
                    + "eigenstate property or count the other eigenstates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The marked-gap enumeration"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First, an admissible set B occupies five disjoint clockwise sites per "
                        + "centre: send a centre and an offset in Fin 5 to their sum modulo L. "
                        + "Equality of two images with different centres would contradict one of "
                        + "the two directed separation inequalities. For equal centres the offsets "
                        + "are equal. This injection gives 5 times the cardinality of B at most L.")),
                    Paragraph(Text(
                        "For a positive n with 5n at most L, consider boundary positions "
                        + "s₀ = 0, sₙ = L with successive differences at least five. Subtracting "
                        + "four from each successive difference gives n positive integers with "
                        + "sum L − 4n. Conversely, the partial sums of those integers plus four "
                        + "give the boundary positions. Successive differences recover every part, "
                        + "so these constructions are inverse. Clockwise separation can also be "
                        + "expressed by the natural representative of b − a in Fin L; this shows "
                        + "that translating all centres preserves admissibility.")),
                    Paragraph(Text(
                        "The first n boundary positions form an admissible n-element set "
                        + "containing zero. Their strict increase proves the cardinality and the "
                        + "forward separation inequalities; the terminal boundary L gives the "
                        + "inequalities across zero. Equal such sets have equal increasing "
                        + "enumerations, hence equal partial sums and equal positive parts. "
                        + "Conversely, enumerate any admissible n-element set containing zero "
                        + "in increasing order and append L. Consecutive centres and the final "
                        + "gap to zero have separation at least five; when the only centre is "
                        + "zero, the final gap is L, at least five. The successive differences "
                        + "therefore recover a unique positive composition of L − 4n.")),
                    Paragraph(Text(
                        "Now mark a centre a in a nonempty admissible set. Subtract a from "
                        + "every centre and use the preceding correspondence to obtain a positive "
                        + "composition. Conversely, translate the set constructed from a composition "
                        + "by a and mark a. The marked centre and increasing enumeration show that "
                        + "these operations are inverse. If c(L,n) denotes the number of admissible "
                        + "n-element sets, counting marked sets gives n c(L,n) on one side and "
                        + "L times the number of positive compositions on the other. Positive "
                        + "compositions of L − 4n into n parts number binomial(L − 4n − 1,n − 1). "
                        + "Thus n c(L,n) = L binomial(L − 4n − 1,n − 1), proving both the placement "
                        + "coefficient and the exactness of its natural division by n.")),
                    Paragraph(Text(
                        "For a fixed centre set B of size n, a subset x of size k has energy "
                        + "2k − n. Such subsets exist only when n + E is even and |E| is at most n. "
                        + "Under those conditions the energy equation is equivalent to "
                        + "k = Int.toNat((n + E) / 2); the subsets of that size number binomial(n,k). "
                        + "If either condition fails, the size bound k at most n contradicts the "
                        + "energy equation, so the filtered powerset is empty. At n = 0 the only "
                        + "centre set and its only subset are empty, giving one labelling exactly "
                        + "when E = 0.")),
                    Paragraph(Text(
                        "Finally, group the defining sum by the cardinality n of B. The packing "
                        + "bound restricts n to zero through L / 5. Separate the zero term, and "
                        + "use the label count, which is constant over sets of the same size, "
                        + "to factor each positive-size sum. Cast this natural-number equality "
                        + "into the integers, distribute the cast over sums and products, and "
                        + "substitute the placement coefficient for every n from one through "
                        + "L / 5. This gives the displayed formula for every L at least five "
                        + "and every integer E."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mukherjee-banerjee-sengupta-sen-2021-bubble-eigenstate-degeneracy"),
                    ResolutionKind.Proved)))));

    private static Formula AdmissibleFormula()
    {
        Formula a = X("a");
        Formula b = X("b");
        Formula av = At(Qualified("Fin", "val"), a);
        Formula bv = At(Qualified("Fin", "val"), b);
        Formula distance = If(Less(av, bv), Subtract(bv, av), Subtract(Add(X("L"), bv), av));
        Formula separation = All("a", FinOf(X("L")), Arrow(Member(a, X("B")),
            All("b", FinOf(X("L")), Arrow(Member(b, X("B")),
                Arrow(NotEqual(a, b), LE(D(5), distance))))));
        return All("L", Naturals(), All("B", CentreSets(),
            Equal(LocalCall("Admissible", X("L"), X("B")), Parenthesized(separation))));
    }

    private static Formula BubbleCountFormula()
    {
        Formula universe = Typed(Qualified("Finset", "univ"), FinsetOf(CentreSets()));
        Formula sets = At(Qualified("Finset", "filter"), LocalCall("Admissible", X("L")), universe);
        Formula energy = Equal(Subtract(Multiply(D(2), CastInteger(Card(X("x")))),
            CastInteger(Card(X("B")))), X("E"));
        Formula labels = Card(At(Qualified("Finset", "filter"), LambdaOf("x", CentreSets(), energy),
            At(Qualified("Finset", "powerset"), X("B"))));
        return All("L", Naturals(), All("E", Integers(),
            Equal(Typed(LocalCall("bubbleCount", X("L"), X("E")), Naturals()),
                SumOver("B", CentreSets(), sets, labels))));
    }

    private static Formula ClaimFormula()
    {
        Formula L = X("L");
        Formula E = X("E");
        Formula n = X("n");
        Formula size = Subtract(Subtract(L, Multiply(D(4), n)), D(1));
        Formula coefficient = CastInteger(At(Qualified("Nat", "div"),
            Multiply(L, At(Qualified("Nat", "choose"), size, Subtract(n, D(1)))), n));
        Formula parity = Equal(At(Qualified("Int", "emod"), Add(CastInteger(n), E), D(2)), D(0));
        Formula range = LE(new Formula.Absolute(E), CastInteger(n));
        Formula labelIndex = At(Qualified("Int", "toNat"),
            At(Qualified("Int", "ediv"), Add(CastInteger(n), E), D(2)));
        Formula labels = If(Conjunction(parity, range),
            CastInteger(At(Qualified("Nat", "choose"), n, labelIndex)), Typed(D(0), Integers()));
        Formula sizes = At(Qualified("Finset", "Icc"), D(1), At(Qualified("Nat", "div"), L, D(5)));
        Formula vacuum = If(Equal(E, D(0)), Typed(D(1), Integers()), Typed(D(0), Integers()));
        return All("L", Naturals(), Arrow(LE(D(5), L), All("E", Integers(),
            Equal(CastInteger(LocalCall("bubbleCount", L, E)),
                Add(vacuum, SumOver("n", Naturals(), sizes, Multiply(coefficient, labels)))))));
    }

    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "SpinChains",
        "BubbleEigenstateDegeneracy", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula X(string name) => F.Id(name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula FinsetOf(Formula type) => At(Qualified("Finset"), type);
    private static Formula CentreSets() => FinsetOf(FinOf(X("L")));
    private static Formula Card(Formula set) => At(Qualified("Finset", "card"), set);
    private static Formula CastInteger(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Integers());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Typed(X(name), type), InMacro, set)), Sp, Parenthesized(body));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), condition, yes, no);
    private static Formula Arrow(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
}
