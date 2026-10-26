using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class KageyInversionFirstLetterDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Combinatorics/Permutation/KageyInversionFirstLetter.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/kagey2021firstletter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For k<n, the mean first letter at inversion number k is M(n+1,k)/M(n,k).",
        H("First letters at a fixed inversion number"),
        Blocks(
            Paragraph(Text("Permutations are Equiv.Perm (Fin n), with positions numbered from zero. "
                + "The existing PSW.word sends a permutation pi to List.ofFn (fun i => (pi i).val + 1), "
                + "so its entries are the source's one-based letters. "
                + "D5.S1.Digit.Carry.ListInversions.inv counts strictly inverted pairs of positions. "
                + "Nat.cast in the formulas below has codomain Q, the rational field. "
                + "The function List.headD returns its default zero on an empty word; k<n implies n>0.")),
            Node("M", "Mahonian cardinalities", MahonianBody(),
                "Section 5.2, page 20: “where M(n, k), as above, is the number of permutations w ∈ S_n such that inv(w) = k.” "
                    + "The finite set contains each permutation once and retains exactly inversion number k.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("E", "The conditional mean", ExpectationBody(),
                "Section 5.2, page 20: “Because the expected value of the first letter is given by the weighted sum of the permutations with mah(w) = k divided by the number of such permutations, E[π(1) | π ∈ S_n, mah(π) = k] has a denominator that is (a factor of) M(n, k), the number of permutations of w ∈ S_n such that inv(w) = k.” "
                    + "Here mah is inv. Each first letter is cast to Q before summation, and M(n,k) is cast to Q before division. "
                    + "Rational division is total, including when the finite set is empty.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Kagey's Conjecture 5.1", Equal(V("claim"), Parenthesized(ClaimBody())),
                "Conjecture 5.1, page 20: “For fixed k and n > k, the expected value of the first letter of a permutation with a given number of inversions satisfies a rational function in n given by E[π(1) | π ∈ S_n, inv(π) = k] = M(n + 1, k)/M(n, k), where M(n, k), as above, is the number of permutations w ∈ S_n such that inv(w) = k.” "
                    + "Both k and n range over natural numbers; k<n is the complete hypothesis.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The first-letter expectation identity", ClaimBody(),
                "Deleting first letter j removes j−1 inversions. Two successive insertions with total inversion contribution t have t+1 choices when t≤k<n. "
                    + "Their count equals the first-letter weight. Thus the natural weighted numerator is M(n+1,k); casting that identity to Q proves the displayed equality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kagey-2021-inversion-first-letter-conjecture-5-1"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("kagey-inversion-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Root + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Rationals => Seq(Mathbb, Grp(V("Q")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(params string[] names)
    {
        var parts = new Formula[names.Length * 2 - 1];
        for (var i = 0; i < names.Length; i++)
        {
            parts[2 * i] = V(names[i]);
            if (i + 1 < names.Length) parts[2 * i + 1] = Dot;
        }
        return Seq(Operatorname, Grp(parts));
    }
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        Apply(Seq(Operatorname, Grp(V(name))), args);
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Parameters(Formula body) => All("n", Naturals, All("k", Naturals, body));
    private static Formula Permutations => Apply(Qualified("Equiv", "Perm"), Call("Fin", V("n")));
    private static Formula Word(Formula pi) => Apply(Qualified("PSW", "word"), pi);
    private static Formula Inversions(Formula pi) => Apply(
        Qualified("D5", "S1", "Digit", "Carry", "ListInversions", "inv"), Word(pi));
    private static Formula Lambda(string variable, Formula type, Formula body) => Parenthesized(Seq(
        Parenthesized(Seq(V(variable), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Slice() => Apply(Qualified("Finset", "filter"),
        Lambda("pi", Permutations, Equal(Inversions(V("pi")), V("k"))),
        Parenthesized(Seq(Qualified("Finset", "univ"), Colon, Sp, Call("Finset", Permutations))));
    private static Formula RationalCast(Formula value) => Parenthesized(Seq(
        Apply(Qualified("Nat", "cast"), value), Colon, Sp, Rationals));
    private static Formula MahonianBody() => Parameters(Equal(Call("M", V("n"), V("k")),
        Apply(Qualified("Finset", "card"), Slice())));
    private static Formula ExpectationBody()
    {
        var letter = Apply(Qualified("List", "headD"), Word(V("pi")), D(0));
        var numerator = Seq(new Formula.Subscript(Sum, Seq(V("pi"), Sp, InMacro, Sp, Slice())),
            Sp, RationalCast(letter));
        return Parameters(Equal(Call("E", V("n"), V("k")),
            new Formula.Fraction(numerator, RationalCast(Call("M", V("n"), V("k"))))));
    }
    private static Formula ClaimBody() => All("k", Naturals, All("n", Naturals,
        new Formula.Logic(new Formula.Relation(V("k"), FormulaRelationOperator.LessThan, V("n")),
            FormulaLogicOperator.Implies,
            Equal(Call("E", V("n"), V("k")), new Formula.Fraction(
                RationalCast(Call("M", Add(V("n"), D(1)), V("k"))),
                RationalCast(Call("M", V("n"), V("k"))))))));
}
