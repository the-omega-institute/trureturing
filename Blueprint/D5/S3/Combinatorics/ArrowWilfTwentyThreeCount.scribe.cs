using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfTwentyThreeCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfTwentyThreeCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower derangement prefix and a decreasing upper skeleton enumerate avoiders with a prescribed smallest fixed point.",
        H("Decorated Objects for the Second Pattern"),
        Blocks(
            Node("twenty-three-data", "Decorated data with a smallest fixed point", "TwentyThreeData", "Choose r lower values R, a word rho on R, a no-fixed-point word sigma on the remaining lower values, and a weak gap composition of r indexed by the values above m.", DescribeRole.Definition),
            Node("upper-descending", "The decreasing upper skeleton", "upperDescending", "The upper word is n down through m plus one in decreasing order.", DescribeRole.Definition),
            Node("upper-gap-sizes", "Read upper gaps in skeleton order", "upperGapSizes", "The list reads each labelled upper gap in the order n down through m plus one.", DescribeRole.Definition),
            Node("upper-gap-total", "Length and sum of upper gaps", "upperGapSizes_length_sum", "The upper gap list has n minus m entries, and their sum is r.", DescribeRole.Theorem),
            Node("twenty-three-list", "The decorated output word", "twentyThreeList", "Concatenate the no-fixed lower prefix, m, and the decreasing upper skeleton with consecutive blocks of rho inserted after its entries.", DescribeRole.Definition),
            Node("twenty-three-permutation", "The output uses each value once", "twentyThreeList_perm", "When one at most m at most n, every decorated output permutes the standard support from one through n.", DescribeRole.Theorem),
            Node("twenty-three-fixed-m", "The distinguished value is fixed", "twentyThreeList_fixed_m", "For m strictly below n, hat fixes m in the decorated output.", DescribeRole.Theorem),
            Node("append-greater-syntax", "A larger suffix preserves singleton syntax", "fixedSyntax_append_greater_iff", "For g below m appearing in a prefix u, appending m and a suffix leaves FixedSyntax g equivalent to its status in u.", DescribeRole.Theorem),
            Node("append-greater-member", "A lower singleton lies in the prefix", "fixedSyntax_append_greater_mem", "If g below m has singleton syntax in a word split before m, then g occurs in the prefix before m.", DescribeRole.Theorem),
            Node("no-lower-fixed", "No smaller value is fixed", "twentyThreeList_no_lower_fixed", "No value g below m occurring in a decorated output is fixed by hat.", DescribeRole.Theorem),
            Node("upper-filter", "Recovering the upper skeleton", "filter_twentyThreeList_upper", "Filtering a decorated output for values greater than m yields the decreasing upper skeleton.", DescribeRole.Theorem),
            Node("upper-pair-order", "Upper entries cannot increase", "no_increasing_upper_pair", "If m is below a and a is below b, the ordered pair a,b is not a sublist of a decorated output.", DescribeRole.Theorem),
            Node("twenty-three-avoids", "The decorated output avoids the second pattern", "twentyThreeList_avoids", "For positive m below n, the decorated word does not contain (23; 1 to 1).", DescribeRole.Theorem),
            Node("twenty-three-avoider", "The output as an avoiding word", "twentyThreeAvoider", "Package the decorated list as a word on the standard support that avoids the second pattern.", DescribeRole.Definition),
            Node("twenty-three-data-equivalence", "The independent decorated choices", "twentyThreeDataEquiv", "The data type is equivalent to the dependent sum over R of a word on R, a no-fixed-point word on its lower complement, and an upper-labelled gap vector.", DescribeRole.Definition),
            Node("twenty-three-data-cardinality", "The decorated summand count", "card_twentyThreeData", CountFormula(), "The cardinality is choose(m minus one,r) times choose(n minus m plus r minus one,r) times r factorial times the derangement number at m minus one minus r.", DescribeRole.Theorem),
            Node("top-avoiders", "The exceptional top fiber", "TopAvoiders", "These avoiding words fix n and have no hat-fixed value below n.", DescribeRole.Definition),
            Node("top-avoiders-equivalence", "The top fiber has an exact fixed set", "topAvoidersEquiv", "For positive n, the exceptional top fiber is equivalent to words whose exact hat-fixed set is the singleton containing n.", DescribeRole.Definition),
            Node("interleaving-decomposition", "Decomposing an arbitrary word", "interleave_decompose", "Any word splits into an initial filler block and later filler blocks after the entries satisfying a Boolean skeleton predicate.", DescribeRole.Theorem),
            Node("forced-upper-order", "Avoidance forces the upper order", "upper_filter_eq_of_avoids", "For an avoiding word fixed at m, filtering values above m gives the unique decreasing upper skeleton.", DescribeRole.Theorem),
            Node("split-at-member", "Splitting at an occurring value", "split_at_member", "Every list containing x can be written as a prefix followed by x and a suffix.", DescribeRole.Theorem),
            Node("fixed-syntax-split", "Structure around a singleton block", "fixedSyntax_split", "When m is absent from a prefix and has singleton syntax at the following position, all prefix entries are below m and the suffix is empty or begins above m.", DescribeRole.Theorem),
            Node("headed-interleaving", "No initial filler before a skeleton head", "interleave_decompose_head", "If the first entry satisfies the skeleton predicate, the interleaving decomposition has no initial filler block.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula CountFormula()
    {
        var n = F.Id("n"); var m = F.Id("m"); var r = F.Id("r");
        var left = Call("card", Call("TwentyThreeData", n, m, r));
        var right = Mul(Call("choose", Sub(m, D(1)), r),
            Call("choose", Sub(Add(Sub(n, m), r), D(1)), r),
            Call("factorial", r), Call("numDerangements", Sub(Sub(m, D(1)), r)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("n"), Bound("m"), Bound("r")],
            new Formula.Relation(left, FormulaRelationOperator.Equal, right)));
    }

    private static Formula.BoundVariable Bound(string name) =>
        new(FormulaIdentifier.Create(name), new Formula.NamedConstant(FormulaIdentifier.Create("Nat")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(params Formula[] args)
    {
        Formula result = args[0];
        for (var i = 1; i < args.Length; i++) result = new Formula.Binary(result, FormulaBinaryOperator.Multiply, args[i]);
        return result;
    }
}
