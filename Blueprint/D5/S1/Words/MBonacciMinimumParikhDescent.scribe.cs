using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class MBonacciMinimumParikhDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/MBonacciMinimumParikhDescent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum complete Parikh cardinality forces a sentinel-iterate length in the literal "
            + "m-bonacci word.",
        H("Minimum Parikh Cardinality and Sentinel Lengths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("star"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciMinimumParikhDescent.star"),
                H("Star vectors"), StatementSource.FromAuthor(ConverseStatement("star")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a list r and a letter a, star(r,a) has coordinate i equal to letterCount(r,i) plus one exactly when i equals a. These are vectors in natural coordinates; no truncated subtraction is used."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("star-injective"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciMinimumParikhDescent.star_injective"),
                H("Distinct star vectors"), StatementSource.FromAuthor(ConverseStatement("star_injective")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every alphabet size and list r, the map from excess letters to star vectors is injective. Comparing the coordinate of one excess letter distinguishes unequal letters. At a sentinel length this identifies exactly m distinct attained vectors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("star-subset"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciMinimumParikhDescent.star_subset"),
                H("Attainment by actual right extensions"), StatementSource.FromAuthor(ConverseStatement("star_subset")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m at least two and every fully right-special actual factor r, every star vector is the count vector of an actual factor at a natural start. Each excess letter chooses its own right-extension occurrence. Combined with the converse all-start upper inclusion, this yields equality and exact cardinality, rather than an upper bound alone."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Let m be a natural number with 2 at most m and 3 at most m. The alphabet "
                + "is Fin m. The literal substitution sends each letter a below m minus one "
                + "to the two letters zero and a plus one, and sends the terminal letter to "
                + "zero. The word is the unbounded limit of the iterated images of zero. "
                + "For a list s, T(s) is its substituted image followed by zero.")),
            Paragraph(Text(
                "For a natural length n, parikhImage(m,n) is the range of the map sending "
                + "every natural start q to the vector of letter counts of factor(word,q,n). "
                + "Start zero is included. Each coordinate is at most n, so this complete "
                + "image is finite even though the set of starts is infinite. Its cardinality "
                + "is the abelian complexity of the actual word at length n.")),
            Describe.Lean(
                DescribeId.Create("minimal-abelian-complexity-length"),
                DeclarationHandle.Create(Prefix + "minimal_abelian_complexity_length"),
                H("Minimum complexity determines a sentinel length"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take the reverse r of the position-zero prefix of length n minus "
                        + "one. It is fully right-special: each list r followed by a letter "
                        + "has an actual occurrence. These m extensions give m distinct "
                        + "Parikh vectors, the central vector of r plus each unit vector. "
                        + "If the complete image has cardinality m, these vectors exhaust it.")),
                    Paragraph(Text(
                        "A signed defect of r is an actual word v of length one more than "
                        + "r whose integer count difference is e(a) plus e(b) minus e(c), "
                        + "with a, b and c pairwise distinct. Its negative coordinate excludes "
                        + "it from the central vectors, so minimum cardinality rules it out.")),
                    Paragraph(Text(
                        "For a nonempty fully right-special list starting with a nonzero "
                        + "letter a, choose another nonzero letter b distinct from a. An "
                        + "occurrence of r followed by b is followed by zero. Removing the "
                        + "first letter and retaining that zero produces a signed defect. "
                        + "Consequently every nonempty defect-free fully right-special list "
                        + "starts with zero and has a strictly shorter fully right-special "
                        + "preimage under T.")),
                    Paragraph(Text(
                        "Signed defects lift under T. If the terminal coordinate difference "
                        + "is minus one, zero or one, use respectively the tail of the actual "
                        + "substituted occurrence, the whole occurrence or its sentinel "
                        + "extension. The start is respectively boundary(q) plus one or "
                        + "boundary(q). The new difference is the cyclic rotation of the old "
                        + "one. A defect-free image therefore has a defect-free preimage. "
                        + "Strong induction on length identifies r with an iterate of T "
                        + "starting at the empty list, yielding the stated equation."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The conclusion includes n equal to one, with k equal to zero. No balance, "
                + "palindrome, finite occurrence window or numeration admissibility "
                + "hypothesis is required.")))));

    private static Formula Statement() => All("m", N(), Imp(
        And(Leq(D(2), F.Id("m")), Leq(D(3), F.Id("m"))),
        All("n", N(), Imp(
            And(Leq(D(1), F.Id("n")),
                Eq(Call("ncard", Call("parikhImage", F.Id("m"), F.Id("n"))), F.Id("m"))),
            Ex("k", N(), Eq(F.Id("n"),
                Add(Call("length", Call("iterate", Call("T", F.Id("m")),
                    F.Id("k"), Call("nil"))), D(1))))))));

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Ex(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula ConverseStatement(string name)
    {
        var m = F.Id("m"); var n = F.Id("n"); var k = F.Id("k");
        var q = F.Id("q"); var i = F.Id("i"); var t = F.Id("t");
        var r = F.Id("r"); var s = F.Id("s"); var a = F.Id("a");
        var x = F.Id("x"); var count = F.Id("count");
        Formula ns = CFCall("S", m, k);
        Formula si = CFCall("sentinelIter", m, k);
        Formula rho = CFCall("ncard", CFCall("parikhImage", m, n));
        Formula minimum = CFEq(rho, m);
        Formula sentinel = CFEx("k", CFN(), CFEq(n, ns));
        Formula periodic = CFEx("k", CFN(), CFEq(CFCall("fullGreedy", m, n),
            CFCall("periodicDigits", m, k)));
        Formula body = name switch
        {
            "star" => CFAll("r", CFCall("List", CFCall("Fin", m)),
                CFAll("a", CFCall("Fin", m), CFAll("i", CFCall("Fin", m),
                    CFAnd(CFImp(CFEq(i, a), CFEq(CFCall("star", r, a, i),
                            CFAdd(CFCall("letterCount", r, i), F.D(1)))),
                        CFImp(new Formula.Relation(i, FormulaRelationOperator.NotEqual, a),
                            CFEq(CFCall("star", r, a, i), CFCall("letterCount", r, i))))))),
            "star_injective" => CFAll("r", CFCall("List", CFCall("Fin", m)),
                CFCall("Injective", CFCall("star", r))),
            "star_subset" => CFAll("r", CFCall("List", CFCall("Fin", m)),
                CFImp(CFCall("FRS", m, r), CFCall("Subset", CFCall("range", CFCall("star", r)),
                    CFCall("parikhImage", m, CFAdd(CFCall("length", r), F.D(1)))))),
            _ => throw new ArgumentOutOfRangeException(nameof(name)),
        };
        Formula bound = name == "uniform_minimum_characterization"
            ? CFAnd(CFLe(F.D(2), m), CFLe(F.D(5), m)) : CFLe(F.D(2), m);
        bool unrestricted = name is "star" or "star_injective" or "factor_add";
        return F.Disp(CFAll("m", CFN(), unrestricted ? body : CFImp(bound, body)));
    }

    private static Formula CFN() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula CFCall(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula CFAll(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula CFEx(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula CFEq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula CFLe(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula CFAdd(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula CFAnd(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula CFImp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
