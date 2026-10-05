using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.AbelianBorders;

internal sealed class MutualAbelianBorderDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/AbelianBorders/MutualAbelianBorderDensity.";
    private const string WordOwner = "D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace.Word";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/maitykrishna2025mutuallyabelian");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both binary mutual abelian-border densities have limits, with witnesses 1 and 0.",
        H("Mutual Abelian-Border Densities of Binary Word Pairs"),
        Blocks(
            Describe.Lean(DescribeId.Create("binary-word-carrier"), DeclarationHandle.Create(WordOwner),
                H("Binary words"), StatementSource.FromAuthor(Disp(All("n", Naturals(),
                    Equal(Call("Word", F.Id("n")),
                        new Formula.TypeArrow(Call("Fin", F.Id("n")), F.Id("Bool")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A binary word of length n is a function from Fin(n) to Bool. "
                    + "Positions are numbered from 0 to n-1, with false and true encoding the paper's letters a and b. "
                    + "The ordered pair carrier is Word(n) × Word(n)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("walk-reflection-count"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/RandomWalks/WalkCount.walk_count"),
                H("Reflection count for nonnegative walks"),
                StatementSource.FromAuthor(WalkCountFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/StatisticalMechanics/jianu2025dycktype")),
                Blocks(Paragraph(Text("For any family walks with the displayed defining equation, every set walks(n,x) "
                    + "is finite and its cardinality is the reflection sum. The parameter n is the number of steps, "
                    + "and x is the initial height; both range over all natural numbers. The two evaluations at i+1 "
                    + "and i use i.succ and i.castSucc. A first-step decomposition gives two disjoint families, "
                    + "with the downward family present only for x at least 1. Pascal's rule gives the same recursion "
                    + "for the sum, and induction identifies their counts. The family used here is "
                    + "SurvivingWalkRecurrence.walks. No second walk definition is needed."))), DescribeRole.Theorem),
            Node("internal-border", "Internal abelian borders", "internal", BorderFormula(true),
                "The two words have the same length n. "
                + "Abelian equivalence is equality of the counts of both Boolean letters. "
                + "Icc(1,NatSub(n,1)) is the finite closed natural interval; NatSub is truncated natural subtraction. "
                + "The suffix is drop(ofFn(fst(p)),NatSub(n,r)), and the prefix is take(ofFn(snd(p)),r). "
                + "Equal counts force equal lengths, so both factors are nonempty and proper.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("external-border", "External abelian borders", "external", BorderFormula(false),
                "The prefix of the first word is "
                + "compared with the suffix of the second word, for the same nonempty proper length r.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mutual-bordered-count", "Counting mutually abelian-bordered pairs", "M", CountFormula(false),
                "univ(A) denotes the finite set of all inhabitants of the finite type A; filter(P,s) "
                + "retains the elements of s satisfying P, and card denotes Finset.card. "
                + "The finite set contains ordered pairs with both kinds of border. "
                + "Internal and external border lengths may differ; overlapping borders are allowed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mutual-unbordered-count", "Counting mutually abelian-unbordered pairs", "Mbar", CountFormula(true),
                "These pairs have neither kind of border. In particular M(1)=0 and Mbar(1)=4.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("limit-question", "The published limit question", "claim",
                Disp(Equivalent(F.Id("claim"), LimitsFormula())),
                "The two existential real limits are independent. The denominator 4^n equals 2^(2n). "
                + "ofRealNat is the natural-to-real coercion, so every displayed quotient is real division. "
                + "The definitions also assign counts at n=0; this finite initial extension does not affect either limit.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("limit-question-proved", "Both limits exist", "result", Disp(LimitsFormula()),
                "The proof chooses the first limit to be 1 and the second to be 0. "
                + "Reverse the first word and interleave it with the complemented second word. "
                + "An internal abelian border becomes a zero at an even time of the resulting unit-step walk. "
                + "Odd times cannot be zero. Border-free prefixes embed in nonnegative walks after fixing their first sign. "
                + "The reflection count bounds the exceptional pairs by a central binomial coefficient. "
                + "Its normalized value tends to zero; swapping the two words gives the same bound for external borders. "
                + "The union bound and squeeze give both limits.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("maity-krishna-2025-mutual-abelian-border-limits"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Commentary(declaration, prose), role, resolution);

    private static BlockSequence Commentary(string declaration, string prose) => declaration switch
    {
        "internal" => Blocks(BorderQuote(true), Paragraph(Text(prose))),
        "external" => Blocks(BorderQuote(false), Paragraph(Text(prose))),
        "M" => Blocks(BorderedQuote(), CountQuote(false), Paragraph(Text(prose))),
        "Mbar" => Blocks(UnborderedQuote(), CountQuote(true), Paragraph(Text(prose))),
        _ => Blocks(QuestionQuote(), Paragraph(Text(prose))),
    };

    private static DocumentBlock BorderQuote(bool inner) => Paragraph(
        Text(inner ? "“We say a pair of words " : "“Similarly, we say the  pair "),
        Math(Pair("x", "y")), Text(inner ? " is an internal abelian-border of " : " is an external abelian-border of "),
        Math(Pair("u", "v")), Text(" if "), Math(F.Id("x")),
        Text(inner ? " is a nonempty proper suffix of " : " is a nonempty proper prefix of "),
        Math(F.Id("u")), Text(" and  "), Math(F.Id("y")),
        Text(inner ? " is a proper prefix of " : " is a proper suffix of "),
        Math(F.Id("v")), Text(" such that "), Math(AbelianEquivalent()),
        Text(".” (Section 1, Definition 1.1, p. 2.)"));

    private static DocumentBlock BorderedQuote() => Paragraph(
        Text("“A pair of words "), Math(Pair("u", "v")),
        Text(" is said to be mutually abelian-bordered if "), Math(Pair("u", "v")),
        Text(" has both internal abelian-border and external abelian-border.” (Section 1, Definition 1.1, p. 2.)"));

    private static DocumentBlock UnborderedQuote() => Paragraph(
        Text("“If a pair of words "), Math(Pair("u", "v")),
        Text(" has neither an internal abelian-border nor an external abelian-border, then "),
        Math(Pair("u", "v")),
        Text(" is said to be mutually abelian-unbordered pair of words.” (Section 1, Definition 1.2, p. 2.)"));

    private static DocumentBlock CountQuote(bool unbordered) => unbordered
        ? Paragraph(Text("“Let "), Math(SourceCount(true)),
            Text("  denote the number of mutually abelian-unbordered pairs of binary words "),
            Math(Pair("u", "v")), Text(" where "), Math(EqualLengths()), Text(".” (Section 3, p. 25.)"))
        : Paragraph(Text("“The number of MAB pairs "), Math(Pair("u", "v")),
            Text(" with "), Math(EqualLengths()), Text(" is denoted by "), Math(SourceCount(false)),
            Text(".” (Section 2, p. 3.)"));

    private static DocumentBlock QuestionQuote() => Paragraph(Text("“Do the limits "),
        Math(SourceLimit(false)), Text(" and "), Math(SourceLimit(true)),
        Text(" exist?” (Section 5, Conclusion, question 1, p. 29.)"));

    private static Formula Pair(string first, string second) =>
        Parenthesized(Seq(F.Id(first), Comma, Sp, F.Id(second)));
    private static Formula AbelianEquivalent() => Seq(F.Id("x"), Sp,
        new Formula.Subscript(Sim, Seq(Mathrm, Grp(F.Id("abl")))), Sp, F.Id("y"));
    private static Formula EqualLengths() => Seq(new Formula.Absolute(F.Id("u")), Sp, Eq, Sp,
        new Formula.Absolute(F.Id("v")), Sp, Eq, Sp, F.Id("n"));
    private static Formula SourceCount(bool unbordered) => Seq(
        unbordered ? Seq(Overline, Grp(Seq(Mathcal, Grp(F.Id("M"))))) : Seq(Mathcal, Grp(F.Id("M"))),
        Parenthesized(F.Id("n")));
    private static Formula SourceLimit(bool unbordered) => Seq(new Formula.Subscript(Lim, Seq(F.Id("n"), To, Infty)), Sp,
        new Formula.Fraction(SourceCount(unbordered), new Formula.Power(D(2), Seq(D(2), F.Id("n")))));

    private static Formula BorderFormula(bool inner)
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var r = F.Id("r");
        var b = F.Id("b");
        var u = Call("ofFn", Call("fst", p));
        var v = Call("ofFn", Call("snd", p));
        var left = inner ? Call("drop", u, Call("NatSub", n, r)) : Call("take", u, r);
        var right = inner ? Call("take", v, r) : Call("drop", v, Call("NatSub", n, r));
        return Disp(All("n", Naturals(), All("p", PairType(n),
            Equivalent(Call(inner ? "internal" : "external", p), ExistsTyped("r", Naturals(),
                And(new Formula.Relation(r, FormulaRelationOperator.MemberOf, Call("Icc", D(1), Call("NatSub", n, D(1)))),
                    All("b", F.Id("Bool"), Equal(Call("count", left, b), Call("count", right, b)))))))));
    }

    private static Formula CountFormula(bool unbordered)
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var inner = Call("internal", p);
        var outer = Call("external", p);
        var condition = unbordered ? And(new Formula.Not(inner), new Formula.Not(outer)) : And(inner, outer);
        return Disp(All("n", Naturals(), Equal(Call(unbordered ? "Mbar" : "M", n),
            Call("card", Call("filter", Seq(LambdaLower, Parenthesized(Seq(p, Colon, Sp, PairType(n))),
                Sp, Mapsto, Sp, Parenthesized(condition)), Call("univ", PairType(n)))))));
    }

    private static Formula WalkCountFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x"), i = F.Id("i"), s = F.Id("s"), d = F.Id("d");
        Formula one = D(1), two = D(2);
        Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
        Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
        Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
        Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
        Formula Eval(Formula a) => new Formula.Apply(s, [a]);
        Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
        Formula walkType = new Formula.TypeArrow(Call("Fin", Add(n, one)), Naturals());
        Formula equation = Equal(Call("walks", n, x), Seq(OpenBrace, s, Sp, InMacro, Sp,
            walkType, Sp, Mid, Sp, And(Equal(Eval(D(0)), x), All("i", Call("Fin", n),
                Or(Equal(Eval(Add(i, one)), Add(Eval(i), one)),
                    Equal(Add(Eval(Add(i, one)), one), Eval(i))))), CloseBrace));
        Formula condition = And(Lt(n, Add(Add(Mul(two, d), x), two)), Le(Mul(two, d), Add(n, x)));
        Formula term = Call("ifThenElse", condition, Call("choose", n, d), D(0));
        Formula sum = Call("sum", Call("range", Add(n, one)),
            Seq(LambdaLower, Sp, d, Sp, Mapsto, Sp, term));
        Formula conclusion = And(Call("Finite", Call("walks", n, x)),
            Equal(Call("ncard", Call("walks", n, x)), sum));
        Formula familyType = new Formula.TypeArrow(Parenthesized(Seq(n, Colon, Sp, Naturals())),
            new Formula.TypeArrow(Naturals(), Call("Set", walkType)));
        return Disp(All("walks", familyType, new Formula.Logic(
            Parenthesized(All("n", Naturals(), All("x", Naturals(), equation))),
            FormulaLogicOperator.Implies,
            Parenthesized(All("n", Naturals(), All("x", Naturals(), conclusion))))));
    }

    private static Formula LimitsFormula() => And(LimitExists("M"), LimitExists("Mbar"));

    private static Formula LimitExists(string count) => ExistsTyped("L", Reals(),
        Call("Tendsto", new Formula.Sequence(
            new Formula.Fraction(Call("ofRealNat", Call(count, F.Id("n"))),
                new Formula.Power(D(4), F.Id("n"))), F.Id("n"), Naturals()),
            F.Id("atTop"), Call("nhds", F.Id("L"))));

    private static Formula PairType(Formula n) =>
        Seq(Call("Word", n), Sp, Times, Sp, Call("Word", n));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ExistsTyped(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
