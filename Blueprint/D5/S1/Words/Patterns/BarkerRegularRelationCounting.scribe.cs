using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class BarkerRegularRelationCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/BarkerRegularRelationCounting.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/barker2019a268943");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal repetition-word counts for loopless relations of constant indegree.",
        H("Repetition words with a regular incoming relation"),
        Blocks(
            Paragraph(Text("The alphabet is Fin q and a word of length n is a function from Fin n "
                + "to Fin q. Equality events are adjacent equal pairs, in position order, including "
                + "overlapping pairs. The word is linear; neither rotations nor changes of alphabet "
                + "labels are identified. The relation constrains successive event labels. "
                + "The alphabet sizes q ≥ 2 in Ma and Zhang's Barker and Hardin's cyclic-repetition "
                + "formulas and an extension of Fried's enumeration are included; the statement "
                + "also permits the empty and one-letter alphabets whenever its hypotheses hold.")),
            Node("eventLabels", "Ordered equality-event labels", EventLabelsFormula(),
                "Zip the word with its tail, retain equal pairs, and read their second coordinates. "
                + "Thus a triple equal letter contributes two events. This is the same extraction "
                + "as in the eight-letter cyclic model, with a variable alphabet size.", DescribeRole.Definition),
            Node("Admissible", "Admissible literal words", All("q", N(), All("n", N(),
                All("R", RelationType(), All("w", Words(V("n")),
                    Equal(Call("Admissible", V("R"), V("w")),
                        App(Q("List", "IsChain"), V("R"),
                            Call("eventLabels", App(Q("List", "ofFn"), V("w"))))))))),
                "An empty or singleton event list is admissible. Longer lists require R between "
                + "each pair of consecutive event labels. In particular, looplessness forbids two "
                + "consecutive events of the same label, including the overlap in a triple letter.",
                DescribeRole.Definition),
            Node("count", "Actual word cardinalities", All("q", N(), All("R", RelationType(),
                All("n", N(), Equal(Call("count", V("R"), V("n")),
                    App(Q("Nat", "card"), Subtype("w", Words(V("n")),
                        Call("Admissible", V("R"), V("w")))))))),
                "The carrier is the subtype of actual words satisfying the event relation. "
                + "No recurrence is used to define this cardinality.", DescribeRole.Definition),
            Node("sourceSeries", "Positive-index coefficient series", All("q", N(),
                All("R", RelationType(), Equal(Call("sourceSeries", V("R")),
                    App(Q("PowerSeries", "mk"), Lam("n", N(),
                        Call("if", Equal(V("n"), D(0)), D(0), Count(V("n")))))))),
                "The coefficient at zero is zero. Every positive coefficient is the actual "
                + "cardinality cast to the rationals. The unique empty word is counted separately "
                + "by count R 0 = 1.", DescribeRole.Definition),
            Node("relation_enumeration", "The regular-relation enumeration", EnumerationFormula(),
                "Partition nonempty admissible words into U with no events, A whose first letter b "
                + "is related to the first event r, and B containing the other eventful words. "
                + "The initial vector is (q,0,0). For each fixed suffix, prepending every possible "
                + "letter gives (U,A,B) ↦ ((q−1)U,(d−1)A+dB,U+(q−d+1)A+(q−d−1)B). "
                + "Exactly d letters precede r under R. The equal-letter choice is removed from "
                + "the A fiber when R(b,r) holds; duplicating b then enters B because R(b,b) fails. "
                + "Removing the first letter recovers the unique suffix and deletes at most its "
                + "first event. Fin.consEquiv therefore converts these exhaustive fibers to the "
                + "literal cardinality sums. The coefficients are rational: d−1 is signed. "
                + "When d=0, A is empty, and the same identities remain valid. Coefficientwise "
                + "series equations and elimination yield the displayed unit-denominator formula. "
                + "Both denominator factors have constant coefficient one. Eliminating the state "
                + "counts also gives the displayed recurrence, which begins at positive length.",
                DescribeRole.Theorem),
            Node("eventCount", "Literal exact-event fibers", EventCountFormula(),
                "This subtype retains the original admissibility predicate and requires the length "
                + "of the ordered event list to be exactly r. Overlapping equality pairs remain "
                + "individual events, and every word keeps its literal alphabet labels.", DescribeRole.Definition),
            Node("eventSeries", "Exact-event coefficient series", EventSeriesFormula(),
                "The coefficient of x to a positive length n is the rational cast of eventCount R n r. "
                + "The constant coefficient is zero. Empty words are accounted for separately.", DescribeRole.Definition),
            Node("markedSeries", "Eventful words marked by event number", MarkedDefinitionFormula(),
                "This is a series in y with coefficients in Q[[x]]. Its coefficient at y to r+1 "
                + "is eventSeries R (r+1), so the coefficient at x to n and y to r+1 is the actual "
                + "exact-event cardinality. The coefficient at y to zero is zero; no substitution "
                + "of one into an arbitrary formal series is used.", DescribeRole.Definition),
            Node("event_enumeration", "Enumeration by the exact number of equality events", EventEnumerationFormula(),
                "Filter the three indicator weights by the length of the extracted event list. "
                + "Prepending a different letter preserves this length. Prepending the first letter "
                + "adds exactly one event, and enters B precisely from U or A. The same unique "
                + "first-letter and suffix correspondence therefore gives the exact-event fibers. "
                + "Write H=1-(q-1)x and J=1+x. For positive event number, U vanishes. The eventful "
                + "states satisfy J A_r=d x (A_r+B_r) and H(A_r+B_r)=x(U_(r-1)+A_(r-1)). "
                + "For zero events, A and B vanish and U=qx/H. Thus E_1 H^2=qx^2 and "
                + "E_(r+2) J H=d x^2 E_(r+1). Induction on event number proves the displayed "
                + "formula, and coefficient extraction proves the literal-word identity and the "
                + "shortest-length boundary. The parameter r in the formula represents r+1 events; "
                + "hence the exponent d^r includes d^0=1 even when d=0. For one event the answer "
                + "is qx^2/H^2, and at indegree zero every fiber with two or more events vanishes. "
                + "There is one empty zero-event word, no empty eventful word, and no singleton "
                + "eventful word. The shortest r+1-event words have length 2(r+1), with count q d^r. "
                + "The final marked identity is in Q[[x]][[y]]. Its denominator has constant "
                + "coefficient JH as a y-series, which is a unit because its x-constant is one. "
                + "Ring.inverse denotes this unit inverse. The numerator is y x(1+x)U, exactly "
                + "as in the source; both markers refer to actual word fibers.", DescribeRole.Theorem),
            Node("binaryStep", "The signed binary steps", All("a", BinaryLetter(),
                Equal(Call("binaryStep", V("a")), Subtract(Multiply(D(2),
                    Cast(App(Q("Fin", "val"), V("a")), Integers())), D(1)))),
                "The source alphabet is literally {0,1}: zero contributes minus one and one "
                + "contributes plus one. The values are integers, so subtraction is signed.",
                DescribeRole.Definition),
            Node("signedImbalance", "Signed imbalance of an actual word", All("w", BinaryWords(),
                Equal(Call("signedImbalance", V("w")), App(Q("List", "sum"),
                    App(Q("List", "map"), Named("binaryStep"), V("w"))))),
                "Summing the signed steps gives the number of ones minus the number of zeros. "
                + "The empty list has imbalance zero.", DescribeRole.Definition),
            Node("binary_substring_equivalence", "Binary events and every contiguous substring",
                BinarySubstringFormula(),
                "This equivalence concerns each actual word and all of its actual contiguous "
                + "sublists. An infix u means there are lists a and b with a++u++b=w; neither "
                + "positions nor alphabet labels are quotiented. The left side uses the original "
                + "overlapping equality-event list and successor modulo two. On {0,1} this "
                + "successor relation is exactly inequality. Replace zero by a step minus one "
                + "and one by a step plus one. A word fits a strip of heights 0 through 2 "
                + "from some integer starting height exactly when its event labels alternate. "
                + "Induction on the word proves the three possible starting-height conditions: "
                + "at height 0 the first letter and the first event, if present, are 1; at height 2 "
                + "they are 0; at height 1 the first event, if present, differs from the first "
                + "letter. Prepending an equal letter inserts that very letter as a new event, "
                + "so the induction retains overlapping pairs. A strip path bounds the sum "
                + "on every infix by subtracting its two endpoint heights. Conversely choose a "
                + "prefix with minimum height among all prefixes, including the empty prefix "
                + "of height zero. The difference between any two ordered prefix heights is "
                + "the signed sum on their intervening actual infix. The substring hypothesis "
                + "therefore places all prefix heights within two of the minimum. Translating "
                + "by its negative gives a strip path and hence the event rule. Empty words, "
                + "empty substrings, singleton words, words with no equality events and short "
                + "event lists are all included. No counting formula enters either direction.",
                DescribeRole.Theorem),
            Paragraph(Text("Only q and d occur in the answer, so two loopless relations on the "
                + "same alphabet with the same indegree have equal counts at every length. For "
                + "d=1, take R(a,b) to mean b=σ(a), where σ is any fixed-point-free permutation. "
                + "Every b has its unique predecessor σ⁻¹(b). The cyclic successor σ(a)=a+1 "
                + "modulo q is one such permutation for q≥2. Its recurrence is "
                + "a(n+3)=(2q−3)a(n+2)+(−q²+4q−2)a(n+1)−q(q−1)a(n) for n≥0; "
                + "the n=0 case follows from 1,q,q²,q³−q. The positive series is "
                + "qx(1−(q−3)x−(q−1)x²)/((1−(q−1)x)(1−(q−2)x−qx²)). "
                + "The existing eight-letter cyclic theorem supplies its unique series and "
                + "positive-index radical expression directly.")),
            Paragraph(Text("For R(a,b) meaning a≠b, the indegree is q−1. Conversely a loopless "
                + "relation of that indegree contains every unequal pair. This is Fried's "
                + "unequal-event enumeration: arXiv:2410.07237v3, Theorem 10, equation (18), "
                + "and Journal of Integer Sequences 28, Article 25.4.3, Section 3.2, Theorem 4 "
                + "and Corollary 5. Its displayed rational function is the full series 1+S, "
                + "with constant coefficient one, although the described sequence starts at "
                + "positive index. Here 1+S=(1−(q−3)x−2(q−2)x²−(q−2)x³)/"
                + "(1−(2q−3)x+(q−1)(q−4)x²+2(q−1)²x³). The homogeneous recurrence "
                + "b(n+3)=(2q−3)b(n+2)+(−q²+5q−4)b(n+1)−2(q−1)²b(n) "
                + "has onset n≥1; b(0)=1 does not extend that onset. The cyclic and unequal "
                + "rules agree on a binary alphabet. For q≥3, the word (0,0,2,2) separates them. "
                + "Other interpretations of the linked sequences are not implied.")))));

    private static DocumentBlock Node(string name, string title, Formula statement,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("regular-repetition-" + name.ToLowerInvariant().Replace("_", "-")),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Integers() => Seq(Mathbb, Grp(V("Z")));
    private static Formula BinaryLetter() => Call("Fin", D(2));
    private static Formula BinaryWords() => App(Named("List"), BinaryLetter());

    private static Formula BinarySubstringFormula()
    {
        var relation = Lam("a", BinaryLetter(), Lam("b", BinaryLetter(),
            Equal(App(Q("Fin", "val"), V("b")), new Formula.Modulo(
                Parenthesized(Add(App(Q("Fin", "val"), V("a")), D(1))), D(2)))));
        var events = App(Q("List", "IsChain"), relation, Call("eventLabels", V("w")));
        var imbalance = Subtract(Cast(App(Q("List", "count"), D(1), V("u")), Integers()),
            Cast(App(Q("List", "count"), D(0), V("u")), Integers()));
        var bounds = And(new Formula.Relation(new Formula.Negate(D(2)),
            FormulaRelationOperator.LessThanOrEqual, imbalance),
            new Formula.Relation(imbalance, FormulaRelationOperator.LessThanOrEqual, D(2)));
        return All("w", BinaryWords(), new Formula.Logic(Parenthesized(events),
            FormulaLogicOperator.Iff, Parenthesized(All("u", BinaryWords(),
                Implies(App(Q("List", "IsInfix"), V("u"), V("w")), bounds)))));
    }

    private static Formula EventLabelsFormula()
    {
        var pairs = App(Q("List", "zip"), V("w"), App(Q("List", "tail"), V("w")));
        var filtered = App(Q("List", "filter"), Lam("p", Seq(Letters(), Times, Letters()),
            Equal(App(Q("Prod", "fst"), V("p")), App(Q("Prod", "snd"), V("p")))), pairs);
        return All("q", N(), All("w", App(Named("List"), Letters()),
            Equal(Call("eventLabels", V("w")), App(Q("List", "map"), Q("Prod", "snd"), filtered))));
    }

    private static Formula EnumerationFormula()
    {
        var initials = And(Equal(Call("count", V("R"), D(0)), D(1)),
            And(Equal(Count(D(1)), V("q")), And(Equal(Count(D(2)), Power(V("q"), D(2))),
                Equal(Count(D(3)), Subtract(Power(V("q"), D(3)), V("q"))))));
        var recurrence = All("n", N(), Equal(Count(Add(V("n"), D(4))),
            Subtract(Add(Multiply(Subtract(Multiply(D(2), V("q")), D(3)), Count(Add(V("n"), D(3)))),
                Multiply(Subtract(Add(Add(new Formula.Negate(Power(V("q"), D(2))),
                    Multiply(D(4), V("q"))), V("d")), D(3)), Count(Add(V("n"), D(2))))),
                Multiply(Multiply(Subtract(V("q"), D(1)), Subtract(Add(V("q"), V("d")), D(1))),
                    Count(Add(V("n"), D(1)))))));
        return All("q", N(), All("d", N(), All("R", RelationType(),
            Implies(All("a", Letters(), new Formula.Not(CallR(V("a"), V("a")))),
                Implies(All("r", Letters(), Equal(App(Q("Nat", "card"),
                    Subtype("b", Letters(), CallR(V("b"), V("r")))), V("d"))),
                    And(Parenthesized(initials), And(Equal(Call("sourceSeries", V("R")),
                        GeneratingFunction()), recurrence)))))));
    }

    private static Formula EventCountFormula()
    {
        var labels = Call("eventLabels", App(Q("List", "ofFn"), V("w")));
        var predicate = And(Call("Admissible", V("R"), V("w")),
            Equal(App(Q("List", "length"), labels), V("r")));
        var card = App(Q("Nat", "card"), Subtype("w", Words(V("n")), predicate));
        var equality = Equal(Call("eventCount", V("R"), V("n"), V("r")), card);
        return All("q", N(), All("R", RelationType(), All("n", N(), All("r", N(), equality))));
    }

    private static Formula EventSeriesFormula() => All("q", N(), All("R", RelationType(), All("r", N(),
        Equal(Call("eventSeries", V("R"), V("r")), App(Q("PowerSeries", "mk"), Lam("n", N(),
            Call("if", Equal(V("n"), D(0)), D(0), EventCount(V("n"), V("r")))))))));

    private static Formula MarkedDefinitionFormula() => All("q", N(), All("R", RelationType(),
        Equal(Call("markedSeries", V("R")), Multiply(Q("PowerSeries", "X"),
            App(Q("PowerSeries", "mk"), Lam("r", N(),
                Call("eventSeries", V("R"), Add(V("r"), D(1)))))))));

    private static Formula EventCount(Formula n, Formula r) =>
        Cast(Call("eventCount", V("R"), n, r), Rationals());

    private static Formula EventFunction(Formula r)
    {
        var x = Q("PowerSeries", "X");
        Formula C(Formula f) => App(Q("PowerSeries", "C"), Cast(f, Rationals()));
        var numerator = Multiply(C(Multiply(V("q"), Power(V("d"), r))),
            Power(x, Multiply(D(2), Add(r, D(1)))));
        var denominator = Multiply(Power(Parenthesized(Add(D(1), x)), r),
            Power(Parenthesized(Subtract(D(1), Multiply(C(Subtract(V("q"), D(1))), x))),
                Add(r, D(2))));
        return Multiply(numerator, Power(Parenthesized(denominator), new Formula.Negate(D(1))));
    }

    private static Formula MarkedFormula()
    {
        var x = Q("PowerSeries", "X");
        var y = Q("PowerSeries", "X");
        Formula C(Formula f) => App(Q("PowerSeries", "C"), f);
        var h = Subtract(D(1), Multiply(C(Cast(Subtract(V("q"), D(1)), Rationals())), x));
        var numerator = Multiply(y, C(Multiply(Multiply(x, Parenthesized(Add(D(1), x))),
            Call("eventSeries", V("R"), D(0)))));
        var denominator = Subtract(C(Multiply(Parenthesized(Add(D(1), x)), Parenthesized(h))),
            Multiply(y, C(Multiply(C(Cast(V("d"), Rationals())), Power(x, D(2))))));
        return Equal(Call("markedSeries", V("R")), Multiply(numerator,
            App(Q("Ring", "inverse"), denominator)));
    }

    private static Formula EventEnumerationFormula()
    {
        var r = V("r");
        var n = V("n");
        var next = Add(r, D(1));
        var empty = And(Equal(Call("eventCount", V("R"), D(0), D(0)), D(1)),
            All("r", N(), Equal(Call("eventCount", V("R"), D(0), next), D(0))));
        var x = Q("PowerSeries", "X");
        var zero = Equal(Call("eventSeries", V("R"), D(0)), Multiply(
            Multiply(App(Q("PowerSeries", "C"), Cast(V("q"), Rationals())), x),
            Power(Parenthesized(Subtract(D(1), Multiply(App(Q("PowerSeries", "C"),
                Cast(Subtract(V("q"), D(1)), Rationals())), x))), new Formula.Negate(D(1)))));
        var series = All("r", N(), Equal(Call("eventSeries", V("R"), next), EventFunction(r)));
        var coefficient = All("r", N(), All("n", N(), Equal(EventCount(n, next),
            App(Q("PowerSeries", "coeff"), n, EventFunction(r)))));
        var shortLength = All("r", N(), All("n", N(), Implies(
            new Formula.Relation(n, FormulaRelationOperator.LessThan, Multiply(D(2), next)),
            Equal(Call("eventCount", V("R"), n, next), D(0)))));
        var shortest = All("r", N(), Equal(Call("eventCount", V("R"), Multiply(D(2), next), next),
            Multiply(V("q"), Power(V("d"), r))));
        var conclusion = And(empty, And(zero, And(series, And(coefficient,
            And(shortLength, And(shortest, MarkedFormula()))))));
        var loopless = All("a", Letters(), new Formula.Not(CallR(V("a"), V("a"))));
        var degree = All("c", Letters(), Equal(App(Q("Nat", "card"),
            Subtype("b", Letters(), CallR(V("b"), V("c")))), V("d")));
        return All("q", N(), All("d", N(), All("R", RelationType(),
            Implies(loopless, Implies(degree, conclusion)))));

    }

    private static Formula GeneratingFunction()
    {
        var x = Q("PowerSeries", "X");
        Formula C(Formula f) => App(Q("PowerSeries", "C"), Cast(f, Rationals()));
        var numerator = Multiply(Multiply(C(V("q")), x), Parenthesized(Subtract(
            Subtract(D(1), Multiply(C(Subtract(V("q"), D(3))), x)),
            Multiply(C(Subtract(Add(V("q"), V("d")), D(2))), Power(x, D(2))))));
        var denominator = Multiply(Parenthesized(Subtract(D(1),
            Multiply(C(Subtract(V("q"), D(1))), x))), Parenthesized(Subtract(
                Subtract(D(1), Multiply(C(Subtract(V("q"), D(2))), x)),
                Multiply(C(Subtract(Add(V("q"), V("d")), D(1))), Power(x, D(2))))));
        return Multiply(numerator, Power(Parenthesized(denominator), new Formula.Negate(D(1))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Seq(V(owner), Dot, V(name))));
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula CallR(Formula a, Formula b) => App(V("R"), a, b);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Letters() => Call("Fin", V("q"));
    private static Formula Words(Formula n) => Seq(Call("Fin", n), Sp, To, Sp, Letters());
    private static Formula RelationType() => Seq(Letters(), Sp, To, Sp, Letters(), Sp, To, Sp, V("Prop"));
    private static Formula Count(Formula n) => Cast(Call("count", V("R"), n), Rationals());
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Subtype(string v, Formula type, Formula p) =>
        Seq(OpenBrace, V(v), Colon, Sp, type, Sp, Mid, Sp, p, CloseBrace);
    private static Formula All(string name, Formula type, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Cast(V(name), type), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Disp(Formula body) => F.Disp(body);
}
