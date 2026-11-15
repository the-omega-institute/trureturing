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
                + "Other interpretations of the linked sequences are not implied.")),
            Paragraph(Text("Eight-letter reuse and normalization")),
            Paragraph(Text("At q=8 the actual word predicate and event extraction are exactly those of BarkerCyclicRepetitionCounting. Its result supplies the unique positive series S₈=8x(1−5x−7x²)/((1−7x)(1−6x−8x²)); its private radical_count, count_recurrence and count_initial supply the strongest existing literal-count facts directly. The original Fin8 owner retains credit for these formulas. No new enumeration is needed. With c(n)=a₈(n), c(0)=1 and c(n+3)=13c(n+2)−34c(n+1)−56c(n) for every n≥0. The first five positive values are 8,64,504,3928,30344. The radical identity extends to n=0: c(n)=[−272·7ⁿ+(153−37√17)(3−√17)ⁿ+(153+37√17)(3+√17)ⁿ]/34 for every n≥0. At zero the numerator is 34. Thus the unique empty word is retained while S₈ still has zero constant coefficient.")),
            Paragraph(Text("The characteristic polynomial factors as t³−13t²+34t+56=(t−7)(t²−6t−8), whose roots are exactly 7,3−√17,3+√17. Since |3−√17|<7<3+√17 and C=(153+37√17)/34>0, division of the existing radical formula by C(3+√17)ⁿ leaves 1 plus constant multiples of [7/(3+√17)]ⁿ and [(3−√17)/(3+√17)]ⁿ. Both ratios have absolute value below one, so their powers tend to zero. Hence limₙ a₈(n)/(C(3+√17)ⁿ)=1, the source asymptotic statement.")),
            Paragraph(Text("Hardin A268944: every column and all seven rows")),
            Paragraph(Text("Put q=k+1, k≥1, and T(n,k)=a_q(n). The actual-count theorem gives T(n+3,k)=(2k−1)T(n+2,k)+(−k²+2k+1)T(n+1,k)−k(k+1)T(n,k). This holds for every column k≥1 and every n≥0 with T(0,k)=1, so it includes the source onset n≥1. The coefficient triples for k=1,…,7 are (1,2,−2),(3,1,−6),(5,−2,−12),(7,−7,−20),(9,−14,−30),(11,−23,−42),(13,−34,−56). These are evaluations of the universal coefficients, rather than an inference from sampled columns.")),
            Paragraph(Text("The complete q-polynomial rows n=1,…,7 are, respectively: q; q²; q³−q; q⁴−3q²+3q; q⁵−6q³+11q²−7q; q⁶−10q⁴+26q³−30q²+15q; q⁷−15q⁵+50q⁴−81q³+73q²−31q. They follow by successive substitution in the actual-count recurrence from 1,q,q². No recurrence-defined replacement count is introduced.")),
            Paragraph(Text("Equivalently the full A268944 rows as polynomials in k are: T(1,k)=k+1; T(2,k)=k²+2k+1; T(3,k)=k³+3k²+2k; T(4,k)=k⁴+4k³+3k²+k+1; T(5,k)=k⁵+5k⁴+4k³+3k²+2k−1; T(6,k)=k⁶+6k⁵+5k⁴+6k³+3k²−k+2; T(7,k)=k⁷+7k⁶+6k⁵+10k⁴+4k³+k²+4k−3. The first three are k+1,(k+1)²,k(k+1)(k+2), giving the stated A000027, A000290 and A007531 identities.")),
            Paragraph(Text("Fried and A269467: every column and all seven rows")),
            Paragraph(Text("Write B(n,k)=b_(k+1)(n), with k≥1. The unequal-event specialization gives B(n+3,k)=(2k−1)B(n+2,k)+(−k²+3k)B(n+1,k)−2k²B(n,k) for n≥1. Its coefficient triples at k=1,…,7 are (1,2,−2),(3,2,−8),(5,0,−18),(7,−4,−32),(9,−10,−50),(11,−18,−72),(13,−28,−98). This is the all-column consequence of Fried’s prior enumeration, not a new priority claim. With b_q(0)=1, the n=0 left side minus the proposed homogeneous right side is 2−q; thus the source onset cannot be extended uniformly to zero.")),
            Paragraph(Text("The complete seven A269467 row polynomials are: B(1,k)=k+1; B(2,k)=k²+2k+1; B(3,k)=k³+3k²+2k; B(4,k)=k⁴+4k³+4k²+k; B(5,k)=k⁵+5k⁴+7k³+2k²−k; B(6,k)=k⁶+6k⁵+11k⁴+4k³−k²+k; B(7,k)=k⁷+7k⁶+16k⁵+8k⁴−k³−k. The first three agree with the cyclic rows. The remaining four follow successively from the unequal-event recurrence starting at n=1. The full rational series has coefficient one at zero; the positive series subtracts that one.")),
            Paragraph(Text("Binary elementary identities")),
            Paragraph(Text("For q=2 the successor and unequal-event languages coincide on each actual word. Specializing the positive series and clearing its unit denominators gives S₂=(4x+6x²)/(1−2x²)−2x/(1−x). All denominators have constant coefficient one. The two-step identity a₂(n+2)=2a₂(n)+2 follows from the actual-count cubic recurrence and initial values a₂(0)=1,a₂(1)=2,a₂(2)=4, by induction. Applying it separately to the two parities gives a₂(2m)=3·2ᵐ−2 and a₂(2m+1)=2^(m+2)−2 for every m≥0, including the empty-word case m=0.")),
            Paragraph(Text("For every n≥0, a₂(n)=Σ_(j=0)^n 2^min(j,n−j). To see the finite-sum identity without replacing the actual count, call the displayed sum P(n). Its endpoint terms at n+2 are both one, and each interior exponent is 1+min(j,n−j). Thus P(n+2)=2P(n)+2, with P(0)=1 and P(1)=2; two-step induction compares it with the already proved actual count. Subtracting consecutive parity formulas gives a₂(n)−a₂(n−1)=2^⌊n/2⌋ for every n≥1. Equivalently the differences obey the same two-step doubling with initial differences 1,2. These are precisely the elementary A027383 identities in the manuscript; the wordwise substring equivalence above supplies its separate semantic assertion.")),
            Paragraph(Text("Attribution and applicability")),
            Paragraph(Text("R. H. Hardin introduced A268943 and A268944; Colin Barker supplied the A268943 conjectured formulas in revision 8, FORMULA. A268944 revision 4 supplies the row, column and cross-reference statements; A027383 revision 193 supplies the elementary identities and binary interpretation; A269467 supplies the unequal-event rows and columns. Sela Fried’s arXiv:2410.07237v3, Section 2.8, Theorem 10, equation (18), and Journal of Integer Sequences 28 (2025), Article 25.4.3, Section 3.2, Theorem 4 and Corollary 5, are prior work. The full revision-2 source is Haobo Ma and Wenlin Zhang’s Barker and Hardin’s cyclic-repetition formulas and an extension of Fried’s enumeration, CC BY 4.0. Haobo Ma is affiliated with ChronoAI Pte Ltd, Singapore; Wenlin Zhang with the National University of Singapore and ChronoAI Pte Ltd, Singapore. The source certificate pins the complete manuscript. Tree, necklace, folding and arithmetic-sequence interpretations and unrelated cross-references are excluded.")))));

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
