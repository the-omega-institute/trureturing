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
                        Call("Admissible", V("R"), V("w"))))))),
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
        DescribeId.Create("regular-repetition-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

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
