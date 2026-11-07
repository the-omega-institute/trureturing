using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class RichWordTypeIOccurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/RichWordTypeIOccurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native seven-letter substitution boundaries and terminal return cancellation.",
        H("Type-I Occurrences in the Seven-Letter Source Word"),
        Blocks(
            Paragraph(Text("The alphabet is Fin 7. The image of i below 6 is [0,i+1], "
                + "and the image of 6 is [0,6,6]. The word u is the limit of the actual "
                + "nested iterates on 0. B(i) is the length of the substituted prefix of "
                + "i letters. Occ(s,q) means that the length-|s| factor at natural "
                + "position q equals s. Consecutive starts a<b have no intervening "
                + "occurrence; overlapping factors and the origin remain in the domain.")),
            Paragraph(Text("The Type-I sequence starts with W(0)=[6]. At ordinary "
                + "phases W(n+1)=phi(W(n))[0]; at phase n modulo 6 equal to 5 it is "
                + "[6]phi(W(n))[0,6]. Left and right extensions are defined by actual "
                + "occurrences of c::s and s++[c], respectively.")),
            Theorem("actual_fixed_point", "actual-fixed-point",
                "Actual limit and exact block semantics", FixedPoint(),
                "All finite iterates are prefixes of u. Prefix compatibility follows "
                + "by writing the next iterate on 0 as the current iterate followed by "
                + "the same iterate on 1; the latter is nonempty. Unbounded lengths "
                + "make the pointwise definition total. Substituting arbitrary prefix "
                + "windows gives the fixed-point block equation. Every image starts "
                + "with zero and has no other zero, so the zeros are precisely the "
                + "unique true boundaries, including B(0)=0. The displayed "
                + "prefixImageLengthSum(i) denotes the sum of |phi(u(j))| over j<i."),
            Theorem("terminal_interval_cancellation", "terminal-interval-cancellation",
                "Final-six deletion on actual return intervals", Cancellation(),
                "For positive a<b with the actual predecessor letters at a and b in "
                + "{5,6}, both preceding image letters are 6. The interval "
                + "[B(a)-1,B(b)-1) has length B(b)-B(a), exactly the length of "
                + "phi(u[a,b)). The identity therefore prepends 6 and deletes the "
                + "final 6 of phi(u[a,b)); it does not increase the length. The proof "
                + "uses contiguous native factors and applies whether or not the "
                + "occurrence windows at a and b overlap."),
            Theorem("ordinary_occurrence_iff", "ordinary-occurrence",
                "Bidirectional ordinary occurrence parsing", Ordinary(),
                "For every native finite word s and every natural q, phi(s) followed "
                + "by zero occurs at q exactly when q=B(i) for an occurrence of s at i. "
                + "The three-letter prefix of phi(c)[0] is injective in c: it is "
                + "[0,c+1,0] below 6 and [0,6,6] at 6. Reserving the final zero "
                + "therefore disambiguates the images of both 5 and 6. Recursive "
                + "decoding includes empty s and imposes no nonoverlap condition."),
            Theorem("typeI_not_at_origin", "typei-origin",
                "No Type-I occurrence at the origin", Origin(),
                "An ordinary step desubstitutes an occurrence at zero to an "
                + "occurrence at zero at the previous index. A terminal step "
                + "starts with 6, whereas u(0)=0. Induction from W(0)=[6] "
                + "excludes position zero at every index."),
            Theorem("terminal_occurrence_iff", "terminal-occurrence",
                "Terminal parsing with exact source contexts", TerminalOccurrence(),
                "The initial 6 is the final 6 before a true boundary: the following "
                + "zero excludes the first 6 of 066. Decoding the central sentinel "
                + "gives the source occurrence. The preceding image ends in 6 "
                + "exactly for source letters 5 and 6; its successor image begins "
                + "06 exactly for those same two letters."),
            Theorem("ordinary_consecutive_iff", "ordinary-consecutive",
                "Ordinary consecutive returns", OrdinaryConsecutive(),
                "Strict boundary monotonicity and the all-position occurrence "
                + "equivalence transfer consecutiveness in both directions. Every "
                + "intermediate target occurrence would decode to an intermediate "
                + "source occurrence, including overlapping windows."),
            Theorem("terminal_return_parikh", "terminal-parikh",
                "All seven counts survive endpoint cancellation", TerminalParikh(),
                "At positive source endpoints with predecessor letters in {5,6}, "
                + "the deleted final 6 and the prepended 6 cancel in every coordinate. "
                + "Thus the native shifted return has count vector M times the "
                + "count vector of the source return. Column c of M is the actual "
                + "count vector of phi(c)."),
            Theorem("base_return_minimum", "base-return",
                "An actual minimum base return", BaseMinimum(),
                "The sixth iterate on zero has a 6 at position 63. Its substituted "
                + "block gives an actual 0660 window at B(63). The adjacent 6s are "
                + "consecutive occurrences of [6], with return [6]. Every actual "
                + "return to [6] begins with 6, so its count vector dominates e(6)."),
            Theorem("typeI_parikh_formula", "factor-parikh",
                "Complete factor Parikh recurrence", FactorParikh(),
                "Write e(c) for unit(c), and increment(n)=e(0) at ordinary phases "
                + "and e(0)+2e(6) at phase 5. The correction sum at n is the sum "
                + "of M raised to n-1-k times increment(k), over 0<=k<n. The "
                + "displayed parikhCorrectionSum denotes exactly this finite sum. "
                + "Induction proves both its equality with the actual factor "
                + "counts and the matrix formula for actual iterated letter images."),
            Theorem("typeI_extensions", "extensions",
                "Exact actual left and right extension sets", Extensions(),
                "Both sets equal {n modulo 6,6}. Membership in each extension set "
                + "means an actual occurrence with the indicated neighboring letter, "
                + "so equality includes witnesses for both letters. The base "
                + "witnesses are 06,66,60 in the actual 0660 window. Ordinary "
                + "steps send contexts through the last letter of their images. "
                + "At phase 5, the extra terminal letters expose the second-last "
                + "and third image letters, sending 5 to 0 and 6 to 6."),
            Theorem("typeI_occurrence_iff", "all-occurrences",
                "All-index bidirectional occurrence transfer", Occurrences(),
                "The occurrence map is B(a) at ordinary phases and B(a)-1 at "
                + "phase 5. At phase 5 the proved extension sets supply both "
                + "source contexts required by terminal recognition. No context "
                + "premise remains in this all-index equivalence."),
            Theorem("typeI_consecutive_iff", "all-consecutive",
                "All-index bidirectional consecutive-return transfer", Consecutives(),
                "The occurrence map is strictly increasing even at the origin, "
                + "since every image has length at least two. The occurrence "
                + "equivalence then transfers every consecutive pair, without "
                + "a restriction on the overlap of its occurrence windows."),
            Theorem("typeI_return_parikh", "return-parikh",
                "Parikh transport of every actual return", ReturnParikh(),
                "At an ordinary step the actual interval is phi(R). At phase 5 "
                + "it is 6 followed by phi(R) with its final 6 deleted. Both "
                + "therefore have vector M times the vector of R."),
            Theorem("typeI_return_minimum", "all-return-minimum",
                "Realized minimum and universal componentwise bound", Minimum(),
                "Transporting the actual adjacent-six base return constructs "
                + "an actual consecutive return with vector M raised to n times "
                + "e(6) at every index. Conversely every actual target return "
                + "decodes to an actual source return. Multiplication by the "
                + "nonnegative incidence matrix preserves the componentwise "
                + "inductive lower bound. Both conclusions cover all natural "
                + "indices and unrestricted occurrence overlaps."))));


    private static DocumentBlock Theorem(string name, string id, string title,
        Formula statement, string exposition) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(exposition))), DescribeRole.Theorem);

    private static Formula FixedPoint()
    {
        Formula k = F.Id("k"), i = F.Id("i"), n = F.Id("n"), q = F.Id("q");
        Formula u = C("word");
        Formula B(Formula x) => C("boundary", x);
        Formula P(Formula x) => C("image", C("phi"), x, F.D(0));
        Formula S(Formula x, Formula y) => C("subst", C("phi"), C("factor", u, x, y));
        return And(
            All("k", N(), Eq(C("factor", u, F.D(0), C("length", P(k))), P(k))),
            And(C("StrictMono", C("boundary")), And(Eq(B(F.D(0)), F.D(0)),
            And(All("i", N(), Eq(B(i), C("prefixImageLengthSum", i))),
            And(All("i", N(), All("n", N(),
                Eq(C("factor", u, B(i), C("length", S(i,n))), S(i,n)))),
            All("q", N(), Iff(Eq(C("word", q), F.D(0)),
                UniqueBoundary(q))))))));
    }

    private static Formula UniqueBoundary(Formula q)
    {
        Formula i = F.Id("i"), j = F.Id("j");
        return new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("i"),
            N(), And(Eq(q, C("boundary", i)),
                All("j", N(), Imp(Eq(q, C("boundary", j)), Eq(j,i)))));
    }

    private static Formula Ordinary()
    {
        Formula s = F.Id("s"), q = F.Id("q"), i = F.Id("i");
        return All("s", C("List", C("Fin", F.D(7))), All("q", N(),
            Iff(C("Occ", C("sentinel", s), q),
                new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("i"),
                    N(), And(Eq(q, C("boundary", i)), C("Occ", s, i))))));
    }

    private static Formula Origin() => All("n", N(),
        Imp(C("Occ", C("typeI", F.Id("n")), F.D(0)), C("False")));

    private static Formula Cancellation()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula Pred(Formula x) => Sub(x, F.D(1));
        Formula B(Formula x) => C("boundary", x);
        Formula Context(Formula x) => Or(Eq(C("word", Pred(x)), F.D(5)),
            Eq(C("word", Pred(x)), F.D(6)));
        return All("a", N(), All("b", N(),
            Imp(Lt(F.D(0),a), Imp(Lt(a,b), Imp(Context(a), Imp(Context(b),
                Eq(C("returnWord", Pred(B(a)), Pred(B(b))),
                   C("append", C("singleton", F.D(6)),
                       C("dropLast", C("subst", C("phi"), C("returnWord", a,b)))))))))));
    }

    private static Formula V(Formula n) =>
        C("mulVec", C("matrixPower", C("M"), n), C("unit", F.D(6)));
    private static Formula W(Formula n) => C("typeI", n);
    private static Formula P(Formula a, Formula b) => C("parikh", C("returnWord",a,b));
    private static Formula Map(Formula n, Formula a) => C("occurrenceMap",n,a);
    private static Formula Context(Formula x) =>
        Or(Eq(C("word",x),F.D(5)),Eq(C("word",x),F.D(6)));
    private static Formula Ex(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(x),domain,body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula ForEndpoints(Func<Formula,Formula,Formula> body) =>
        All("a",N(),All("b",N(),body(F.Id("a"),F.Id("b"))));

    private static Formula TerminalOccurrence()
    {
        Formula s=F.Id("s"), q=F.Id("q"), a=F.Id("a");
        return All("s",C("List",C("Fin",F.D(7))),All("q",N(),
            Iff(C("Occ",C("terminal",s),q),Ex("a",N(),
                And(Lt(F.D(0),a),And(Eq(q,Sub(C("boundary",a),F.D(1))),
                    And(C("Occ",s,a),And(Context(Sub(a,F.D(1))),
                        Context(Add(a,C("length",s)))))))))));
    }

    private static Formula OrdinaryConsecutive()
    {
        Formula s=F.Id("s");
        return All("s",C("List",C("Fin",F.D(7))),ForEndpoints((a,b) =>
            Iff(C("Consecutive",C("sentinel",s),C("boundary",a),C("boundary",b)),
                C("Consecutive",s,a,b))));
    }

    private static Formula TerminalParikh() => ForEndpoints((a,b) =>
        Imp(Lt(F.D(0),a),Imp(Lt(a,b),Imp(Context(Sub(a,F.D(1))),
            Imp(Context(Sub(b,F.D(1))),Eq(
                P(Sub(C("boundary",a),F.D(1)),Sub(C("boundary",b),F.D(1))),
                C("mulVec",C("M"),P(a,b))))))));

    private static Formula BaseMinimum()
    {
        Formula a=F.Id("a"),b=F.Id("b");
        return And(Ex("a",N(),Ex("b",N(),
            And(C("Consecutive",W(F.D(0)),a,b),
                Eq(C("returnWord",a,b),C("singleton",F.D(6)))))),
            ForEndpoints((x,y)=>Imp(C("Consecutive",W(F.D(0)),x,y),
                Le(C("unit",F.D(6)),P(x,y)))));
    }

    private static Formula FactorParikh()
    {
        Formula n=F.Id("n"),c=F.Id("c");
        return And(All("n",N(),Eq(C("parikh",W(Add(n,F.D(1)))),
            Add(C("mulVec",C("M"),C("parikh",W(n))),C("increment",n)))),
            And(All("n",N(),Eq(C("parikh",W(n)),
                Add(V(n),C("parikhCorrectionSum",n)))),
                All("n",N(),All("c",C("Fin",F.D(7)),
                    Eq(C("parikh",C("image",C("phi"),n,c)),
                        C("mulVec",C("matrixPower",C("M"),n),C("unit",c)))))));
    }

    private static Formula Extensions()
    {
        Formula n=F.Id("n");
        Formula extensions=F.Seq(F.OpenBrace,C("phase",n),F.Comma,F.D(6),F.CloseBrace);
        return All("n",N(),And(Eq(C("Lext",W(n)),extensions),Eq(C("Rext",W(n)),extensions)));
    }

    private static Formula Occurrences()
    {
        Formula n=F.Id("n"),q=F.Id("q"),a=F.Id("a");
        return All("n",N(),All("q",N(),
            Iff(C("Occ",W(Add(n,F.D(1))),q),
                Ex("a",N(),And(Eq(q,Map(n,a)),C("Occ",W(n),a))))));
    }

    private static Formula Consecutives()
    {
        Formula n=F.Id("n");
        return All("n",N(),ForEndpoints((a,b)=>
            Iff(C("Consecutive",W(Add(n,F.D(1))),Map(n,a),Map(n,b)),
                C("Consecutive",W(n),a,b))));
    }

    private static Formula ReturnParikh()
    {
        Formula n=F.Id("n");
        return All("n",N(),ForEndpoints((a,b)=>
            Imp(C("Consecutive",W(n),a,b),
                Eq(P(Map(n,a),Map(n,b)),C("mulVec",C("M"),P(a,b))))));
    }

    private static Formula Minimum()
    {
        Formula n=F.Id("n"),a=F.Id("a"),b=F.Id("b");
        return All("n",N(),And(
            Ex("a",N(),Ex("b",N(),And(C("Consecutive",W(n),a,b),Eq(P(a,b),V(n))))),
            ForEndpoints((x,y)=>Imp(C("Consecutive",W(n),x,y),Le(V(n),P(x,y))))));
    }

    private static Formula N() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula C(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
}
