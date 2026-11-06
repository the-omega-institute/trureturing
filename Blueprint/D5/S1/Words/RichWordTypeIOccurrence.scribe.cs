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
            Paragraph(Text("These boundary and cancellation results do not establish "
                + "the complete Type-I prerequisite. Still required are the all-index "
                + "bidirectional occurrence correspondence at terminal phases, "
                + "exact extension sets with witnesses, the full Parikh recurrence, "
                + "and both existence of a minimum actual consecutive return and the "
                + "componentwise bound for every actual consecutive return. No "
                + "ordinary exponent, richness or Type-II conclusion is asserted.")))));

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
