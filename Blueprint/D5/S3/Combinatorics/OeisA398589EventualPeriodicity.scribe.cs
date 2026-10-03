using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class OeisA398589EventualPeriodicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OeisA398589EventualPeriodicity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/weinstein2026a398589");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every initialized infinite self-banning row of OEIS A398589 is eventually periodic.",
        H("Eventual periodicity of the self-banning rows"),
        Blocks(
            Paragraph(Text("The parameter k ranges over every natural number, including zero. "
                + "Time t starts at zero. The row starts with k and at every later time emits "
                + "the least integer x at least k for which every earlier occurrence at s "
                + "satisfies s+x<t. Thus an occurrence bans its label for exactly the next "
                + "x positions. The infinite row is used throughout; the finite display in "
                + "OEIS stops at the end of the first periodic block.")),
            Describe.Lean(
                DescribeId.Create("a398589-literal-row"),
                DeclarationHandle.Create(Prefix + "row"),
                H("The initialized least-legal row"),
                StatementSource.FromAuthor(RowFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The recursion is total. Among the t+1 candidates "
                    + "k through k+t, at least one is absent from the t previous positions "
                    + "and hence legal. The definition chooses the least legal value over "
                    + "all natural labels, without an imposed bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a398589-eventual-periodicity"),
                DeclarationHandle.Create(Prefix + "eventual_periodicity"),
                H("All rows are eventually periodic"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For k>0, the minimum label k occurs exactly at "
                    + "multiples of k+1. Put B=k(k+2). If every label from k through B "
                    + "were unavailable at a time t, their exclusion witnesses would lie "
                    + "in the same window of at most B positions. The k+1 recent clock "
                    + "occurrences, together with the witnesses for labels above k, give "
                    + "B+1 distinct positions in that window. Thus every term is at most B.")),
                    Paragraph(Text("A state is the actual length-B window with values "
                    + "in {0,...,B}. At time t+B, a candidate x in [k,B] is legal exactly "
                    + "when every matching position i in the window satisfies i+x<B. "
                    + "Earlier occurrences cannot exclude x because x<=B. The transition "
                    + "shifts the window and appends the least eligible label. Its fallback "
                    + "is unreachable on the actual orbit by the bound and the legality "
                    + "equivalence. The initial window is the actual prefix at time zero.")),
                    Paragraph(Text("The finite deterministic generator theorem, with "
                    + "both control and input equal to Unit, gives eventual periodicity "
                    + "of this orbit. The head projection is the original row value. "
                    + "For k=0 every term is zero. No minimal period or preperiod length "
                    + "is asserted, and the separate conjecture about nonempty preperiods "
                    + "for k>2 is outside this result."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a398589-all-row-eventual-periodicity"),
                    ResolutionKind.Proved)))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(Formula k, Formula t) =>
        new Formula.Apply(F.Id("a"), [k, t]);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, b);
    private static Formula All(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Exists(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create(variable), Naturals(), body);

    private static Formula RowFormula()
    {
        Formula k = F.Id("k"), t = F.Id("t"), s = F.Id("s"), x = F.Id("x");
        Formula legal = And(Le(k, x), All("s",
            Implies(And(Lt(s, t), Eq(Call(k, s), x)), Lt(Add(s, x), t))));
        Formula choices = Seq(OpenBrace, x, Sp, Mid, Sp, legal, CloseBrace);
        Formula minimum = new Formula.Apply(Seq(Operatorname, Grp(F.Id("min"))), [choices]);
        return Disp(All("k", And(Eq(Call(k, D(0)), k),
            All("t", Implies(Lt(D(0), t), Eq(Call(k, t), minimum))))));
    }

    private static Formula ResultFormula()
    {
        Formula k = F.Id("k"), n = F.Id("N"), p = F.Id("p"), t = F.Id("t");
        return Disp(All("k", Exists("N", Exists("p", And(Lt(D(0), p),
            All("t", Implies(Le(n, t), Eq(Call(k, Add(t, p)), Call(k, t)))))))));
    }
}
