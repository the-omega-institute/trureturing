using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class RationalIntervalWeightedDistanceDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => Seq(Id(s), Open,
        new Formula.LatexSequence([.. xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x })]), Close);
    private static Formula Pow(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula St(params Formula[] xs) => Disp(new Formula.Aligned([.. xs]));
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), InMacro, Sp, t, Comma, Sp);
    private static Formula ZZ => Seq(Mathbb, Grp(Id("Z")));
    private static Formula NN => Seq(Mathbb, Grp(Id("N")));
    private static Formula HalfPow => Pow(Seq(Frac, Grp(D(1)), Grp(D(2))), Id("n"));
    private static Formula Series => Seq(Open, Id("j"), InMacro, Sp, ZZ, Mapsto, Sp,
        Call("w", Id("j")), Call("d", Call("x", Id("j")), Call("y", Id("j"))), Close);
    private static DocumentBlock.Describe Desc(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("rational-weighted-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance." + name), H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/artigue2025shadowing")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original all-integer geometric weighted sum is summable, continuous in the product topology, and bounded by its exact one-sided tail.",
        H("Rational Interval Weighted Distance"), Blocks(
        Paragraph(Text("Let I=[0,1], S=(Z->I), and d be the inherited interval distance. At every integer j put w(j)=2^(-|j|)=(1/2)^|j|. "
            + "Define D(x,y) as the infinite sum over all j in Z of w(j)d(x(j),y(j)). This is Artigue's original weighted-sum expression with the permitted parameter mu=1/2. "
            + "All sums below are actual infinite sums; no coordinate cutoff or alternative product metric replaces D. The existing product topology suffices, and no new metric-space instance is installed.")),
        Desc("geometricWeight_hasSum", "The complete integer weight series",
            St(Call("HasSum", Id("w"), D(3))),
            "The nonnegative integer half has geometric sum two, and the strictly negative half has geometric sum one. The pinned integer HasSum decomposition joins these disjoint halves."),
        Desc("weightedDistance_summable", "Summability for every sequence pair",
            St(Seq(All("x", Id("S")), All("y", Id("S")), Call("Summable", Series))),
            "Every interval distance is at most one. Thus the nonnegative series defining D is dominated by the summable original weight series."),
        Desc("continuous_weightedDistance", "Product-topology continuity of the literal sum",
            St(Seq(Operatorname, Grp(Id("Continuous")), Open,
                Open, Id("x"), Comma, Id("y"), Close, InMacro, Sp, Id("S"), Times, Sp, Id("S"), Mapsto, Sp,
                Call("D", Id("x"), Id("y")), Close)),
            "Each weighted coordinate distance is continuous and uniformly bounded by w(j). The pinned continuous_tsum theorem applies with this summable majorant on S times S."),
        Desc("geometricWeight_negative_tail", "Exact one-sided tail",
            St(Seq(All("n", NN), Sum, Underscore, Grp(Id("j"), InMacro, Sp, ZZ, Comma, Id("j"), Lt, Minus, Id("n")),
                Call("w", Id("j")), Eq, HalfPow)),
            "The nonnegative integer half contributes zero. On j=-(k+1), the condition is n<=k and the weight is (1/2)^(k+1). Reuse the pinned geometric tail sum to obtain exactly (1/2)^n."),
        Desc("weightedDistance_le_negative_tail", "Agreement on a half-line controls all earlier discrepancies",
            St(Seq(All("n", NN), All("x", Id("S")), All("y", Id("S")),
                Open, All("j", ZZ), Minus, Id("n"), Le, Sp, Id("j"), Rightarrow, Sp,
                Call("x", Id("j")), Eq, Call("y", Id("j")), Close, Rightarrow, Sp,
                Call("D", Id("x"), Id("y")), Le, Sp, HalfPow)),
            "All summands on j>=-n vanish. Every remaining distance is at most one, so comparison of genuinely summable series bounds D by the exact tail. "
                + "This is the estimate needed for the original self-tuning antecedent once a counterwitness is shown to agree with its centered true orbit on that half-line. The counterwitness construction and its positive phase defect are not conclusions of this module.")
        )));
}
