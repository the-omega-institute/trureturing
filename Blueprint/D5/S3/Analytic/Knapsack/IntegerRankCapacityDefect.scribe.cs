using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Knapsack;

internal sealed class IntegerRankCapacityDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite distinct integer ranks admit a defect-sensitive capacity bound and an exact nonnegative prefix slack.",
        H("Integer-rank capacity and prefix slack"),
        Blocks(
            Paragraph(Text(
                "Let I be a finite set of natural numbers, r a positive natural number, A and N nonnegative real numbers, and c a function from the natural numbers to the reals. Every d in I satisfies r<=d, 0<=c(d)<=A d, and sum over I of c(d)<=N. The ranks are distinct because I is a set; the hypotheses concern total mass at each rank, not separate contributions sharing a rank. All natural-number ranks in real expressions are cast to the reals.")),
            Paragraph(Math(Disp(Definitions()))),
            Paragraph(Text(
                "Write x(d)=c(d)/d, J for total occupancy, B for total mass, D for the sum of coordinate defects, C=(2r-1)A, g(d) for the strict-prefix gap, and H for the occupancy-weighted prefix slack. The function xtilde on natural numbers equals x(i) for i in I and zero otherwise. The interval [r,d) in every formula is the finite natural-number interval, including its lower endpoint and excluding its upper endpoint.")),
            Paragraph(Math(Disp(Seq(Call("g", F.Id("d")), Sp, Eq, Sp, Gap(F.Id("d")), Comma, Sp,
                F.Id("H"), Sp, Eq, Sp, SumI("d", Seq(Call("x", F.Id("d")), Sp,
                    Call("g", F.Id("d")))))))),
            Describe.Lean(
                DescribeId.Create("integer-rank-capacity-defect"),
                DeclarationHandle.Create("D5/S3/Analytic/Knapsack/IntegerRankCapacityDefect.integer_rank_capacity_defect"),
                H("Defect-sensitive capacity and exact prefix saturation"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For all data satisfying the stated hypotheses and definitions, B equals sum d x(d), D is nonnegative, and J squared plus C J plus D is at most 2 A B, which is at most 2 A N. The defect-adjusted radicand C squared plus 8 A N minus 4 D is nonnegative. J is bounded by its quadratic root, and that root itself is bounded by the root with D omitted.")),
                    Paragraph(Text(
                        "The exact identity is J squared plus C J plus D plus 2 H equals 2 A B. Every prefix gap equals the sum of A-xtilde(i) over the natural-number interval [r,d), and each gap and H are nonnegative. If A>0, H=0 if and only if every active rank d, meaning x(d)>0, has every natural number i in [r,d) present in I with x(i)=A. This imposes no saturation requirement on the last active rank itself. If A=0, H=0 without any additional membership conclusion.")),
                    Paragraph(Text(
                        "Induct on the maximum rank a. The old rank set is contained in [r,a), so its cardinality is at most a-r and its total occupancy J0 is at most (a-r)A. Adding x=x(a) increases the square, linear term, and coordinate defect together by 2x(J0+rA), at most the new budget 2Aax. This proves the capacity inequality from distinct integer ranks rather than assuming a prefix-mass bound. Completing the square and using nonnegative J and C gives the first root bound; nonnegative D and monotonicity of the square root give the root-to-root comparison.")),
                    Paragraph(Math(Disp(Seq(F.Id("J0"), Sp, Le, Sp, Open, F.Id("a"), Minus, F.Id("r"), Close,
                        F.Id("A"), Comma, Sp, D(2), F.Id("x"), Open, F.Id("J0"), Plus,
                        F.Id("r"), F.Id("A"), Close, Sp, Le, Sp, D(2), F.Id("A"),
                        F.Id("a"), F.Id("x"))))),
                    Paragraph(Text(
                        "No old prefix changes when the maximum rank is inserted. H increases by x times (A(a-r)-J0), exactly accounting for the unused increment of the main budget and proving the identity by the same maximum-rank induction. Missing prefix ranks contribute A to the gap, while present ranks contribute A-x(i). These terms are nonnegative. When A>0, a zero sum at an active rank excludes missing ranks and forces all its strict-prefix coordinates to equal A; the converse follows by evaluating each weighted gap.")),
                    Paragraph(Text(
                        "The empty set, A=0, and N=0 are permitted. Each of these cases has J=D=H=0, and the displayed capacity and root inequalities remain valid. No infinite-rank statement, repeated-index capacity, or endpoint saturation is asserted."))),
                DescribeRole.Theorem))));

    private static Formula SumI(string index, Formula body) => Seq(Sum, Underscore,
        Grp(F.Id(index), Sp, InMacro, Sp, F.Id("I")), Sp, body);

    private static Formula Prefix(Formula rank) => Seq(Sum, Underscore,
        Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("I"), Comma, Sp, F.Id("i"), Sp, Lt, Sp, rank),
        Sp, Call("x", F.Id("i")));

    private static Formula Gap(Formula rank) => Seq(F.Id("A"), Open, rank, Minus, F.Id("r"),
        Close, Minus, Prefix(rank));

    private static Formula MainTerm() => Seq(F.Id("J"), Caret, D(2), Plus, F.Id("C"),
        F.Id("J"), Plus, F.Id("D"));

    private static Formula Radicand() => Seq(F.Id("C"), Caret, D(2), Plus, D(8),
        F.Id("A"), F.Id("N"));

    private static Formula DefectRadicand() => Seq(Radicand(), Minus, D(4), F.Id("D"));

    private static Formula Root(Formula radicand) => Seq(Frac,
        Grp(Sqrt, Grp(radicand), Minus, F.Id("C")), Grp(D(2)));

    private static Formula Definitions() => Seq(
        Call("x", F.Id("d")), Sp, Eq, Sp, Frac, Grp(Call("c", F.Id("d"))), Grp(F.Id("d")),
        Comma, Sp, F.Id("J"), Sp, Eq, Sp, SumI("d", Call("x", F.Id("d"))),
        Comma, Sp, F.Id("B"), Sp, Eq, Sp, SumI("d", Call("c", F.Id("d"))),
        Comma, Sp, F.Id("D"), Sp, Eq, Sp, SumI("d", Seq(Call("x", F.Id("d")),
            Open, F.Id("A"), Minus, Call("x", F.Id("d")), Close)),
        Comma, Sp, F.Id("C"), Sp, Eq, Sp, Open, D(2), F.Id("r"), Minus, D(1), Close, F.Id("A"));

    private static Formula Statement() => Seq(
        Forall, Sp, F.Id("I"), Colon, Sp, Call("Finset", Call("Nat")), Comma, Sp,
        F.Id("r"), Colon, Sp, Call("Nat"), Comma, Sp, F.Id("A"), Comma, F.Id("N"),
        Colon, Sp, Call("Real"), Comma, Sp, F.Id("c"), Colon, Sp,
        Call("Nat"), Sp, To, Sp, Call("Real"), Comma, Sp,
        Open, D(0), Sp, Lt, Sp, F.Id("r"), Comma, Sp,
        D(0), Sp, Le, Sp, F.Id("A"), Comma, Sp, D(0), Sp, Le, Sp, F.Id("N"), Comma, Sp,
        Open, Forall, Sp, F.Id("d"), Sp, InMacro, Sp, F.Id("I"), Colon, Sp,
        F.Id("r"), Sp, Le, Sp, F.Id("d"), Comma, Sp,
        D(0), Sp, Le, Sp, Call("c", F.Id("d")), Sp, Le, Sp, F.Id("A"), F.Id("d"), Close,
        Comma, Sp, SumI("d", Call("c", F.Id("d"))), Sp, Le, Sp, F.Id("N"), Close,
        Sp, Implies, Sp, Open,
        F.Id("B"), Sp, Eq, Sp, SumI("d", Seq(F.Id("d"), Call("x", F.Id("d")))),
        Comma, Sp, D(0), Sp, Le, Sp, F.Id("D"), Comma, Sp,
        MainTerm(), Sp, Le, Sp, D(2), F.Id("A"), F.Id("B"), Sp, Le, Sp,
        D(2), F.Id("A"), F.Id("N"), Comma, Sp,
        D(0), Sp, Le, Sp, DefectRadicand(), Comma, Sp,
        F.Id("J"), Sp, Le, Sp, Root(DefectRadicand()), Sp, Le, Sp, Root(Radicand()),
        Comma, Sp, MainTerm(), Plus, D(2), F.Id("H"), Sp, Eq, Sp,
        D(2), F.Id("A"), F.Id("B"), Comma, Sp, D(0), Sp, Le, Sp, F.Id("H"),
        Comma, Sp, Open, Forall, Sp, F.Id("d"), Sp, InMacro, Sp, F.Id("I"), Colon, Sp,
        Call("g", F.Id("d")), Sp, Eq, Sp, Sum, Underscore,
        Grp(F.Id("i"), Sp, InMacro, Sp, OpenBracket, F.Id("r"), Comma, F.Id("d"), Close),
        Sp, Open, F.Id("A"), Minus, Call("xtilde", F.Id("i")), Close, Sp, Ge, Sp, D(0), Close,
        Comma, Sp, Open, D(0), Sp, Lt, Sp, F.Id("A"), Sp, Implies, Sp, Open,
        F.Id("H"), Sp, Eq, Sp, D(0), Sp, Iff, Sp, Forall, Sp,
        F.Id("d"), Sp, InMacro, Sp, F.Id("I"), Comma, Sp,
        D(0), Sp, Lt, Sp, Call("x", F.Id("d")), Sp, Implies, Sp,
        Forall, Sp, F.Id("i"), Sp, InMacro, Sp, OpenBracket, F.Id("r"), Comma,
        F.Id("d"), Close, Colon, Sp, F.Id("i"), Sp, InMacro, Sp, F.Id("I"),
        Sp, Land, Sp, Call("x", F.Id("i")), Sp, Eq, Sp, F.Id("A"), Close, Close,
        Comma, Sp, Open, F.Id("A"), Sp, Eq, Sp, D(0), Sp, Implies, Sp,
        F.Id("H"), Sp, Eq, Sp, D(0), Close, Close);
}
