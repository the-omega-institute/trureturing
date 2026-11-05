using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.RationalRouting;

internal sealed class TwoReplyProfileDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A source-blind finite controller acquires the exact original future-profile cell from at most two genuine replies at one authentic moving cut.",
        H("Original future profiles after actual motion"),
        Blocks(
            Paragraph(Text("Fix one positive rational original x and one source epoch. The finite chronological prefix u is the actual acknowledged L/R action sequence. Its natural matrix A has determinant one, diagonal entries at least one and nonnegative off-diagonal entries. Later letters multiply on the left, so the existing word-matrix convention is applied to the reverse of u. The actual current value is (ax+b)/(cx+d). No source inverse, reset, copy, saved original or unknown-source advice is an instruction.")),
            Paragraph(Text("The finite original interval I must already be earned by actual replies at authentic cuts, or by an earlier acquired archive on that same source. Its positive lower endpoint is included, zero is excluded, and its finite upper endpoint is excluded. The numerical premise is that x belongs to I. The controller receives only I, the known matrix and B; x occurs only in the semantic correctness assertion. Retained actual constraints must be intersected into this working interval before calling the controller. A hypothetical prediction contributes no acquired row.")),
            Describe.Lean(DescribeId.Create("actual-two-reply-original-profile"),
                DeclarationHandle.Create("D5/S3/Observer/RationalRouting/TwoReplyProfile.acquired_original_profile"),
                H("The exact original cell and all future coordinates"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the formula u is an arbitrary finite Boolean word, I a ProfileCell, B a natural and x a rational. The hypotheses are 1<=B, 0<=I.lower and I.Contains x. The typed local definitions bind the attained matrix A, current value z, source-blind program, output C, original upper bound U, raw-scale parameter Q, first interval J, current magnitude bound V and actual rows. The projections a(A), b(A), c(A) and d(A) denote the four natural matrix entries. Thus U=originalUpper(I)=ceil(I.upper), Q=B(cU+d), V=aU+b+1 and M=max(max(a,b),max(c,d)); size=Nat.size, iw=integerWidth and width=ProfileCell.width. For every B at least one, the first proposed scale is Q squared. The output equals the containing original cell, and membership in that cell is exactly equality of the complete common future profile. Its evaluator returns the original floor coordinate for every finite future word and every scale from 1 through B. There is no bound on the unknown original denominator, no bound on future word length, and no literal-history reconstruction.")),
                    Paragraph(Text("First scan the original denominators in I. If the target is already constant, output its cell immediately. Before either possible read, compute the exact lower and upper bounds on that proposed current reply; equality derives the same integer and omits the read. The theorem proves both converses: an already constant target is detected, and every reply constant throughout the working interval is detected by the endpoint test. Otherwise request the complete integer reply at the actual current value. Derived values create no actual-read record, and no separate unit read is requested.")),
                    Paragraph(Text("The first reply has scale Q squared. Inverting its half-open cell and intersecting with I gives J. The lower inverse endpoint is clipped at zero; when the upper raw endpoint reaches or exceeds the image asymptote, it imposes no new upper bound on I. This handles translations with c=0 and the zero original slice. The inverse threshold denominator is aD-cr; the forward transported denominator is cj+dm. These expressions have different roles.")),
                    Paragraph(Text("Every original target cut j/m strictly inside J has m at most B and transported denominator cj+dm at most Q. Two distinct transported fractions with such denominators cannot share one raw cell at scale Q squared. The scan computes the least numerator above the lower endpoint at each original denominator. Repeated fractions identify the same cut. If none occurs, J already determines the full target. Otherwise the current reply at s=cj+dm decides the original side of j/m by comparison with p=aj+bm. This optional second scale is at most Q. Splitting at that cut leaves a single original full-profile class, including exact ownership of a cut equal to the actual source.")),
                    Paragraph(Text("TwoReplyTrace lists the only possible genuine-read traces: no rows, the first row alone, the second row alone after a derived first reply, or both in chronological order. All rows concern the same actual current value. The read-only program type contains no action instruction. Every branch uses finite integer arithmetic, finite denominator scans and at most two supplied finite-completing services. B=1, repeated requested resolutions and noncoprime scales remain in the quantified range.")),
                    Paragraph(Text("The arithmetic scans range over original denominators 1 through B, rather than over Q or an LCM. They use integer divisions and cross-products. The endpoint pass is tail recursive and retains only selected endpoint pairs and its current index. AcquisitionScans gives the exact recursive scan execution: at most 3B integer divisions and 4B integer cross-product comparisons across the initial target test, the post-reply cut test and the final endpoint scan. The first inverse interval and every operand in the two cut scans and final endpoint scan satisfy the displayed uniform W bound. The final reduced endpoint denominators are at most B and their numerator magnitudes are at most BU. The fixed amount of rational endpoint, clipping, derived-reply and representative arithmetic is outside these scan counters. Only the final two selected grid pairs are reduced by the endpoint scan. The theorem also bounds the sum of actual scale-name and reply binary widths, with one delimiter bit per integer, by 6 size(Q)+2 size(V)+4, where size is the natural binary bit length. This bound omits skipped rows and charges complete nonnegative replies. Within each quantified e, the native width formula uses W=acquisitionWidth(A,I,B,e)=16(e+(size(B)+1)+(size(U)+1)+(size(M)+1)+1). These integer sizes bound all listed scan operands. The source resource estimate uses its own conservative widths W=16(e+lambda(B)+lambda(U)+mu+1) and local work O(B W squared+W cubed), with only a constant number of selected-fraction reductions. Request bits, output bits, provenance, matrix replay and service-internal resources are separate charges. The reference in Theorem 39.7 to Proposition 39.10 is a source locator discrepancy: the finite-prefix resource vector is Proposition 39.12. The displayed theorem does not supply an execution-cost relation for every fixed rational operation, a total constant gcd-call bound, a uniform width bound for every intermediate of that full computation, or a schoolbook/Euclid primitive cost binding. The complete numerical bit-work estimate and the literal real-log payload bound with constant 12 remain open."))),
                DescribeRole.Theorem))));

    private static Formula App(string name, params Formula[] arguments) =>
        F.Seq(F.Operatorname, F.Sp, F.Grp(F.Id(name)), F.Open, F.Seq(arguments), F.Close);

    private static Formula Let(string name, Formula type, Formula value) =>
        F.Seq(F.Operatorname, F.Sp, F.Grp(F.Id("let")), F.Sp, F.Id(name), F.Colon, F.Sp,
            type, F.Eq, value, F.Semi, F.Sp);

    private static Formula Naturals() => F.Seq(F.Mathbb, F.Sp, F.Grp(F.Id("N")));
    private static Formula Rationals() => F.Seq(F.Mathbb, F.Sp, F.Grp(F.Id("Q")));

    private static Formula Pow(Formula value, byte exponent) => F.Seq(F.Grp(value), F.Caret, F.Grp(F.D(exponent)));
    private static Formula Size(string name) => App("size", F.Id(name));
    private static Formula Width(string name) => App("width", F.Id(name));
    private static Formula Reply(Formula scale) => App("reply", scale, F.Comma, F.Id("z"));
    private static Formula QSquared() => Pow(F.Id("Q"), 2);

    private static Formula Statement() => F.Disp(F.Seq(
        F.Forall, F.Sp, F.Id("u"), F.InMacro, F.Sp, App("List", App("Bool")), F.Comma,
        F.Id("I"), F.InMacro, F.Sp, App("ProfileCell"), F.Comma,
        F.Id("B"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("N")), F.Comma,
        F.Id("x"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Q")), F.Comma,
        F.D(1), F.Le, F.Sp, F.Id("B"), F.Land, F.Sp, F.D(0), F.Le, F.Sp, App("lower", F.Id("I")), F.Land, F.Sp,
        App("Contains", F.Id("I"), F.Comma, F.Id("x")), F.Longrightarrow, F.Sp,
        F.Begin, F.Sp, F.Grp(F.Id("gathered")),
        Let("A", App("PositiveMatrix"), App("wordMatrix", App("reverse", F.Id("u")))), F.RowBreak, F.Sp,
        Let("z", Rationals(), App("attain", F.Id("u"), F.Comma, F.Id("x"))), F.RowBreak, F.Sp,
        Let("program", App("ProfileProgram"), App("acquireProfile", F.Id("A"), F.Comma, F.Id("I"), F.Comma, F.Id("B"))), F.RowBreak, F.Sp,
        Let("C", App("ProfileCell"), App("execute", F.Id("program"), F.Comma, F.Id("z"))), F.RowBreak, F.Sp,
        Let("U", Naturals(), App("originalUpper", F.Id("I"))), F.RowBreak, F.Sp,
        Let("Q", Naturals(), App("profileScale", F.Id("A"), F.Comma, F.Id("I"), F.Comma, F.Id("B"))), F.RowBreak, F.Sp,
        Let("J", App("ProfileCell"), App("firstInterval", F.Id("A"), F.Comma, QSquared(), F.Comma, F.Id("I"), F.Comma, Reply(QSquared()))), F.RowBreak, F.Sp,
        Let("V", Naturals(), F.Seq(App("a", F.Id("A")), F.Id("U"), F.Plus, App("b", F.Id("A")), F.Plus, F.D(1))), F.RowBreak, F.Sp,
        Let("rows", App("List", Naturals(), F.Times, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Z"))),
            App("actualReads", F.Id("program"), F.Comma, F.Id("z"))), F.RowBreak, F.Sp,
        Let("M", Naturals(), App("max",
            App("max", App("a", F.Id("A")), F.Comma, App("b", F.Id("A"))), F.Comma,
            App("max", App("c", F.Id("A")), F.Comma, App("d", F.Id("A"))))), F.RowBreak, F.Sp,
        F.Id("C"), F.Eq, App("containingCell", F.Id("B"), F.Comma, F.Id("x")), F.Land, F.Sp, F.RowBreak, F.Sp,
        F.Open, F.Forall, F.Sp, F.Id("y"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Q")), F.Comma,
        App("Contains", F.Id("C"), F.Comma, F.Id("y")), F.Iff, F.Sp,
        F.D(0), F.Lt, F.Id("y"), F.Land, F.Sp,
        App("SameFuture", F.Id("B"), F.Comma, F.Id("y"), F.Comma, F.Id("x")), F.Close, F.Land, F.Sp, F.RowBreak, F.Sp,
        F.Open, F.Forall, F.Sp, F.Id("v"), F.InMacro, F.Sp, App("List", App("Bool")), F.Comma,
        F.Id("m"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("N")), F.Comma,
        F.D(1), F.Le, F.Sp, F.Id("m"), F.Le, F.Sp, F.Id("B"), F.Longrightarrow, F.Sp,
        App("evaluate", F.Id("C"), F.Comma, F.Id("v"), F.Comma, F.Id("m")), F.Eq,
        App("reply", F.Id("m"), F.Comma, App("attain", F.Id("v"), F.Comma, F.Id("x"))), F.Close, F.Land, F.Sp, F.RowBreak, F.Sp,
        App("TwoReplyTrace", F.Id("Q"), F.Comma, F.Id("z"), F.Comma, F.Id("rows")), F.Land, F.Sp, F.RowBreak, F.Sp,
        F.Open, App("findCut", F.Id("B"), F.Comma, F.Id("I")), F.Eq, App("none"), F.Iff, F.Sp,
        F.Forall, F.Sp, F.Id("y"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Q")), F.Comma,
        App("Contains", F.Id("I"), F.Comma, F.Id("y")), F.Longrightarrow, F.Sp,
        App("SameFuture", F.Id("B"), F.Comma, F.Id("y"), F.Comma, F.Id("x")), F.Close, F.Land, F.Sp, F.RowBreak, F.Sp,
        F.Open, F.Forall, F.Sp, F.Id("r"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Z")), F.Comma,
        App("determinedReply", F.Id("A"), F.Comma, F.Id("I"), F.Comma, QSquared()), F.Eq, App("some", F.Id("r")), F.Iff, F.Sp,
        F.Forall, F.Sp, F.Id("y"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Q")), F.Comma,
        App("Contains", F.Id("I"), F.Comma, F.Id("y")), F.Longrightarrow, F.Sp,
        App("reply", QSquared(), F.Comma, App("mobius", F.Id("A"), F.Comma, F.Id("y"))), F.Eq, F.Id("r"), F.Close, F.Land, F.Sp, F.RowBreak, F.Sp,
        F.Open, F.Forall, F.Sp, F.Id("s"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("N")), F.Comma,
        F.D(1), F.Le, F.Sp, F.Id("s"), F.Longrightarrow, F.Sp,
        F.Forall, F.Sp, F.Id("r"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Z")), F.Comma,
        App("determinedReply", F.Id("A"), F.Comma, F.Id("J"), F.Comma, F.Id("s")), F.Eq, App("some", F.Id("r")), F.Iff, F.Sp,
        F.Forall, F.Sp, F.Id("y"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Q")), F.Comma,
        App("Contains", F.Id("J"), F.Comma, F.Id("y")), F.Longrightarrow, F.Sp,
        App("reply", F.Id("s"), F.Comma, App("mobius", F.Id("A"), F.Comma, F.Id("y"))), F.Eq, F.Id("r"), F.Close, F.Land, F.Sp, F.RowBreak, F.Sp,
        App("AcquisitionScans", F.Id("A"), F.Comma, F.Id("I"), F.Comma, F.Id("B"), F.Comma, F.Id("z"), F.Comma, F.Id("C")), F.Land, F.Sp,
        App("BoundedReplies", F.Id("Q"), F.Comma, F.Id("V"), F.Comma, F.Id("rows")), F.Land, F.Sp, F.RowBreak, F.Sp,
        App("den", App("lower", F.Id("C"))), F.Le, F.Sp, F.Id("B"), F.Land, F.Sp,
        App("den", App("upper", F.Id("C"))), F.Le, F.Sp, F.Id("B"), F.Land, F.Sp, F.RowBreak, F.Sp,
        App("replyWidths", F.Id("rows")), F.Le, F.Sp, F.D(6), Size("Q"), F.Plus, F.D(2), Size("V"), F.Plus, F.D(4), F.Land, F.Sp, F.RowBreak, F.Sp,
        F.Lvert, F.Sp, App("num", App("lower", F.Id("C"))), F.Rvert, F.Sp, F.Le, F.Sp, F.Id("B"), F.Id("U"), F.Land, F.Sp,
        F.Lvert, F.Sp, App("num", App("upper", F.Id("C"))), F.Rvert, F.Sp, F.Le, F.Sp, F.Id("B"), F.Id("U"), F.Land, F.Sp, F.RowBreak, F.Sp,
        Width("J"), F.Le, F.Sp, App("max", Width("I"), F.Comma,
            F.Seq(App("max", App("size", QSquared()), F.Comma, App("iw", Reply(QSquared()))),
                F.Plus, Size("M"), F.Plus, F.D(3))), F.Land, F.Sp, F.RowBreak, F.Sp,
        F.Open, F.Forall, F.Sp, F.Id("e"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("N")), F.Comma,
        Width("I"), F.Le, F.Sp, F.Id("e"), F.Longrightarrow, F.Sp,
        Let("W", Naturals(), App("acquisitionWidth", F.Id("A"), F.Comma, F.Id("I"), F.Comma, F.Id("B"), F.Comma, F.Id("e"))),
        F.D(4), Width("J"), F.Le, F.Sp, F.Id("W"), F.Land, F.Sp,
        App("CutOperandWidths", F.Id("B"), F.Comma, F.Id("I"), F.Comma, F.Id("W")), F.Land, F.Sp,
        App("CutOperandWidths", F.Id("B"), F.Comma, F.Id("J"), F.Comma, F.Id("W")), F.Close,
        F.End, F.Sp, F.Grp(F.Id("gathered"))));
}
