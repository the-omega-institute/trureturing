using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Recurrence;

internal sealed class AlphaUnpredictableAverageRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Dynamics/Recurrence/AlphaUnpredictableAverageRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/akhmettilessov2026integral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A smooth even alpha-unpredictable function has neither ordinary Cesaro mean.",
        H("Alpha unpredictability does not ensure an average"),
        Blocks(
            Describe.Lean(DescribeId.Create("poisson-return"),
                DeclarationHandle.Create(Module + ".PoissonReturn"),
                H("A sequence of uniform returns on bounded intervals"),
                StatementSource.FromAuthor(Disp(All("f", Functions(), All("q", Sequences(),
                    Equal(Call("PoissonReturn", X("f"), X("q")), ReturnBody()))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Journal §2, Definition 1, page 2 of 8: “Definition 1 ([4,10]). A uniformly continuous and bounded on the real axis function f(t) is said to be Poisson stable if there exists a strictly increasing sequence tₙ that approaches infinity, such that the sequence of shifts f(t+tₙ) converges uniformly to the function f(t) on every bounded interval.”")),
                    Paragraph(Text(
                        "PoissonReturn keeps the real return sequence q explicit. Uniform convergence is written as an eventual epsilon estimate on each closed bounded interval. Uniform continuity implies continuity, and the real number M bounds the absolute value on the whole real line."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("poisson-stable"),
                DeclarationHandle.Create(Module + ".IsPoissonStable"),
                H("Poisson stability"),
                StatementSource.FromAuthor(Disp(All("f", Functions(), Equal(
                    Call("IsPoissonStable", X("f")), ExistsOf("q", Sequences(),
                        Call("PoissonReturn", X("f"), X("q"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Journal §2, Definition 1, page 2 of 8: “Definition 1 ([4,10]). A uniformly continuous and bounded on the real axis function f(t) is said to be Poisson stable if there exists a strictly increasing sequence tₙ that approaches infinity, such that the sequence of shifts f(t+tₙ) converges uniformly to the function f(t) on every bounded interval.”")),
                    Paragraph(Text("IsPoissonStable existentially quantifies the real return sequence in PoissonReturn."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("alpha-unpredictable"),
                DeclarationHandle.Create(Module + ".IsAlphaUnpredictable"),
                H("Alpha unpredictability with the same return sequence"),
                StatementSource.FromAuthor(Disp(All("f", Functions(), Equal(
                    Call("IsAlphaUnpredictable", X("f")), AlphaBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Journal §2, Definition 2, page 2 of 8: “Definition 2 ([9]). A Poisson-stable function f(t) is defined as alpha unpredictable if, in addition to having a convergent sequence, there exist a strictly increasing sequence sₙ that tends to infinity, and positive numbers ϵ₀ and δ such that for each index n, the following inequality is satisfied:”")),
                    Paragraph(Text("“|f(t+tₙ)-f(t)|>ϵ₀ for all t∈[sₙ,sₙ+δ].”")),
                    Paragraph(Text(
                        "The displayed source interval is [s n, s n + delta]. Its following prose instead describes a symmetric interval; the formula above follows the displayed inequality. The real sequence q is shared by recurrence and separation. Both q and s are strictly increasing and tend to positive infinity; the positive separation threshold and interval length are independent of n."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Universal existence of an ordinary average"),
                StatementSource.FromAuthor(Disp(Equal(X("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Journal §3, Remark 1, page 7 of 8: “Remark 1. We see that the constant c in (8)—paired with a bounded function g(t)—exists if and only if it equals to the average of f(t). Nevertheless, whether every alpha unpredictable function possesses an average is still an open question.”")),
                    Paragraph(Text(
                        "The source does not define average. The two alternatives quantify ordinary one-sided and symmetric Cesàro limits, respectively. Negating their disjunction denies each universal assertion. The functions and both sequences are real-valued; indices are natural numbers. The value at T = 0 is irrelevant to a limit at positive infinity, and continuity ensures integrability on every compact interval. The question occurs in the journal article; it is absent from arXiv:2608.09809v2. The bounded-remainder assertion in the first sentence is a separate statement."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Neither universal average-existence assertion holds"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Start with the empty binary word. At stage n + 1, append the concatenation of all binary words of length n + 1, followed by a constant block of length (n + 1) squared times one plus the length already written. Its letter is Nat.bodd (n + 1). Each stage extends its predecessor, and its length is at least its index. Reading a fixed position from a sufficiently long stage therefore defines one infinite binary sequence. Every finite word occurs arbitrarily late, while the fraction of ones at a stage endpoint differs from that stage's final letter by at most 1/(n squared + 1).")),
                    Paragraph(Text(
                        "Reflect the unit cells across zero by sending an integer k below zero to -k-1. Cast each binary letter using Bool.toNat to form a bounded measurable step function. Convolve it with the normalized even ContDiffBump centered at zero with inner radius 1/8 and outer radius 1/4. Mathlib's convolution smoothness, normalized mass, plateau and reflection results give an even smooth function bounded in absolute value by one. A uniform integral bound on its derivative gives uniform continuity.")),
                    Paragraph(Text(
                        "Arbitrarily late copies of each reflected central word supply an increasing integer return sequence. The smoothed function agrees exactly with its translate on each sufficiently small central interval. For each of those same shifts q n, an arbitrarily late copy of q n zeroes followed by one supplies a zero plateau whose translate is a one plateau. Choosing increasing plateau centers plus 1/2 gives the divergence sequence, with separation threshold 1/2 and interval length 1/8.")),
                    Paragraph(Text(
                        "Translating an interval changes the integral of the step function by at most twice the translation distance. Fubini and the kernel's radius bound therefore show that smoothing changes each integrated total from zero to T by at most 1/2. At the growing stage endpoints the mean differs from the alternating letter by at most 2/n. A hypothetical limit would then make the constant zero and constant one subsequences have the same limit. Evenness identifies the symmetric mean with the one-sided mean, so this single function defeats both alternatives.")),
                    Paragraph(Text(
                        "Symbolic sequence constructions and convolution realizations of unpredictability appear in Akhmet–Fen, Poincaré chaos and unpredictable functions (arXiv:1608.07301), and Akhmet–Fen–Alejaily, A randomly determined unpredictable function (arXiv:1910.12758v2). Nonconvergent time averages are also part of classical historic behavior. The argument here combines arbitrarily late word occurrences with alternating occupation proportions and an even smooth realization. Exhaustive literature completeness remains ASSUMED-UNVERIFIED; the full Sigmund article and the relevant IOP monograph chapters were not verified in the literature screen.")),
                    Paragraph(Text(
                        "The exact finite checker is in the-omega-institute/trureturing-experiments at commit 8a5ad4a43297e68ef131028eddf08d0eb60c04f2, docs/reports/akhmet-tilessov-2026-alpha-unpredictable-average/check.py, SHA-256 28eafdc7ea3bdac010b391cae6d106e24cba1e51b1e7a7d2f20c27a462349a43; python3 check.py exited 0. It checks finite counts, rational samples and support containment using a polynomial test kernel. It does not establish infinite limits or smoothness, and its enumeration order and sample shifts need not equal those of the noncomputable Lean function."))),
                DescribeRole.Theorem))));

    private static Formula ReturnBody()
    {
        Formula f = X("f"), q = X("q"), t = X("t"), n = X("n"), epsilon = Varepsilon;
        Formula intervalEstimate = All("t", Reals(), Imp(
            Member(t, At(Q("Set", "Icc"), X("a"), X("b"))),
            Less(Abs(Sub(At(f, Add(t, At(q, n))), At(f, t))), epsilon)));
        Formula returns = All("a", Reals(), All("b", Reals(), All(epsilon, Reals(),
            Imp(LeqOf(X("a"), X("b")), Imp(Less(D(0), epsilon),
                ExistsOf("N", Naturals(), All("n", Naturals(),
                    Imp(LeqOf(X("N"), n), intervalEstimate))))))));
        return And(Call("UniformContinuous", f),
            And(ExistsOf("M", Reals(), All("t", Reals(), LeqOf(Abs(At(f, t)), X("M")))),
                And(Call("StrictMono", q),
                    And(Call("Tendsto", q, Q("Filter", "atTop"), Q("Filter", "atTop")), returns))));
    }

    private static Formula AlphaBody()
    {
        Formula f = X("f"), q = X("q"), s = X("s"), t = X("t"), n = X("n");
        Formula epsilon = Seq(Varepsilon, Underscore, Grp(D(0))), delta = DeltaLower;
        Formula separation = All("n", Naturals(), All("t", Reals(), Imp(
            Member(t, At(Q("Set", "Icc"), At(s, n), Add(At(s, n), delta))),
            Less(epsilon, Abs(Sub(At(f, Add(t, At(q, n))), At(f, t)))))));
        return ExistsOf("q", Sequences(), And(Call("PoissonReturn", f, q),
            ExistsOf("s", Sequences(), ExistsOf(epsilon, Reals(), ExistsOf(delta, Reals(),
                And(Call("StrictMono", s), And(
                    Call("Tendsto", s, Q("Filter", "atTop"), Q("Filter", "atTop")),
                    And(Less(D(0), epsilon), And(Less(D(0), delta), separation)))))))));
    }

    private static Formula ClaimBody() => Or(MeanAssertion(false), MeanAssertion(true));

    private static Formula MeanAssertion(bool symmetric)
    {
        Formula f = X("f"), time = X("T"), m = X("m"), t = X("t");
        Formula integral = Seq(Int, Underscore, Grp(symmetric ? Seq(Minus, time) : D(0)),
            Caret, Grp(time), Sp, At(f, t), Sp, F.Id("d"), t);
        Formula denominator = symmetric ? Seq(D(2), Sp, Cdot, Sp, time) : time;
        Formula limit = Call("Tendsto", LambdaOf("T", Reals(),
            new Formula.Fraction(integral, denominator)), Q("Filter", "atTop"), Call("nhds", m));
        return All("f", Functions(), Imp(Call("IsAlphaUnpredictable", f), ExistsOf("m", Reals(), limit)));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] parts) =>
        Seq(Operatorname, Grp(Seq([.. parts.SelectMany((part, index) =>
            index == 0 ? new[] { X(part) } : new[] { Dot, X(part) })])));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula name, Formula type) => Parenthesized(Seq(name, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => All(X(name), type, body);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula ExistsOf(string name, Formula type, Formula body) => ExistsOf(X(name), type, body);
    private static Formula ExistsOf(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Functions() => new Formula.TypeArrow(Reals(), Reals());
    private static Formula Sequences() => new Formula.TypeArrow(Naturals(), Reals());
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, Parenthesized(right));
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LeqOf(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Abs(Formula value) => new Formula.Absolute(value);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Imp(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Rightarrow, Sp, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Lor, Sp, Parenthesized(right));
}
