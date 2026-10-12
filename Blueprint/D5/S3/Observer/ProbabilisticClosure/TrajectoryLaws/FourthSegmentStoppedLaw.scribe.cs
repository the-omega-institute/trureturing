using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class FourthSegmentStoppedLawDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw.";

    public DocumentDefinition Create()
    {
        Formula r = F.Id("r");
        Formula s = F.Id("s");
        Formula w = F.Id("w");
        Formula b = F.Id("b");
        Formula n = F.Id("n");
        Formula omega = F.Id("x");
        Formula phase = F.Id("ActivePhase");
        Formula word = Call("List", F.Id("Letter"));
        Formula stopped = Call("stoppedReadWord", s);
        Formula value = Call("stoppedReadWord", s, omega);
        Formula raw = Call("rawReadLaw", r);
        Formula family = Call("WordFamily", s, b, w);
        Formula prefix = Call("Prefix", omega, w);
        Formula law = Disp(All(r, F.Id("unitInterval"), All(s, phase,
            Seq(Call("Measurable", stopped), Land,
                Call("map", raw, stopped), Eq, Call("explicitStoppedWordLaw", s, r)))));
        Formula normal = Disp(All(s, phase, All(w, word, All(b, F.Id("Letter"),
            Seq(Call("Parses", Call("active", s), w, b), Leftrightarrow, family)))));
        Formula first = Disp(All(s, phase, All(omega, F.Id("Stream"),
            All(b, F.Id("Letter"), All(n, F.Id("Nat"),
                Seq(Call("FirstStop", F.Id("totalRead"), F.Id("pendingColor"),
                        Call("active", s), omega, b, n), Leftrightarrow,
                    Exists, Sp, w, Colon, word, Comma, Sp,
                    Call("length", w), Eq, n, Land, prefix, Land, family))))));
        Formula fiber = Disp(All(s, phase, All(omega, F.Id("Stream"), All(w, word,
            Seq(value, Eq, Call("some", w), Leftrightarrow,
                prefix, Land, Open, Exists, Sp, b, Colon, F.Id("Letter"), Comma, Sp,
                family, Close)))));
        Formula measurable = Disp(All(s, phase, Call("Measurable", stopped)));
        Formula zero = Disp(All(r, F.Id("unitInterval"), All(s, phase,
            Seq(Call("mass", raw,
                    Seq(OpenBrace, omega, Colon, F.Id("Stream"), Vert, Sp,
                        value, Eq, F.Id("none"), CloseBrace)), Eq, D(0)))));

        Formula prefixStep = Disp(All(omega, F.Id("Stream"), All(n, F.Id("Nat"),
            Seq(Call("readPrefix", omega, Seq(n, Plus, D(1))), Eq,
                Call("cons", Call("head", omega), Call("readPrefix", Call("shift", omega), n))))));
        Formula nonstopp = Call("Nonstop", F.Id("totalRead"), F.Id("pendingColor"),
            Call("active", F.Id("p")), omega);
        Formula nonstopb = Call("Nonstop", F.Id("totalRead"), F.Id("pendingColor"),
            Call("active", F.Id("beta")), omega);
        Formula loopPrefix = Disp(All(omega, F.Id("Stream"), Seq(nonstopp, Rightarrow,
            All(n, F.Id("Nat"), Call("Prefix", omega, Call("loopWord", n))))));
        Formula betaReturn = Disp(All(omega, F.Id("Stream"), Seq(nonstopb, Rightarrow,
            Open, Call("head", omega), Eq, D(0), Land,
                Call("Nonstop", F.Id("totalRead"), F.Id("pendingColor"),
                    Call("active", F.Id("p")), Call("shift", omega)), Close)));
        Formula infiniteNonstop = Disp(All(s, phase,
            Call("Nonstop", F.Id("totalRead"), F.Id("pendingColor"),
                Call("active", s), Call("infiniteTail", s))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Complete stopped Read words from the fourth payload segment.",
            H("First completion and the full stopped-word law"),
            Blocks(
                Node("fourth-prefix-successor", "prefix_succ", "A prefix separates its head",
                    prefixStep, "head(x)=x(0) and shift(x)(i)=x(i+1). For every infinite Read stream and natural n, its n+1 prefix is the head consed onto the n prefix of the shifted stream."),
                Node("fourth-nonstop-loop-prefix", "nonstop_p_prefix", "Every nonstopping p stream contains every loop prefix",
                    loopPrefix, "Nonstop means that no finite trace has a pending completion. loopWord(n)=(beta alpha)^n. This implication retains every natural n and applies to the original totalized Read table."),
                Node("fourth-nonstop-beta-return", "nonstop_beta_return", "A nonstopping suspended stream begins with alpha",
                    betaReturn, "Its head must be alpha=0, and its shifted tail is nonstopping from p under the same totalRead and pendingColor. The two conclusions refer to one stream."),
                Node("fourth-infinite-tail-nonstop", "infinite_tail_nonstop", "Both original alternating infinite tails do not complete",
                    infiniteNonstop, "infiniteTail(p) alternates beta,alpha and infiniteTail(beta) alternates alpha,beta. Every finite trace remains active in the appropriate alternating phase; the original noncompletion outcomes remain in scope."),
                Paragraph(Text("Letters 0 and 1 represent alpha and beta. The two active phases are p and beta. At p, alpha completes bit 0 and beta suspends the parser; at beta, alpha returns to p and beta completes bit 1. Completion reaches pending b. Its sole legal operation is Stop b, leading to delivered. Neither terminal phase permits Read. A state-preserving totalization is used only to evaluate mathematical traces beyond a terminal prefix.")),
                Paragraph(Text("The output is the entire prefix consumed through the least trace index reaching pending. It is some word for finite first completion and none for infinite noncompletion. The alphabet stream has a product measurable structure; the ambient output carrier Option (List (Fin 2)) has the discrete measurable structure. The output definition uses the execution trace, independently of the following word families.")),
                Paragraph(Text("Write L(j) for j repetitions of beta-alpha. At p, the complete words are L(j)-alpha for bit 0 and L(j)-beta-beta for bit 1, for every natural j. At beta, they are the one-letter beta for bit 1, or alpha prepended to a p word. The beta already acquired before the beta-phase cut is absent from the future word.")),
                Node("parses-normal-form", "parses_normal_form", "The exact completion language", normal,
                    "Induction on the finite input word follows the actual Read table. A completing letter permits no additional word suffix. A beta-alpha return restores p without completing. These cases give both directions of the language characterization, including arbitrary return lengths."),
                Node("first-completion-normal-form", "first_completion_normal_form", "First completion and its full prefix", first,
                    "FirstStop is the chronological trace condition: the terminal color is some b at length n and none at every smaller index. Finite parsing is equivalent to that condition on the length-n stream prefix. Thus every actual first completion is exactly a family word, and every matching family prefix is an actual first completion."),
                Node("stopped-word-fiber", "stopped_word_fiber", "Finite output fibers", fiber,
                    "A finite output fiber is its entire chronological prefix cylinder when the word belongs to the completion language, and is empty otherwise. Letters after first completion are not consumed and add no likelihood factors."),
                Node("measurable-stopped-read-word", "measurable_stopped_read_word", "Measurability of first-completion output", measurable,
                    "Each finite fiber is a measurable prefix cylinder or the empty set. The noncompletion fiber is the complement of the countable union of finite fibers. Countability of the output carrier therefore establishes measurability without requiring a countable stream domain."),
                Paragraph(Text("For an arbitrary closed-unit-interval parameter r, rawReadLaw is the homogeneous trajectory law with initial Bernoulli alpha probability r and the same constant Bernoulli transition kernel at every coordinate. Set R=r, S=1-r and A=RS, interpreted as nonnegative extended-real weights. The explicit p law is the sum over all natural j of R A^j times the Dirac measure at some pWord(j,0), plus S^2 A^j times the Dirac measure at some pWord(j,1). The explicit beta law has an S Dirac atom at some [1], followed by atoms of weights R^2 A^j and R S^2 A^j at alpha prepended to the respective p words. There is no Dirac term at none or any invalid finite word.")),
                Node("noncompletion-fiber", "noncompletion_fiber", "The unique infinite continuation",
                    Disp(All(s, phase, All(omega, F.Id("Stream"), Seq(value, Eq, F.Id("none"),
                        Leftrightarrow, Sp, omega, Eq, Call("infiniteTail", s))))),
                    "None occurs precisely on beta-alpha repeated forever from p, or alpha followed by that sequence from beta. The alternating stream remains active at every finite trace index and never delivers Stop. All other streams complete at a finite first index."),
                Node("actual-noncompletion-mass-zero", "actual_noncompletion_mass_zero", "Zero actual mass of infinite noncompletion", zero,
                    "A surviving p execution must repeatedly read beta-alpha. A surviving beta execution must first read alpha, then follow the same returns. Their noncompletion events lie in every such finite prefix cylinder, whose masses are A^j and R A^j. Since A is at most one quarter, these upper bounds tend to zero. This proof includes r=0 and r=1; it retains none in the carrier and does not condition on completion."),
                Node("p-word-mass", "p_word_mass", "Bernoulli mass of each p completion word",
                    Disp(All(r, F.Id("unitInterval"), All(F.Id("j"), F.Id("Nat"),
                        All(b, F.Id("Letter"), Seq(
                            Call("wordMass", r, Call("pWord", F.Id("j"), b)), Eq,
                            Call("if", Seq(b, Eq, D(0)), Call("alphaMass", r),
                                Call("power", Call("betaMass", r), D(2))),
                            Times, Call("power", Seq(Call("alphaMass", r), Times,
                                Call("betaMass", r)), F.Id("j"))))))),
                    "Each return contributes one alpha and one beta factor. The final marker contributes alpha for bit zero and two beta factors for bit one. This coefficient identity is consumed both by the complete-law identification and by finite endpoint event calculations."),
                Node("explicit-finite-mass", "explicit_finite_mass", "All finite singleton masses",
                    Disp(All(s, phase, All(r, F.Id("unitInterval"), All(w, word,
                        Seq(Call("mass", Call("explicitStoppedWordLaw", s, r),
                                Seq(OpenBrace, Call("some", w), CloseBrace)), Eq,
                            Call("if", Seq(Exists, Sp, b, Colon, F.Id("Letter"), Comma,
                                family), Call("wordMass", r, w), D(0))))))),
                    "A valid completion word has its Bernoulli product mass, and every other finite word has zero mass. The disjoint completion-word families identify the unique indexed atom; no renormalization or finite truncation is used."),
                Node("actual-fourth-segment-stopped-word-law", "actual_fourth_segment_stopped_word_law", "The actual full stopped-word law", law,
                    "The prefix-product formula for the constant Bernoulli kernel gives the advertised finite atom masses on the actual first-completion fibers. Infinite noncompletion has mass zero. Equality on all singletons in the countable discrete output carrier proves equality of the two measures. Normalization of the explicit law follows from this equality with the measurable image of a probability law, rather than being an assumption."),
                Paragraph(Text("This is the fixed-parameter raw fourth-segment projection. For a fixed source depth k, substitute its parameter r_k separately. Conditional freshness after random actual histories, the shared-depth posterior mixture, and the measurable correspondence with the full original record and event transcript are separate mathematical bridges. The current phase theorem adds no runtime history, posterior service or future conditioning. Held records B, Qplus and Z must be retained in a full transcript construction. The coherence-price and common-attainment conclusions require further estimates beyond this law.")))));
    }

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, type, Comma, Sp, Open, body, Close);
    private static Formula Call(string name, params Formula[] xs)
    {
        var parts = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++)
        {
            parts[i * 2] = xs[i];
            if (i > 0) parts[i * 2 - 1] = Comma;
        }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(parts), Close);
    }
}
