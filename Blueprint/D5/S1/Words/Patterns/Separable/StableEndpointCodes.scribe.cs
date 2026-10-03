using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class StableEndpointCodesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed bounded endpoint codes give exact actual successful fibers and mass sums.",
        H("Stable Endpoint Codes"),
        Blocks(
            Paragraph(Text(
                "U(n) consists of the actual permutations of Fin(n) avoiding literal 2413 and 3142. "
                + "State none is U; state some(t) is the actual class with no proper cut of sign t. "
                + "False is direct and true is skew. A Code(K,H) stores only a stop kind or a sign, "
                + "an endpoint length r in 1 through K, its actual bounded shape, and a smaller-horizon "
                + "code. An emitted shape is indecomposable for its sign; a right shape is an arbitrary "
                + "actual avoider of its bounded size. No terminal permutation or n-indexed data is stored. "
                + "Code(K,H) is finite even when K or H is zero.")),
            Paragraph(Text(
                "StableCode(t,m,K,H) is the fixed finite subtype satisfying the actual target and state "
                + "guards. A stop is good when m=0, exhausted for positive m at horizon zero, or cap for "
                + "positive m at positive horizon. An action needs positive unmet target and parent U "
                + "or J(not sign). Emission resets the child state to U and target to max(m-r,0); right "
                + "removal sets the child to J(sign) with unchanged target. For n>H*K, history reconstructs "
                + "actual positive sizes and states by subtracting each bounded endpoint length.")),
            Paragraph(Text(
                "In the displays, t ranges over Option(Bool), and m,B,K,H,n are natural numbers. "
                + "Allowed(t) is the initial source inside U(n): all of U(n) for t=none, and the "
                + "members without a proper cut of sign s for t=some(s). An event A is any subset "
                + "of U(n), and intersect denotes set intersection. mass(n,E) is the original "
                + "full-avoider uniform mass card(E)/card(U(n)), not mass conditional on Allowed(t). "
                + "history(c,n) reconstructs the supplied history from the underlying code c.val. "
                + "Under the full threshold, codeFiber(c) denotes Fiber(m,B,H,K,(history(c,n),terminal(c))), "
                + "the actual deterministic classifier fiber; terminal(c) means terminal(c.val). "
                + "Recompression returns an Option(Code(K,H)), so some(c.val), not c, is its result.")),
            Describe.Lean(
                DescribeId.Create("stable-success-fibers"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/StableEndpointCodes.stable_success_fibers"),
                H("Complete successful supplied-history fibers"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("n"), Gt, F.Id("H"), Star, F.Id("K"), Plus,
                    Call("max", Seq(D(2), Star, F.Id("K")), Call("max", F.Id("m"), F.Id("B"))),
                    Implies, Forall, Sp, F.Id("c"), Colon,
                    Call("StableCode", F.Id("t"), F.Id("m"), F.Id("K"), F.Id("H")), Comma, Sp,
                    Call("terminal", F.Id("c")), Eq, F.Id("good"), Implies,
                    Forall, Sp, F.Id("pi"), InMacro, Call("Avoider", F.Id("n")), Comma, Sp,
                    Call("Fiber", F.Id("m"), F.Id("B"), F.Id("H"), F.Id("K"),
                        Seq(Open, Call("history", F.Id("c"), F.Id("n")), Comma, F.Id("good"), Close),
                        F.Id("pi")), Iff,
                    Call("Event", Call("history", F.Id("c"), F.Id("n")), F.Id("pi"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural K,H, every state t, targets m,B and length n with "
                    + "n>H*K+max(2*K,max(m,B)), every stable code c with terminal kind good, and every "
                    + "actual avoider pi, the deterministic classifier fiber of (history(c,n),good) "
                    + "is exactly the complete supplied-history event. Every actual leaf is selected. "
                    + "The recovered minimum cut and its unique actual Cartesian factors force each "
                    + "recorded action. A right action has left length greater than K because its "
                    + "right length is at most K and the parent size is greater than 2*K; left precedence "
                    + "is not assumed. At the good stop, the target is met and the remaining size exceeds B."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stable-code-transport"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/StableEndpointCodes.stable_code_transport"),
                H("Stable reconstruction and actual recoding"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("n"), Gt, F.Id("H"), Star, F.Id("K"), Implies,
                    Forall, Sp, F.Id("c"), Colon,
                    Call("StableCode", F.Id("t"), F.Id("m"), F.Id("K"), F.Id("H")), Comma, Sp,
                    Call("compress", Call("history", F.Id("c"), F.Id("n")),
                        Call("terminal", F.Id("c")), F.Id("K"), F.Id("H")), Eq,
                    Call("some", Seq(F.Id("c"), Dot, F.Id("val")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every stable code and n>H*K, its reconstructed supplied history has at most H "
                    + "steps, every endpoint size is at most K, and its word at every alphabet and low "
                    + "offset equals the code word. Recompression with its terminal kind recovers the "
                    + "code exactly. A good code emits at least m positions. Above the full threshold, "
                    + "boundedClassify acts on each actual carrier member and its decoded history and "
                    + "terminal kind equal the actual deterministic explorer outcome. Thus every actual "
                    + "outcome is represented by a code from a family independent of n, not by an "
                    + "n-dependent classifier-image catalog."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stable-finite-mass-sums"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/StableEndpointCodes.stable_finite_mass_sums"),
                H("Fixed-family exact restricted sums and successful products"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("n"), Gt, F.Id("H"), Star, F.Id("K"), Plus,
                    Call("max", Seq(D(2), Star, F.Id("K")), Call("max", F.Id("m"), F.Id("B"))),
                    Implies, Forall, Sp, F.Id("A"), Subseteq, Call("Avoider", F.Id("n")), Comma, Sp,
                    Call("mass", F.Id("n"), Call("intersect", Call("Allowed", F.Id("t")), F.Id("A"))),
                    Eq, new Formula.Subscript(Sum, Seq(F.Id("c"), Colon,
                        Call("StableCode", F.Id("t"), F.Id("m"), F.Id("K"), F.Id("H")))), Sp,
                    Call("mass", F.Id("n"), Call("intersect", Call("codeFiber", F.Id("c")), F.Id("A")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every state t and natural m,B,K,H,n above n>H*K+max(2*K,max(m,B)), "
                        + "each allowed actual permutation has a unique stable code. For every code, "
                        + "its actual fiber cardinality is exactly the selected terminal-leaf cardinality. "
                        + "Its mass conditional on the actual initial source is history.weight times "
                        + "card(selected leaves)/card(all leaves). On good codes the fiber is the complete "
                        + "history event and its conditional mass is exactly history.weight, the true "
                        + "finite product of actual child-to-parent carrier cardinality ratios. "
                        + "The left numerator is the actual U child count; the right numerator is the "
                        + "actual J(sign) child count, not an independent replacement law.")),
                    Paragraph(Text(
                        "For every actual event A, its intersection with the initial source has count "
                        + "and full-class uniform mass equal to the finite sums over all "
                        + "StableCode(t,m,K,H) of its intersections with the corresponding fibers. "
                        + "For every predicate on List(Option(Fin B)), the literal first-m-coordinate "
                        + "cylinder mass is the sum of cylinderMass. A successful summand is zero when "
                        + "the predicate rejects the stable code word, and otherwise initial-source "
                        + "mass times the true history product. A non-successful summand retains its "
                        + "actual restricted tested fiber mass. The same fixed-family identity holds "
                        + "for the absolute zero-based test pi(i)!=i at every i<m, using noFixedMass "
                        + "and the code word in alphabet m. Offsets and pending right suffixes remain literal.")),
                    Paragraph(Text(
                        "Cap fibers are not assigned unrestricted leaf counts: n=4,m=B=H=K=1 "
                        + "in state U has four selected cap leaves out of twenty-two full leaves. "
                        + "The symbolic formulas include zero cap, zero horizon and zero target. "
                        + "Count-ratio asymptotics, sign-half, the infinite coupled law, truncation "
                        + "tails, occupation, discrepancy, filtration, hitting and the full all-length "
                        + "derangement-ratio limit remain distinct mathematical questions."))),
                DescribeRole.Theorem))));
}
