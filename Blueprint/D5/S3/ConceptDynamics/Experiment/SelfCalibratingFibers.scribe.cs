using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class SelfCalibratingFibersDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entire positive shear fibers determine globally attaining causal policies and exact literal action minima.",
        H("Actual Positive Shear Fibers"),
        Blocks(
            Paragraph(Text(
                "Every globally valid original three-read protocol is proved to select a "
                + "positive U or V shear after each positive initial read; this is a "
                + "consequence of arbitrary-history correctness, not an additional policy "
                + "assumption. Every positive source has a positive factorization R=c l "
                + "with one row l fixed throughout the run, and every literal word reads "
                + "l(E(w)c)=trace(E(w)R).")),
            Paragraph(Text(
                "Fix positive reals x,z and a positive natural k. True denotes U^k with "
                + "rows (1,k),(0,1), and false denotes V^k with rows (1,0),(k,1). "
                + "The upper fiber has rows (x-s,s(x-s)/z),(z,s); the lower fiber has "
                + "rows (x-s,z),(s(x-s)/z,s), with exactly 0<s<x. Both reads are x "
                + "and x+kz. Every compatible positive rank-one source has this form.")),
            Paragraph(Text(
                "For B=E(w)U^k set e=B21; for B=E(w)V^k set e=B12. In both cases "
                + "D=B22-B11 and the third read is t0+Ds+(e/z)s(x-s). "
                + "t0=B11 x+B12 z in the upper branch, and B11 x+B21 z in the lower.")),
            Describe.Lean(DescribeId.Create("self-calibrating-full-fiber-signed-capacity"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Experiment/SelfCalibratingFibers.full_fiber_and_signed_capacity"),
                H("Full-fiber injectivity, literal lengths, and native selected queries"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("upper"), Comma, F.Id("x"), Comma, F.Id("z"), Comma,
                    F.Id("k"), Comma, F.Id("w"), Comma, Sp,
                    Call("PositiveParameters", F.Id("x"), F.Id("z"), F.Id("k")),
                    Sp, Implies, Sp, Call("DerivedSecondShear", F.Id("x")), Sp, Land, Sp,
                    Call("FixedGaugeFactorization"), Sp, Land, Sp,
                    Call("ExactFiber", F.Id("upper")), Sp, Land, Sp,
                    Open, Call("Injective", F.Id("B")), Sp, Leftrightarrow, Sp,
                    F.Id("e"), Sp, Gt, D(0), Sp, Land, Sp,
                    F.Id("e"), Seq(Frac, Grp(F.Id("x")), Grp(F.Id("z"))), Sp, Leq,
                    Lvert, Sp, F.Id("D"), Rvert, Close, Sp, Land, Sp,
                    Call("LiteralMinimum", F.Id("upper")), Sp, Land, Sp,
                    Call("NativeThirdQuery", F.Id("upper")), Sp, Land, Sp,
                    Call("ExactRecoveryRange", F.Id("upper")), Sp, Land, Sp,
                    Call("CausalAttainingPolicy", F.Id("upper")), Sp, Land, Sp,
                    Call("ShortestPrefixAndOptimizedCost", F.Id("upper"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("All quantifiers include the entire open source fiber. "
                        + "If e=0 the raw signed relation forces D=0 and the read is constant. "
                        + "For e>0, injectivity is equivalent to |D|>=e x/z. Equality is "
                        + "allowed because the fiber endpoints are excluded. Failure places "
                        + "a quadratic vertex inside the interval and supplies two interior "
                        + "points with equal third reads.")),
                    Paragraph(Text("Put rho=x/z, m=ceil(rho), and h=(length(w)+1)/2 with "
                        + "natural integer division. Every injective upper continuation has "
                        + "rho<=k+h; every injective lower continuation has rho<=k+h-1. "
                        + "The exact minimum literal lengths are 2 max(0,m-k-1)+1 and "
                        + "2 max(0,m-k)+1. Alternating words starting with M or J attain "
                        + "the respective minima after the same fixed shear endpoint.")),
                    Paragraph(Text("For an OriginalValid native policy selecting a literal "
                        + "second word with that endpoint, the common second history cannot "
                        + "stop. Its third query extends that exact paid word and is injective "
                        + "on every compatible source. Equal third reads would otherwise "
                        + "force the same terminal relation on two different sources. "
                        + "This uses arbitrary history selectors and the same retained "
                        + "source at every read; it assumes no finite candidate normalization. "
                        + "Every successful native run on every compatible source pays at "
                        + "least its original literal prefix length plus the branch minimum; "
                        + "the cost includes its unread terminal tail.")),
                    Paragraph(Text("For every real a>=rho, put f(p)=z+ap+p(x-p)/z and "
                        + "K=x+az>=2x. Its exact image on 0<p<x is z<tau<z+ax. "
                        + "For an actual tau=f(p), the discriminant is (K-2p)^2>0, "
                        + "its positive square root is K-2p, and the other root K-p is "
                        + "strictly beyond x. The stable inverse is "
                        + "p=2z(tau-z)/(K+sqrt(K^2-4z(tau-z))). Upper recovery uses "
                        + "s=p and lower recovery uses s=x-p. The equality K=2x is included.")),
                    Paragraph(Text("Let m=ceil(x/z). The upper policy selects "
                        + "N=max(k,m-1), executes N-k chronological M,J pairs then M, "
                        + "and has actual cumulative endpoint MU^N. The lower policy "
                        + "selects N=max(k,m), executes N-k J,M pairs then J, and has "
                        + "cumulative endpoint JV^N. The increasing coordinate is s "
                        + "above and p=x-s below, with a=N+1 or a=N. The selected words "
                        + "therefore have exactly the stated open ranges and recovery "
                        + "formulas, including the equality boundary.")),
                    Paragraph(Text("Any functions of the initial read may choose direction, "
                        + "positive exponent, and a literal prefix representing that shear. "
                        + "The history-only optimalPolicy preserves this entire prefix. "
                        + "It obtains z=(y-x)/k from the second read, selects the shortest "
                        + "continuation, decodes its actual third read, and stops with no "
                        + "unread tail. On every positive rank-one source native execution "
                        + "has exactly three reads, follows chronological queries, returns "
                        + "the initial relation, and costs the paid prefix plus the exact "
                        + "branch minimum. No correctness premise is imposed on this policy.")),
                    Paragraph(Text("The shortest prefix for U^k or V^k costs exactly 2k. "
                        + "Adding the continuation minima gives C_U=max(2k+1,2m-1) "
                        + "and C_V=max(2k+1,2m+1). These optimized values apply when "
                        + "the prefix is replaced before execution; an already executed "
                        + "redundant prefix always retains its literal paid cost.")),
                    Paragraph(Text("These statements concern exact real reads and literal "
                        + "M/J action counts. They do not bound bit complexity or numerical "
                        + "precision, and no noisy inverse guarantee is asserted."))),
                DescribeRole.Theorem))));
}
