using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class QuiverTreePhysicalCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/LeeYang/QuiverTreePhysicalCounterexample.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fiolmartinezmontoyariosfukelman2020quiver");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-vertex physical tree polynomial has an off-circle root at tau minus one.",
        H("An exact physical counterexample on 122 labelled edges"),
        Blocks(
            Definition("endpointFactor", "The physical endpoint factorial factor",
                "Equation (2.15) supplies f(t)=(2t)!/((t-1)!t!). Factorials are cast "
                + "to the real field before division. Every endpoint part used in the "
                + "counterexample is either one or two, with f(1)=2 and f(2)=12."),
            Definition("valence", "Incidence valence",
                "The valence counts both source and target incidences. For the actual "
                + "tree these are two at the centre, 61 at each hub, and one at each leaf."),
            Definition("vertexFactor", "Every physical vertex factor",
                "For mass m and valence d this is (m-1)!/(m-d+2)! times every incident "
                + "endpoint factor. Legal positive endpoint parts imply m at least d, "
                + "so the natural-number subtractions agree with the source factorial "
                + "arguments. Native mass assigns k to src; all paper arrows are reversed."),
            Definition("physicalRho", "The all-vertex physical split distribution",
                "The distribution multiplies binomial(2n,2k) over every labelled edge "
                + "and vertexFactor over every vertex. Equation (2.31) prints the upper "
                + "index m, whereas the explicit construction and (2.16)-(2.19) use m+1 "
                + "vertices. This declaration implements the preregistered all-vertex "
                + "interpretation. No published erratum is claimed."),
            Definition("claimPhys", "The physical unit-circle assertion at tau minus one",
                "Issue #17677 fixes all finite named spanning trees with at least two "
                + "edges, fixed labelled totals n(e) at least two, and the actual physical "
                + "distribution. The polynomial is the existing public treePoly, mapped "
                + "from real to complex coefficients. The assertion says that each root "
                + "has complex norm one at tau=-1. It imposes no arbitrary-weight hypothesis."),
            Describe.Lean(
                DescribeId.Create("quiver-tree-physical-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The physical assertion is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Operatorname, Grp(Id("claimPhys"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The fixed tree has a centre, two hubs and 60 distinct leaves at each "
                    + "hub: 123 vertices and 122 edges. The two hub-centre totals are three; "
                    + "the 120 leaf totals are two. There are exactly four labelled splits. "
                    + "The full physical factors give weights C times (9,244,244,7442), "
                    + "where C=900(60!) squared times 12 to the power 120 is positive. "
                    + "The actual spin sum at tau=-1 is C(1-X) to the power 122 times "
                    + "Q=7442 S62 squared (1+X squared)+488 S62 S61 (1+X cubed) "
                    + "+9 S61 squared (1+X to the fourth), with Sm the finite geometric sum. "
                    + "A Hermitian completed square excludes unit roots with real part "
                    + "at least 9/10. Complex factorization counts every root occurrence. "
                    + "The first two derivative evaluations at one then force "
                    + "2J2-4402J0 at most zero, while exact coefficients give 1276511376. "
                    + "This supplies an actual off-circle complex root and transfers it "
                    + "through the physical polynomial identity. The ancillary generic "
                    + "strict coefficient statement in the earlier source attempt was "
                    + "rejected: F=1 at n=0 would require 0<0. Its authored correction "
                    + "requires a natural n with 1<=n and degree 2n; that corrected "
                    + "generic statement has not received independent review. The fixed "
                    + "Lean route uses a non-strict bound valid for every finite root "
                    + "multiset, followed by the positive numerical gap, and asserts no "
                    + "generic strict theorem. This settles the registered tau=-1 assertion, "
                    + "without classifying other tau, product weights, smaller trees or "
                    + "Conjecture 2. The 2026-10-21 bounded literature screen found no "
                    + "settlement in its searched scope; it is not exhaustive or a "
                    + "priority or minimality claim.")),
                    Paragraph(Text(
                    "The source factors can be checked before expanding any polynomial. "
                    + "Every leaf contributes 0! f(1)/2!=1. A hub with distinguished "
                    + "part k contributes 2^60 f(k)(59+k)!/(k+1)!, and the centre "
                    + "contributes f(3-k)f(3-l)/(6-k-l). The pendant binomials "
                    + "contribute 6^120 and the two remaining binomials contribute "
                    + "15 each. Thus the four displayed weights are reductions of "
                    + "the original physical product, including every vertex. "
                    + "For each fixed split, parity of the opposite-spin edge count "
                    + "gives the product over vertices of 1+(-1)^d X^m. Substituting "
                    + "the centre, hub and leaf masses gives the stated identity "
                    + "P=C(1-X)^122 Q through the public spin-sum definition.")),
                    Paragraph(Text(
                    "Here is the algebraic square used on the unit circle. Put "
                    + "a=1-z^62, b=1-z^61, c=Re(z), K=(z+conj(z)^2)/2, "
                    + "h=7442c, d=9(2c^2-1), and "
                    + "E=h|a|^2+488 Re(a conj(b) K)+d|b|^2. The raw expression "
                    + "(1-z)^2 Q(z) equals -2 z^63 E when |z|=1. The identity "
                    + "hE=|ha+244 conj(K)b|^2+(hd-244^2|K|^2)|b|^2 "
                    + "completes the square. Since |K|^2=(1+4c^3-3c)/2, its "
                    + "determinant term is 7442(2c^3+3c-4), positive for c>=9/10. "
                    + "A root there would force a=b=0, hence z^61=z^62=1 and "
                    + "z=1. The value Q(1)=60972306 excludes that final case.")),
                    Paragraph(Text(
                    "The contradiction counts roots with their full multiplicities; "
                    + "it needs no choice of conjugate pairs or distinct-root assumption. "
                    + "For the full root multiset define v=sum 1/(1-r) and "
                    + "w=sum (1/(1-r))^2. Differentiating the root product gives "
                    + "Q'(1)=Q(1)v and Q''(1)=Q(1)(v^2-w). The exact values are "
                    + "Q'(1)=3780282972=62Q(1) and Q''(1)=269676602388. "
                    + "If all roots were unit roots, the excluded arc would give "
                    + "Re(1/(1-r)-(1/(1-r))^2)=1/(2(1-Re(r)))<5 for each "
                    + "occurrence. Degree at most 124 therefore gives "
                    + "Re(v-w)<=620, so Re(w)>=-558 and Q''(1)<=4402Q(1). "
                    + "The exact difference Q''(1)-4402Q(1)=1276511376 is positive. "
                    + "Equivalently, with J0=Q(1) and J2=Q''(1)/2, this is "
                    + "2J2-4402J0>0. Only a non-strict multiset sum bound is used "
                    + "in the Lean contradiction, so no positive-cardinality "
                    + "hypothesis is missing from a generic strict sum statement."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fiol-martinezmontoya-riosfukelman-2020-tree-lee-yang"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create("quiver-tree-physical-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
