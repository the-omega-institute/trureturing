using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class A398542MinimumRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/A398542MinimumRecurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The upper-minimum split is a bijection of actual fixed-bottom permutations.",
        H("Actual minimum split and cardinal recurrence"),
        Blocks(
            Paragraph(Text(
                "All sizes are natural numbers. Perm(n) means bijections of Fin(n). "
                + "The definitions Actual, Configuration, count, gap and dead are those "
                + "of A398542FixedBottom. Both children always retain the same whole "
                + "bottom b, and their upper values are restandardized. Empty children "
                + "and repeated gaps are allowed. This is the actual-object recurrence "
                + "used to prove the fixed-bottom conjecture preregistered in issue #9332.")),
            Node("IntervalActual", "Actual permutations with restricted gaps",
                "For b in Perm(m) and l,h,k in N, IntervalActual(b,l,h,k) is the "
                + "subtype of Actual(b,k) whose every upper gap, extracted from the "
                + "actual permutation, lies between l and h inclusive. There is "
                + "no change to the bottom alphabet or its ordering."),
            Node("IntervalConfiguration", "The corresponding restricted configurations",
                "For b in Perm(m) and l,h,k in N, IntervalConfiguration(b,l,h,k) "
                + "is the subtype of Configuration(b,k) in which every gap label "
                + "lies in [l,h]. It is the matching restriction of the existing "
                + "actual/configuration equivalence."),
            Node("intervalCount", "Actual interval cardinality",
                "For all b,l,h,k, intervalCount(b,l,h,k) is "
                + "Nat.card(IntervalActual(b,l,h,k)). It is not recursively defined."),
            Node("joinUpper", "The forced value shifts at the minimum",
                "For every a,c, v in Perm(a), and r in Perm(c), joinUpper(v,r) "
                + "is in Perm(a+(c+1)). At the first a positions its values are "
                + "c+1+v(i); at position a its value is zero; at position a+1+j "
                + "its value is r(j)+1. The existing actual blockSum constructor "
                + "is used directly, with the right minimum inserted via finSuccEquiv."),
            Node("join_avoids_iff", "Avoidance of a minimum join",
                "For all a,c and arbitrary v in Perm(a), r in Perm(c), "
                + "joinUpper(v,r) avoids 213 if and only if both v and r avoid 213. "
                + "The factors may be empty. A putative crossing occurrence "
                + "contradicts the strict ordering of the forced value blocks.",
                DescribeRole.Theorem),
            Node("minimum_factorization", "Unique factors of an actual upper permutation",
                "For every a,c and u in Perm(a+(c+1)), if u(a)=0 and u avoids "
                + "213, there is exactly one pair (v,r) in Perm(a) times Perm(c) "
                + "such that joinUpper(v,r)=u and both v and r avoid 213. The "
                + "minimum forces every left value above every right value. "
                + "Bijection of u then forces the exact value sets, including "
                + "when a=0 or c=0.", DescribeRole.Theorem),
            Node("joinGaps", "In-order gap concatenation",
                "For every root gap g in Fin(m+1), left gap function "
                + "v:Fin(a)->Fin(m+1) and right gap function r:Fin(c)->Fin(m+1), "
                + "joinGaps(g,v,r) is the function on Fin(a+(c+1)) given by v, "
                + "then g, then r. The definition itself does not assume "
                + "monotonicity; repeated labels are retained."),
            Node("joinConfiguration", "Reconstruction over one entire bottom",
                "For every b in Perm(m), g in Fin(m+1), l<=g<=h with g<dead(b,g), "
                + "v in IntervalConfiguration(b,l,g,a), and r in "
                + "IntervalConfiguration(b,g,min(h,dead(b,g)-1),c), "
                + "joinConfiguration returns an element of "
                + "IntervalConfiguration(b,l,h,a+(c+1)). The root cutoff constrains "
                + "right gaps; no monotonicity of dead is used. Both children "
                + "keep the same b. The new upper permutation is joinUpper and "
                + "its labels are joinGaps."),
            Node("SplitActual", "Disjoint actual splitting data",
                "For b in Perm(m) and l,h,k in N, SplitActual(b,l,h,k) is the "
                + "dependent sum over g in Fin(m+1) with l<=g<=h and "
                + "a in Fin(k+1) of IntervalActual(b,l,g,a) times "
                + "IntervalActual(b,g,min(h,dead(b,g)-1),k-a). These are actual "
                + "children, each with the complete bottom b. The data describe "
                + "a parent with k+1 upper points."),
            Node("actual_cardinal_recurrence", "The full actual cardinal recurrence",
                "For every m, b in Perm(m) avoiding 132, and natural l<=h<=m, "
                + "write N(l,h,k)=intervalCount(b,l,h,k). Then N(l,h,0)=1. "
                + "For every k in N there exists an equivalence from "
                + "IntervalActual(b,l,h,k+1) to SplitActual(b,l,h,k), and "
                + "N(l,h,k+1) is the sum over all g in [l,h] and a in [0,k] "
                + "of N(l,g,a)*N(g,min(h,dead(b,g)-1),k-a). Finally, for "
                + "every k in N, N(0,m,k)=count(b,k). These are the three "
                + "conclusions of the one theorem. The inverse maps split at "
                + "the unique upper minimum and rejoin with the forced value "
                + "shifts. They treat both empty children and repeated gaps, "
                + "and the zero-size class consists of b alone. In particular "
                + "the source boundary d(b,0)=1 follows.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
