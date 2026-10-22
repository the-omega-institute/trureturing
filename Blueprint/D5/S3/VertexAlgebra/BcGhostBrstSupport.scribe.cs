using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostBrstSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/BcGhostBrstSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual ghost deletion and the support needed for an algebraic BRST charge.",
        H("Actual Ghost BRST Support"),
        Blocks(
            Paragraph(Text("K is any commutative ring, including the zero ring. A ghost state is "
                + "a finitely supported K-linear combination of finite subsets of N. The occupied "
                + "set is the union of the subsets in its coefficient support. The existing signed "
                + "creation and deletion operators, b, c, normalPair and L are used without "
                + "replacement by an abstract representation. Write B(g)=sup(occupied(g)), "
                + "with sup(empty)=0.")),
            Describe.Lean(
                DescribeId.Create("bcghostbrstsupport-occupied-annihilate-subset"),
                DeclarationHandle.Create(Prefix + "occupied_annihilate_subset"),
                H("Actual deletion cannot add an occupied site"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every site i and every state g, the occupied set of "
                    + "annihilate(i)g is contained in occupied(g) with i erased. Every nonzero "
                    + "output basis coefficient originates in a supported input subset containing "
                    + "i, and its subset is exactly that input subset with i erased. Cancellation "
                    + "can remove coefficients but cannot create any other output subset."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostbrstsupport-c-vanish-below"),
                DeclarationHandle.Create(Prefix + "c_vanish_below"),
                H("The shifted c-mode has an input-dependent lower tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If n<-B(g)-2, then c(-n)g=0. This is the actual "
                    + "annihilation branch: its even site 2(-n-2) exceeds every occupied site "
                    + "of g. In the n<=-2 branch, deletion also bounds the occupied set of "
                    + "c(-n)g by that of g."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostbrstsupport-expanded-support-rectangle"),
                DeclarationHandle.Create(Prefix + "expanded_support_rectangle"),
                H("The actual expanded array has joint finite support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The array is c(-n)normalPair(n+k,-k)g for n>=-1, "
                    + "and normalPair(n+k,-k)c(-n)g for n<=-2. Its support lies in the "
                    + "finite rectangle [-B(g)-2,2B(g)+4] times [-(3B(g)+8),3B(g)+8]. "
                    + "The low tail kills the right c(-n). The high tail applies the original "
                    + "BcGhostStressTails.normal_pair_high to every actual pair before "
                    + "applying c(-n). In shifted rows, occupied(c(-n)g) is contained in "
                    + "occupied(g), by actual deletion origin. The shifted occupied supremum is "
                    + "bounded by B(g); hence the shifted cutoff is at most B(g)+abs(n)+4, "
                    + "and therefore at most 3B(g)+8 on the retained outer interval. "
                    + "The shifted cutoff is not silently replaced by an unshifted assumption. "
                    + "This is joint support of the actual two-index array, not only separate "
                    + "finiteness of each row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostbrstsupport-normalghost-support-interval"),
                DeclarationHandle.Create(Prefix + "normalGhost_support_interval"),
                H("The normally ordered ghost summand has a finite outer interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("N_n g=c(-n)L_n g for n>=-1, and L_n c(-n)g "
                    + "for n<=-2. Its support in n lies in [-B(g)-2,2B(g)+4]. "
                    + "N_n directly reuses BcGhostStressTails.outerNormalPair; no replacement "
                    + "operator or forwarding alias is defined. L_n is the actual statewise "
                    + "finite weighted normal-pair sum. "
                    + "A nonzero outer value requires a nonzero expanded entry, so the "
                    + "outer bound follows from the joint rectangle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostbrstsupport-expanded-joint-sum"),
                DeclarationHandle.Create(Prefix + "expanded_joint_sum"),
                H("Finite double-interval evaluation of the actual joint sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pointwise finsum over (n,k) of "
                    + "(n-k) expanded(g,(n,k)) is the double finite sum on the stated "
                    + "rectangle. normalGhost_joint_finsum identifies the outer finsum "
                    + "of N_n g with that same joint sum. The coefficient is n-k, "
                    + "not n+k. These are construction identities, consumed by the actual "
                    + "tensor charge evaluation; they are not independent novelty claims."))),
                DescribeRole.Theorem),
            Paragraph(Text("The construction uses the original public zero-annihilation "
                + "proofs of BcGhostFockSupport, with their arbitrary-CommRing scope. "
                + "No CAR, Virasoro, nilpotence or cohomology claim is implicit in these "
                + "support and summation statements.")))));
}
