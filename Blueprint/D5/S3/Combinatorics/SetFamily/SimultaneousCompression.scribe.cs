using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SetFamily;

internal sealed class SimultaneousCompressionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SetFamily/SimultaneousCompression.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous coordinate deletion for cross-intersecting families with two independent exact-trace measures.",
        H("Simultaneous Weighted Compression"),
        Blocks(
            Describe.Lean(DescribeId.Create("simultaneous-compression-cross-intersection"),
                DeclarationHandle.Create(Prefix + "CrossIntersecting"), H("Cross-intersection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two finite families A and B are cross-intersecting if every X in A "
                    + "has a common element with every Y in B. Each side may contain mutually disjoint sets; "
                    + "the condition compares only opposite sides."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("simultaneous-compression-shift"),
                DeclarationHandle.Create(Prefix + "shift"), H("A local coordinate replacement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shifted trace replaces t by s: shift(s,t,X) is the union of {s} "
                    + "with X minus {t}. The operation is defined for every finite trace."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("simultaneous-compression-family"),
                DeclarationHandle.Create(Prefix + "compressedFamily"), H("One trace becomes one or two traces"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let Omega be the finite feasible trace family. Among members X of A "
                    + "containing t, move exactly those whose shifted trace is absent from A. Retain all other "
                    + "members, insert each moved trace's shifted trace, and also insert its extension by u "
                    + "when that extension belongs to Omega. Finite-set unions count each resulting trace once."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("simultaneous-compression-mass"),
                DeclarationHandle.Create(Prefix + "mass"), H("Exact-trace mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real weight w on finite traces, mass(w,A) is the sum of w(X) "
                    + "over the members X of A. Distinct completions may contribute to a single trace's weight."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("simultaneous-compression-marginal"),
                DeclarationHandle.Create(Prefix + "marginalWeight"), H("The full projection fibre"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reduced weight of R is the sum of w(X) over every feasible X "
                    + "whose deletion of t equals R. This includes all feasible original traces, whether or not "
                    + "they belonged to the selected family. It neither chooses one completion nor discards multiplicities."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exists-simultaneous-weighted-compression"),
                DeclarationHandle.Create(Prefix + "exists_simultaneous_compression"),
                H("A common deletion does not decrease either mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let alpha be any type with decidable equality, Omega a finite family of "
                        + "feasible finite subsets, and A and B subfamilies of Omega. Choose s,t,u with s distinct "
                        + "from both t and u. Every feasible trace containing t must omit s and u, and replacing "
                        + "t by s must remain feasible. Suppose A and B are cross-intersecting. Let w and v be "
                        + "two arbitrary real weights, each nonnegative on Omega. For every feasible X containing t, "
                        + "require separately for w and v that the weight of X equals the weight of its shift "
                        + "plus the weight of the shifted trace extended by u if that extension is feasible, "
                        + "and equals the shifted weight alone otherwise. No equality between w and v is assumed.")),
                    Paragraph(Text("Then there are families C and D in the image of Omega under deletion of t. "
                        + "They remain cross-intersecting after this common deletion, mass(w,A) is at most "
                        + "mass(marginalWeight(Omega,w,t),C), and mass(v,B) is at most "
                        + "mass(marginalWeight(Omega,v,t),D). Each nonempty input side has a nonempty output side, even when all its weights vanish. Empty input families and zero weights are allowed.")),
                    Paragraph(Text("To prove this, first extend the pair to mutually maximal cross-intersecting "
                        + "families inside Omega, using the polar operation twice. In a maximal family, a moved "
                        + "trace's extension target was also absent: otherwise a disjoint opposite trace supplied "
                        + "by maximality would have to contain t and u simultaneously. Each of the two target maps "
                        + "is injective on moved traces, and their images are disjoint because exactly the extension "
                        + "targets contain u. They are also disjoint from retained members. The local equation "
                        + "therefore preserves each maximal family's mass without counting a target twice.")),
                    Paragraph(Text("For cross-intersection after deletion, if both outputs contain s they meet "
                        + "there. Otherwise an output lacking s is retained. A retained trace containing t has its "
                        + "shift already in its original family. Comparing this shifted trace with the opposite "
                        + "original trace rules out an intersection only at t, including when the other output "
                        + "came from a moved trace. Finally, full projection fibres can only increase mass by "
                        + "nonnegativity. The argument uses each side's own weight equation.")),
                    Paragraph(Text("Iteration requires the feasibility, local equations and full projection law "
                        + "on every reduced support. Applying this result to polygon triangulations additionally "
                        + "requires actual conditional completion weights and a condition-preserving ear-slide "
                        + "construction. The present statement assumes the local weight equations; it does not "
                        + "establish those geometric facts or an original-family deficit bound."))),
                DescribeRole.Theorem)), []));
}
