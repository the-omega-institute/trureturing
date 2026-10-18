using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class ExpandingDiagonalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expanding diagonal products and opposite matching.", H("ExpandingDiagonal"), Blocks(
            Paragraph(Text("Let x and y be nonnegative real vectors and suppose y is decreasing. If the product of x over every subset of k coordinates is bounded by the product of the first k entries of y, then every unitarily invariant diagonal gauge of x is bounded by that of y.")),
            Paragraph(Text("Sort x decreasingly by a finite permutation. Each initial segment of this permutation selects an arbitrary coordinate subset, so the hypothesis gives weak log-majorization. Apply the existing weak-log-majorization sum inequality to each initial restriction to obtain weak majorization. The unitarily invariant gauge theorem and permutation invariance finish the comparison. The hypothesis on all subsets is essential to this route: initial-product bounds on an unsorted vector alone do not suffice.")),
            Paragraph(Text("For positive diagonal weights a and b and an expanding square matrix T, apply the lower Gelfand–Naimark ratio inequality to C = diagonal(a) T diagonal(b) and D = diagonal(1/b). Their product is diagonal(a) T. Expansion increases every singular value under right multiplication. The singular values of D are the reciprocals of b in increasing order. It follows that every subset product of the opposite matching a↓ᵢ b↑ᵢ is bounded by the corresponding initial product of the singular values of C. The preceding diagonal-gauge comparison proves that the opposite-matching permutation is a lower bound for every expanding T.")),
            Paragraph(Text("For nonnegative weights, replace a and b by a + ε and b + ε. The same sorting permutations work for every positive ε. Continuity of the norm and matrix multiplication passes the inequality to ε = 0, preserving a single permutation for all expanding matrices. Thus zeros require neither inverse diagonal matrices at the limit nor a change of permutation.")))));
}
