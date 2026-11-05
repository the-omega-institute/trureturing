using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyRankTwoPathDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/HeadleyRankTwoPath.";

    private static DocumentBlock.Describe Definition(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("headley-rank-two-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constructive unbounded Hamilton path with exactly two occurrences of each circular length below the diameter.",
        H("Headley rank-two circular-length paths"),
        Blocks(
            Definition("circularLength", "Circular distance",
                "For natural n,x,y, circularLength(n,x,y) is min(dist(x,y),n-dist(x,y)), with natural subtraction. The path proof applies it only to vertices between zero and n-1."),
            Definition("steps", "Actual adjacent lengths",
                "For natural n,x and a list p, steps(n,x,p) lists the shorter circular distances along the path starting at x and continuing through p. It includes the edge from x to the first entry and has one entry for each vertex of p; it adds no closing edge."),
            Definition("LengthPath", "Both complete finite inventories",
                "For every natural m, LengthPath(m) is a type of records with a natural-number list tail whose head is m, an exact permutation proof from zero::tail to range(2m), and an exact permutation proof from steps(2m,zero,tail) to m followed by two copies of the list 1 through m-1. Thus zero and the diameter are the first two vertices, every vertex occurs once, the diameter length occurs once, and each smaller positive circular length occurs exactly twice."),
            Describe.Lean(
                DescribeId.Create("headley-rank-two-power-path"),
                DeclarationHandle.Create(Owner + "powerTwoPath"),
                H("One construction for every exponent at least three"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each natural a and proof ha of 3 <= a, powerTwoPath(a,ha) constructs an actual LengthPath(2^(a-1)). The cyclic factor therefore has order 2^a. No path, inventory, graceful sequence or cycle certificate is an argument.")),
                    Paragraph(Text("At half-orders four and eight the constructor consumes the two native words. At larger parameters, write m=2s with s at least eight. The initial word is zero,m,m-1,m+1,...,m-s+1,m+s-1,s. Appending 3s+1,3s,s-2 reaches R(s-2). The right state has terminal alpha, unused vertices [1,alpha-1], alpha+1 and [2m-alpha,2m-1], and missing second lengths 2 through 2alpha+1.")),
                    Paragraph(Text("A recursive block appends 2m-alpha,alpha+1,2m-alpha+2,alpha-1,2m-alpha+1,alpha-3. These are exactly the native R(alpha) to L(alpha-3) to R(alpha-3) transitions. Its lengths are 2alpha,2alpha+1,2alpha-1,2alpha-3,2alpha-2,2alpha-4. Strong induction proves distinct vertices, the precise unused set, distinct missing lengths and the precise deficit interval together. The parameter drops by three. Right parameters three, four and five respectively use L(0), the transition to R(1), and the early L(2) completion. Right state two is never reached on the proved path.")),
                    Paragraph(Text("This is the path input to the two-row R-star base for C2 times C_(2^a). The resulting rank-two bases supply the minimum-exponent-one branch in the Headley noncyclic 2-group induction; the general extension needs an R-cycle on its kernel and an even R-star quotient. A path alone does not supply those permutations, and this module does not assert the arbitrary-subset sequencing problem.")),
                    Paragraph(Text("Attribution: P. Headley, R-sequenceability and R-star-sequenceability of abelian 2-groups, Discrete Mathematics 131 (1994), 345-350, DOI 10.1016/0012-365X(94)90396-4. The formulas follow the supplied native reconstruction and its completed independent mathematical audit. No novelty claim is made."))),
                DescribeRole.Definition))));
}
