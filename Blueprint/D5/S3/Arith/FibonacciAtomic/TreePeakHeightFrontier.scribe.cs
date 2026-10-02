using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class TreePeakHeightFrontierDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first-rejection task has an exact binary-tree peak and height frontier.",
        H("Tree Peak and Height Frontier"),
        Blocks(
            Paragraph(Text("Let n=k+1 be positive. The input is the full product of the five-window "
                + "alphabet at coordinates zero through k. The first-rejection task returns the "
                + "first failed seam, the terminal failure, or acceptance, with the same fixed order "
                + "on every input. T ranges over all full binary trees whose leaves are labelled "
                + "bijectively by these coordinates. Leaf order is unrestricted.")),
            Paragraph(Text("An implementation sends complete discrete messages, uses one coordinate "
                + "at each terminal, and applies a fixed binary function at every fork. A fixed root "
                + "decoder must return the task on every input. There are no other input channels. "
                + "P(T) is the minimum peak number of reachable messages over accurate implementations, "
                + "including the root. Capacity(A) counts the distinct completion responses of a coordinate "
                + "subset A. Height counts task edges. Write H=clog(2,n), and let E be one when n is at "
                + "least four and n=2^H, and zero otherwise.")),
            Describe.Lean(DescribeId.Create("first-rejection-tree-frontier"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/TreePeakHeightFrontier.result"),
                H("Exact Attainable Frontier"),
                StatementSource.FromAuthor(Seq(
                    Call("P", V("T")), Sp, Eq, Sp, Call("maxNodeCapacity", V("T")), Sp, Land, Sp,
                    Call("minPeak", V("n")), Sp, Eq, Sp, Add(V("n"), D(1)), Sp, Land, Sp,
                    Call("minHeight", V("n")), Sp, Eq, Sp, V("H"), Sp, Land, Sp,
                    Call("minHeightAtMinPeak", V("n")), Sp, Eq, Sp, Add(V("H"), V("E")),
                    Sp, Land, Sp, Call("minPeakAtMinHeight", V("n")), Sp, Eq, Sp,
                    Add(Add(V("n"), D(1)), V("E")), Sp, Land, Sp,
                    Grp(Seq(Call("excludesZero", V("A")), Sp, Land, Sp, Call("card", V("A")), Sp, Ge, Sp, D(2),
                        Sp, Implies, Sp, Call("capacity", V("A")), Sp, Ge, Sp,
                        Add(Seq(D(2), Cdot, Call("card", V("A"))), D(2)))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The equality for P holds for every full all-coordinate tree. "
                        + "Each minimum consists of an attaining tree and a lower bound for every "
                        + "tree in its stated class. Thus all trees have peak at least n+1 and height "
                        + "at least H. Among trees with peak n+1, the least height is H+E. Among trees "
                        + "of height H, the least peak is n+1+E. The subset inequality holds for every "
                        + "subset excluding zero and containing at least two coordinates, with no "
                        + "interval assumption.")),
                    Paragraph(Text("For n at least three, split the root into a leading interval of "
                        + "length ceil((n+1)/2) and its trailing complement. Recursively bisect both "
                        + "intervals with the larger half first. Every nonprefix node has length "
                        + "at most floor((n-1)/2), so the interval capacity formulas bound every "
                        + "node by n+1. The resulting height is clog(2,n+1). Ordinary balanced "
                        + "bisection attains height H with peak at most n+2.")),
                    Paragraph(Text("Any full binary tree of edge height h has at most 2^h labelled "
                        + "leaves. At n=2^H and height H, both root children must have n/2 leaves. "
                        + "Disjointness forces one child block to exclude zero; the arbitrary-subset "
                        + "bound then forces peak at least n+2. This also excludes height H among "
                        + "peak-minimal trees. Outside the exceptional case, the biased construction "
                        + "attains both minima. A single terminal and a two-terminal fork handle "
                        + "the two smallest sizes.")),
                    Paragraph(Text("Peak is a single node's message alphabet size, not simultaneous "
                        + "storage. Height counts dependencies, not an unconditional running time. "
                        + "Input access, control, precision, storage, total work and available "
                        + "parallel resources are separate quantities."))), DescribeRole.Theorem))));
}
