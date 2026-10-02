using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class GenealogicalFiberTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered tree shapes and their leaf labels determine exact composition fibers.",
        H("Composition Fibers and Fibonacci Genealogical Transport"),
        Blocks(
            Paragraph(Text("Sources are nonempty ordered full binary trees. True labels alpha and false labels beta. "
                + "Their composition counts the two leaf labels. The Fibonacci step and quantity are "
                + "M(a,b)=(b,a+b) and q(a,b)=2a+3b.")),
            Def("Source", "Actual sources", "The source type is FreeMagma Bool, with the original ordered tree constructors."),
            Def("substitution", "Native substitution", "The magma homomorphism sends alpha to beta and beta to the ordered pair (beta,alpha)."),
            Def("composition", "Actual leaf composition", "Alpha has composition (1,0), beta has composition (0,1), and pairing adds compositions."),
            Def("Fiber", "Composition fiber", "Fiber(v) consists of actual source trees whose composition equals v."),
            Def("fiberCount", "Catalan and binomial expression", "N(a,b)=catalan(a+b-1) choose(a+b,a). Natural subtraction is truncated at zero."),
            Def("TreeLabels", "Labels on a shape", "A leaf carries one Boolean label, and an internal node carries the labels of its left and right subshapes."),
            Def("assemble", "Assembling a source", "Assembling a shape with its leaf labels produces the actual ordered source tree."),
            Def("decompose", "Decomposing a source", "Decomposition retains the ordered shape and every leaf label."),
            Def("sourceEquiv", "Shape and label equivalence", "Assembly and decomposition are inverse on all nonempty ordered sources."),
            Def("labelsEquiv", "Indexed leaf labels", "Leaf labels are functions on the left-to-right leaf positions of a shape."),
            Def("indexedEquiv", "Complete indexed encoding", "An actual source corresponds to its ordered shape and its Boolean leaf-position function."),
            Def("positionsEquiv", "Alpha positions", "A Boolean function on finite positions corresponds to the subset of positions labeled alpha."),
            Def("positionedEquiv", "Shape and alpha positions", "An actual source corresponds to its ordered shape and the subset of its alpha positions."),
            Def("fiberEquiv", "Fixed-composition correspondence", "For a+b>=1, actual sources of composition (a,b) correspond to shapes with a+b-1 internal nodes and subsets of exactly a alpha positions."),
            Def("fiberMap", "Actual iterated substitution", "The map from Fiber(v) to Fiber(M^n v) sends a source to its n-th substituted tree."),
            Def("uniformMass", "Real uniform mass", "Each tree in a nonempty fiber has mass 1/card(Fiber(v))."),
            Def("pushedMass", "Actual pushforward mass", "At each target tree, sum the source uniform masses over all source trees whose n-th substituted tree equals that target."),
            Def("transportVariation", "Variation on one target fiber", "Compare the actual pushforward and the uniform target mass using one half of their finite absolute-difference sum."),
            Paragraph(Text("The shape count is the Catalan count in Stanley, Enumerative Combinatorics, Volume 2, section 6.2. "
                + "The shape enumeration and the finite subset count use their corresponding mathlib results.")))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("genealogical-fiber-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
