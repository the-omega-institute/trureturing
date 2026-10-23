using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.AlmostDisjoint;

internal sealed class ColorFiberDiagonalDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Statement => Disp(Seq(
        All("Label", V("Type")), Call("Nonempty", V("Label")), Sp, Rightarrow, Sp,
        All("M", Fn(V("Label"), Call("Set", V("Nat")))),
        All("u", Fn(V("Nat"), V("unitInterval"))),
        All("l", Fn(V("Label"), V("unitInterval"))),
        Call("MADFamily", Call("range", V("M"))), Sp, Land, Sp,
        Grp(Seq(All("i", V("Label")), Call("ConvergesOn", V("u"), Call("M", V("i")), Call("l", V("i"))))),
        Sp, Rightarrow, Sp, All("D", Call("Set", V("Nat"))),
        Call("Partitions", V("M"), V("D")), Sp, Rightarrow, Sp,
        All("r", V("unitInterval")), V("r"), Sp, InMacro, Sp,
        Call("ColorSupport", V("M"), V("u"), V("D")), Sp, Rightarrow, Sp,
        Neg, Call("Countable", Call("Fiber", V("M"), V("l"), V("D"), V("r")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every partitioner color support has uncountably many convergent maximal-family labels.",
        H("The maximality diagonal for color fibers"),
        Blocks(
            Paragraph(Text("Information audit is unfinished: the exact source scope and compiled Reg attempt do not establish validated raw source reconstruction. The concrete missing evidence for this theorem is tracked in https://github.com/the-omega-institute/trureturing/issues/16293. This does not add a mathematical assumption or claim a complete adaptive-refinement counterexample.")),
            Paragraph(Text(
                "Partitions(M,D) means that for every label i, either M(i) minus D or M(i) intersected with D is finite. "
                + "Fiber(M,l,D,r) is {i : l(i)=r and M(i) minus D is finite}. "
                + "ConvergesOn and ColorSupport use the exact finite-exception and finite-union-ideal definitions of the preceding modules. "
                + "The label type can be any nonempty type, with no countability or descriptive-set assumption.")),
            Describe.Lean(
                DescribeId.Create("color-support-fiber-uncountable"),
                DeclarationHandle.Create("D5/S3/Topology/AlmostDisjoint/ColorFiberDiagonal.color_support_fiber_uncountable"),
                H("A color support forces an uncountable eventual-color fiber"),
                StatementSource.FromAuthor(Statement), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose the eventual-color fiber were countable and enumerate it, allowing the empty and finite cases through a default label. "
                        + "For every k, ideal support supplies f(k) in D, above k, in the value ball of radius 1/(k+1) at r, "
                        + "and outside the first k enumerated family members. These choices can be made independently. "
                        + "The bound f(k)>k makes its range infinite, and the shrinking balls give convergence to r.")),
                    Paragraph(Text(
                        "Unrestricted maximality supplies a member meeting that range infinitely. Hausdorff separation forces its existing convergence limit to be r. "
                        + "The partitioner hypothesis and the range's containment in D force that member to have the D color. "
                        + "It therefore occurs in the enumeration, but the diagonal construction leaves only finitely many range points in it. This is a contradiction.")),
                    Paragraph(Text(
                        "This proves uncountability, not continuum cardinality. The branch-tail F-sigma formula, perfect-set upgrade, separator elimination, "
                        + "actual compact open-map counterexample and full Ref classification remain outstanding. "
                        + "The Reg mirror checks the exact original theorem type only; a faithful four-slot dependent-family registration is unfinished."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Topology/AlmostDisjoint/NeighborhoodIdeal"))]));
}
