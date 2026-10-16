using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class CompactSmoothPostcompositionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/CompactSmoothPostcomposition.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Inst(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp);
    private static Formula C(Formula x, Formula y) => Call("ContinuousMap", x, y);
    private static Formula C(string x, string y) => C(V(x), V(y));
    private static Formula L(Formula x, Formula y) => Call("ContinuousLinearMap", V("k"), x, y);
    private static Formula Compose(Formula f, Formula g) => Call("comp", f, g);
    private static Formula Post => Seq(V("g"), Sp, Mapsto, Sp, Compose(V("f"), V("g")));
    private static Formula Derivative => Call("bundle", Call("fderiv", V("k"), V("f")));
    private static Formula Apply(Formula a) => Call("applyContinuousLinearMap", a);
    private static Formula[] Context(bool smooth) => [
        Seq(All("K", Call("Type", V("a"))), Inst("TopologicalSpace", V("K")), Inst("CompactSpace", V("K"))),
        Seq(All("k", Call("Type", V("b"))), Inst("NontriviallyNormedField", V("k")),
            smooth ? Inst("IsRCLikeNormedField", V("k")) : Seq()),
        Seq(All("E", Call("Type", V("u"))), Inst("NormedAddCommGroup", V("E")), Inst("NormedSpace", V("k"), V("E"))),
        Seq(All("F", Call("Type", smooth ? Call("max", V("u"), V("v")) : V("v"))),
            Inst("NormedAddCommGroup", V("F")), Inst("NormedSpace", V("k"), V("F")))
    ];
    private static Formula Smooth(Formula n, Formula f) => Call("ContDiff", V("k"), n, f);
    private static Formula OperatorType => L(C(V("K"), L(V("E"), V("F"))), L(C("K", "E"), C("K", "F")));
    private static Formula Definition => Disp(new Formula.Aligned([
        .. Context(false), Seq(Call("applyContinuousLinearMap"), Colon, Sp, OperatorType)
    ]));
    private static Formula Evaluation => Disp(new Formula.Aligned([
        .. Context(false), Seq(All("A", C(V("K"), L(V("E"), V("F")))), All("g", C("K", "E")), All("x", V("K"))),
        Seq(Call("apply", Apply(V("A")), V("g"), V("x")), Sp, Eq, Sp,
            Call("apply", Call("apply", V("A"), V("x")), Call("apply", V("g"), V("x"))))
    ]));
    private static Formula Differentiability => Disp(new Formula.Aligned([
        .. Context(true), Seq(All("f", C("E", "F")), Smooth(Num(1), V("f")), Sp, Rightarrow),
        Seq(All("g", C("K", "E")), Call("HasFDerivAt", Grp(Post),
            Apply(Compose(Derivative, V("g"))), V("g")))
    ]));
    private static Formula Regularity => Disp(new Formula.Aligned([
        .. Context(true), Seq(All("n", Call("NatInfinity")), All("f", C("E", "F"))),
        Seq(Smooth(Call("toOrder", V("n")), V("f")), Sp, Rightarrow, Sp,
            Smooth(Call("toOrder", V("n")), Grp(Post)))
    ]));
    private static AssessedProvenance Source => AssessedProvenance.FromLiterature(
        LibraryNoteRef.Create("D5/L/Topology/tauceti2026smoothpostcomposition"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonlinear postcomposition preserves every finite differentiability order and smoothness on continuous maps from an arbitrary compact topological space.",
        H("Smooth postcomposition in the uniform norm"), Blocks(
            Paragraph(Text("ContinuousMap(K,E) denotes continuous maps with their existing sup norm. K is any compact topological space, including empty and infinite spaces. "
                + "The field k is nontrivially normed; the differentiability results also assume IsRCLikeNormedField(k). E and F are normed k-spaces. "
                + "The independent universe levels are a for K, b for k, u for E, and max(u,v) for F in the differentiability results. "
                + "No completeness, finite dimension, Hausdorff assumption on K, globally bounded derivative, or linearity of f is required. "
                + "The bilinear operator and its evaluation identity allow independent E and F universes.")),
            Describe.Lean(DescribeId.Create("pointwise-linear-application"), DeclarationHandle.Create(Owner + "applyContinuousLinearMap"),
                H("Bounded pointwise application"), StatementSource.FromAuthor(Definition), Source,
                Blocks(Paragraph(Text("For A a continuous family of continuous linear maps and g a continuous E-valued map, applyContinuousLinearMap(A)(g) sends x to A(x)(g(x)). "
                    + "The pointwise operator-norm estimate bounds its uniform norm by the product of the uniform norms of A and g. "
                    + "The resulting operator is continuous linear in A and continuous linear in g."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pointwise-evaluation"), DeclarationHandle.Create(Owner + "applyContinuousLinearMap_apply"),
                H("Evaluation of the bilinear operator"), StatementSource.FromAuthor(Evaluation), Source,
                Blocks(Paragraph(Text("Evaluation at every x agrees with actual application of A(x) to g(x). This identity identifies the pointwise derivative in the uniform remainder estimate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-frechet-derivative"), DeclarationHandle.Create(Owner + "hasFDerivAt_postcomp"),
                H("Frechet derivative of nonlinear postcomposition"), StatementSource.FromAuthor(Differentiability), Source,
                Blocks(Paragraph(Text("In this formula bundle(fderiv(k,f)) is the continuous map from E to continuous linear maps E to F, with continuity supplied by ContDiff(k,1,f). "
                    + "The derivative at g applies fderiv(k,f,g(x)) to the increment at x. Compactness of the image of g and continuity of fderiv give a common neighborhood "
                    + "on which the derivative varies by at most any prescribed positive c. The segment mean-value estimate gives the nonlinear remainder bound "
                    + "c times the uniform input distance. This is the Frechet little-o criterion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-finite-and-infinite-orders"), DeclarationHandle.Create(Owner + "contDiff_postcomp"),
                H("Full nonlinear smooth-superposition theorem"), StatementSource.FromAuthor(Regularity), Source,
                Blocks(Paragraph(Text("NatInfinity consists of the natural orders and infinity; toOrder is its canonical inclusion into NatInfinityOmega, the order type used by ContDiff. "
                    + "The lambda variable g ranges over ContinuousMap(K,E), so Post is a map into ContinuousMap(K,F). Order zero follows from continuity of postcomposition. "
                    + "For a successor order, apply the finite-order induction to the continuous derivative family, then compose with the bounded pointwise application operator. "
                    + "The displayed Frechet derivative identifies this derivative with that of postcomposition. The all-finite-orders criterion gives the infinite case. "
                    + "The max(u,v) codomain universe retains the derivative family at the same universe level.")),
                    Paragraph(Text("These are the original selected proofs of the cited source. The nonlinear theorem is a supplier for smooth Picard residuals. "
                    + "It asserts no ODE existence, global-flow, half-density group, strong-continuity, generator, transport-equation or self-adjointness result."))), DescribeRole.Theorem))));
}
