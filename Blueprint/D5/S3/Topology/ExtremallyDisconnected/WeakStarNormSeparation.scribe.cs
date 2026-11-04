using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.ExtremallyDisconnected;

internal sealed class WeakStarNormSeparationDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Inst(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula ToStrong(Formula value) =>
        new Formula.Apply(Seq(Operatorname, Grp(V("WeakDual"), Dot, V("toStrongDual"))), [value]);
    private static Formula Statement => Disp(new Formula.Aligned([
        Seq(All("u", V("UniverseLevel")), All("v", V("UniverseLevel"))),
        Seq(All("X", Seq(V("Type"), Underscore, Grp(V("u")))),
            Inst("NormedAddCommGroup", V("X")),
            Inst("NormedSpace", Seq(V("Real"), Comma, Sp, V("X")))),
        Seq(All("K", Seq(V("Type"), Underscore, Grp(V("v")))),
            Inst("TopologicalSpace", V("K")), Inst("CompactSpace", V("K")),
            Inst("T2Space", V("K")), Inst("ExtremallyDisconnected", V("K"))),
        Seq(All("h", Seq(V("K"), Sp, To, Sp, Call("WeakDual", V("Real"), V("X")))),
            Call("Continuous", V("h")), Sp, Rightarrow, Sp,
            Call("Injective", V("h")), Sp, Rightarrow, Sp),
        Seq(Exists, Sp, V("c"), Colon, Sp, V("Real"), Comma, Sp,
            D(0), Sp, Lt, Sp, V("c"), Sp, Land, Sp,
            All("p", V("K")), All("q", V("K")), V("p"), Sp, Neq, Sp, V("q"),
            Sp, Rightarrow, Sp, V("c"), Sp, Le, Sp,
            Call("norm", ToStrong( Grp(Seq(
                Call("h", V("p")), Sp, Minus, Sp, Call("h", V("q")))))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact Stonean weak-star embeddings have a uniform positive operator-norm gap.",
        H("Uniform strong-dual norm separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("weak-star-uniform-norm-separation"),
            DeclarationHandle.Create("D5/S3/Topology/ExtremallyDisconnected/WeakStarNormSeparation.exists_pos_le_norm_sub"),
            H("Exact separation theorem"), StatementSource.FromAuthor(Statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "X is any real normed space, and K is any compact Hausdorff extremally disconnected space. "
                    + "The map h is continuous for the weak-star topology and injective. There is one real c greater than zero "
                    + "bounding below the strong-dual norm of h(p)-h(q) for every pair of distinct points. "
                    + "K may be empty or a singleton; neither completeness of X nor a global norm bound is assumed.")),
                Paragraph(Text(
                    "More generally, a lower semicontinuous real function F on K times K that is positive away from the diagonal "
                    + "has a uniform positive lower bound there. Otherwise choose unequal pairs with F less than 1/(n+1). "
                    + "For a fixed clopen U, its symmetric cross (U times its complement) union (its complement times U) is compact. "
                    + "If nonempty, F attains a strictly positive minimum on this cross. The chosen pair eventually misses the cross, "
                    + "since 1/(n+1) tends to zero. If the cross is empty it is always missed. Thus membership in every clopen eventually agrees. "
                    + "PointPairSeparation.eventually_eq_of_eventually_mem_isClopen_iff forces eventual equality, a contradiction. "
                    + "Symmetry and the triangle inequality for F are not needed.")),
                Paragraph(Text(
                    "For the norm theorem, subtraction is continuous in the weak-star topology. Pinned Mathlib's "
                    + "WeakDual.isClosed_closedBall makes every norm sublevel set of the difference closed. "
                    + "This proves lower semicontinuity without asserting continuity of WeakDual.toStrongDual. "
                    + "Injectivity of h and of the linear equivalence toStrongDual gives strict positivity off the diagonal.")),
                Paragraph(Text(
                    "The compact-minimum composition is derived here from the supplied ordinary argument and the point-pair theorem. "
                    + "The CH/Talagrand research context is described in Library/Topology/kania2026talagrand.md. "
                    + "This theorem concerns arbitrary dual functionals, including both signs. It does not construct the CH recursion, "
                    + "the signed dual ball, or the full analytic endpoint."))),
            DescribeRole.Theorem))));
}
