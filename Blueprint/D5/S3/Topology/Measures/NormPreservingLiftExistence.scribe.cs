using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class NormPreservingLiftExistenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/NormPreservingLiftExistence.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Mass(string name) => Call("totalVariation", V(name), Call("univ"));
    private static Formula Statement => Disp(new Formula.Aligned([
        Seq(All("K", Call("Type", V("u"))), All("L", Call("Type", V("v")))),
        Seq(Call("CompactMetricBorelSpace", V("K")), Sp, Land, Sp,
            Call("HausdorffBorelSpace", V("L")), Sp, Rightarrow),
        Seq(All("p", Seq(V("K"), Sp, To, Sp, V("L"))), Call("Continuous", V("p")),
            Sp, Land, Sp, Call("Surjective", V("p")), Sp, Rightarrow),
        Seq(All("nu", Call("SignedMeasure", V("L")))),
        Seq(Exists, Sp, V("s"), Colon, Sp, Call("SignedMeasure", V("K")), Comma, Sp,
            Call("map", V("s"), V("p")), Sp, Eq, Sp, V("nu"), Sp, Land, Sp,
            Mass("s"), Sp, Eq, Sp, Mass("nu"))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite signed measure on a Hausdorff Borel quotient of a compact metric space has a total-variation-mass-preserving signed lift.",
        H("Existence of total-variation-preserving signed lifts"),
        Blocks(
            Describe.Lean(DescribeId.Create("exists-norm-preserving-lift"),
                DeclarationHandle.Create(Owner + "exists_norm_preserving_lift"),
                H("Signed lift with equal total variation mass"), StatementSource.FromAuthor(Statement),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/wu2026measurableselection")),
                Blocks(
                    Paragraph(Text(
                        "K and L have independent universes. K is any compact metric space with its Borel structure; L is any Hausdorff topological space with its Borel structure. "
                        + "For every continuous surjection p:K to L and every actual finite SignedMeasure nu on L, there is an actual SignedMeasure s on K "
                        + "with map(s,p)=nu and totalVariation(s)(univ)=totalVariation(nu)(univ), an equality in the extended nonnegative reals. "
                        + "Neither carrier nonemptiness nor zero-dimensionality, probability normalization, positivity or finite support is assumed.")),
                    Paragraph(Text(
                        "Selection.Measurable.exists_measurable_right_inverse supplies a measurable q with p(q(y))=y. Define s=map(nu,q). "
                        + "For each measurable A in L, two applications of VectorMeasure.map_apply give map(s,p)(A)=nu(q-preimage(p-preimage(A)))=nu(A). "
                        + "VectorMeasure.ext proves equality of the actual signed measures; no unprovided map-map lemma is used. "
                        + "VectorMeasure.variation_map_le and SignedMeasure.totalVariation_eq_variation first give mass(s) at most mass(nu); "
                        + "applying them along p gives mass(nu) at most mass(s). Antisymmetry proves equality. "
                        + "SignedMeasure is not assigned a normed-space instance. The upstream selector construction is attributed separately from this project bridge.")),
                    Paragraph(Text(
                        "On a compact metric totally disconnected K, classical choice applies this existence theorem to every member of an indexed signed-measure family. "
                        + "The selected family satisfies exactly the pushforward and mass premises of NormPreservingLifts.arbitrary_lifts_tendsto. "
                        + "That existing theorem still requires supported clopen rows, a uniform TV bound, eventual fiber constancy for each fixed locally constant test, "
                        + "and a reference weak-star limit. The existence supplier does not construct those data or provide the reference limit. "
                        + "The CH transfinite A–G recursion, future homeomorphism bookkeeping and the analytic conclusions of Kania–Kąkol Problem 8.2 remain outside this theorem."))),
                DescribeRole.Theorem))));
}
