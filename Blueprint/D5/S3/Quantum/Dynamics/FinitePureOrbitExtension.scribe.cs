using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class FinitePureOrbitExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite prefix in independent subspaces forces an invertible linear orbit to remain in their union.",
        H("Finite pure-direction orbit extension"),
        Blocks(
            Paragraph(Text(
                "Let K be any field, V a finite-dimensional K-vector space of dimension r, "
                + "and A an invertible K-linear map on V. Let S be a finite independent family "
                + "of nonzero subspaces, indexed by a set I with at least two elements. "
                + "Independence means that each subspace has zero intersection with the sum "
                + "of the other subspaces; orthogonality is not required.")),
            Paragraph(Text(
                "For a word w of length L over I, its word space C(w) consists of vectors "
                + "whose j-th iterate lies in S(w(j)) for every j less than L. "
                + "The potential Phi(L) is the sum of max(2 dim C(w)-1,0) over all words "
                + "of length L. Thus zero word spaces contribute zero.")),
            Describe.Lean(
                DescribeId.Create("pure-prefix-potential-stabilizes"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/FinitePureOrbitExtension.pure_prefix_potential_stabilizes"),
                H("Finite prefix, stable potential, and infinite orbit"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a nonzero vector x. If A to the power j applied to x belongs "
                        + "to some S(i) for every j less than 2r-1, then the potential has "
                        + "equal consecutive values at a positive length strictly below 2r-1, "
                        + "and every later iterate of x belongs to the same union of subspaces.")),
                    Paragraph(Text(
                        "Appending a symbol intersects a parent word space with a pulled-back "
                        + "member of S. These child spaces are independent, so their dimensions "
                        + "sum to at most the parent dimension. If no child equals a nonzero "
                        + "parent, the sum of their potential contributions is strictly smaller. "
                        + "Initially the total is at most 2r-2; a surviving nonzero word space "
                        + "at length 2r-1 prevents strict descent at every preceding step.")),
                    Paragraph(Text(
                        "At equality of consecutive potentials, every nonzero word space "
                        + "has an extension equal to itself. Applying A shifts each extended "
                        + "word to its suffix, so the union at the stable length is forward invariant.")),
                    Paragraph(Text(
                        "For a quantum channel, applying this result requires an invariant "
                        + "cyclic tail with invertible induced motion and a decomposition whose "
                        + "members are exactly its pure-input directions. The present theorem "
                        + "establishes the word-space extension after those data are supplied.")),
                    Paragraph(Text(
                        "The companion channel bridge `pure_output_of_kraus_collinear` uses the "
                        + "repository's finite Kraus representation: when every Kraus image of "
                        + "a unit input vector is collinear with one unit output vector and the "
                        + "coefficient weights sum to one, `QuantumChannel.mapState` is `IsPure`.")),
                    Paragraph(Text(
                        "The direction-level result `pure_prefix_channel_directions` applies the "
                        + "potential stabilization to a finite family of such Kraus-pure directions. "
                        + "It returns a pure channel output for every later linear-orbit direction; "
                        + "an equality identifying these directions with the iterated channel states "
                        + "is an additional bridge obligation and is not assumed by the abstract "
                        + "word-space theorem."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        Formula orbit(Formula n) => Seq(F.Id("A"), Caret, Grp(n), F.Id("x"));
        Formula member(Formula n) => Seq(Exists, Sp, F.Id("i"), InMacro, F.Id("I"), Comma, Sp,
            orbit(n), InMacro, F.Id("S"), Underscore, Grp(F.Id("i")));
        Formula bound = Seq(D(2), F.Id("r"), Minus, D(1));
        Formula phi(Formula n) => Call("Phi", n);
        Formula length = F.Id("L");
        Formula j = F.Id("j");
        Formula k = F.Id("k");
        return Disp(Seq(
            Open, F.Id("x"), Neq, D(0), Sp, Land, Sp,
            Forall, Sp, j, Lt, bound, Comma, Sp, member(j), Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, Exists, Sp, length, Comma, Sp, D(1), Le, length, Lt, bound, Sp, Land, Sp,
            phi(Seq(length, Plus, D(1))), Eq, phi(length), Close,
            Sp, Land, Sp, Forall, Sp, k, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
            member(k)));
    }
}
