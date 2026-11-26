using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMObservableProductRigidityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMObservableProductRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Grouped modular observability and connected product rigidity for the actual BKM gap.",
        H("Grouped modular observability and connected product rigidity"), Blocks(
            Entry("bkm-gap-ratio-commutation", "bkmGap_eq_zero_iff_commute_ratioPieces",
                "Commutation with whole retained modular ratio groups",
                "Let S be the right partial trace of a positive definite joint matrix A on finite "
                + "spaces with a nonempty environment. For each real v, collect the entries of "
                + "the retained Hermitian observable K for which the row eigenvalue of S equals "
                + "v times the column eigenvalue. The resulting matrix in the original basis "
                + "is the v component of K. The ratio group includes all entries with that ratio, "
                + "including those arising from repeated eigenvalues. The actual BKM gap vanishes "
                + "if and only if the relative density, obtained by sandwiching A with the lifted "
                + "inverse square root of S, commutes with the identity lift of every component. "
                + "To prove the equivalence, apply the modular functional calculus to the "
                + "indicator of each ratio on the fixed weighted observable. The joint modular "
                + "eigen-equation becomes the commutation equation after removing the two marginal "
                + "square roots. Conversely the component eigen-equations give functional "
                + "intertwining on their sum."),
            Entry("bkm-gap-product-marginals", "bkmGap_eq_zero_iff_eq_marginals_kronecker",
                "Exact product of the two marginals for a connected observable",
                "Suppose additionally that A has trace one, the eigenvalues of S are distinct, "
                + "and the graph of nonzero off-diagonal entries of K in that eigenbasis is "
                + "connected. The gap vanishes if and only if A is the Kronecker product of its "
                + "two partial traces. In retained spectral coordinates every auxiliary slice "
                + "of the relative density commutes with all ratio components. Each ratio "
                + "component of a slice inherits these commutations. Its adjoint times itself "
                + "is diagonal and constant along graph edges. A ratio different from one "
                + "has a zero column at a spectral extremum, so its entire component vanishes. "
                + "The remaining diagonal slice is scalar by connectivity. This gives a tensor "
                + "product with the retained identity, and undoing the sandwich and taking "
                + "the left partial trace yields the two actual marginals."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
