using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualImageAddressesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualImageAddresses.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw endpoint observations and address sets of ordered Fibonacci source trees.",
        H("Actual Image Addresses"), Blocks(
            Paragraph(Text("Sources are nonempty ordered full binary trees with alpha and beta leaves. "
                + "The substitution sends alpha to beta and beta to (beta,alpha), and preserves pairing. "
                + "Addresses reuse ActualTreeReadoutAcquisition.Address, with false for left and true for right. "
                + "The frozen Reply and readout interface supplies alpha, beta, branch and absent endpoint reports. "
                + "The complete leaf frontier reuses ActualImageSevenLeafSeparation.leafAddresses.")),
            Def("height", "Maximum leaf depth", "Height is the height of the existing ordered shape decomposition. A leaf has height zero."),
            Def("ActualImage", "Actual substitution image", "ActualImage(d) is the range of the d-fold native substitution on complete source trees."),
            Def("Within", "Finite depth window", "Within(h,Q) means that each address in the finite set Q has length at most h."),
            Def("Sound", "Positive address certificate", "Sound(d,V,h,Q) means Within(h,Q) and: every complete tree U with c(U)=c(V) "
                + "and readout(u,U)=readout(u,V) for every u in Q belongs to ActualImage(d). Exact composition is the only competitor promise, "
                + "no prefix-closure condition on Q, and no adaptive or random query order."),
            Def("alphaAddresses", "Alpha leaf addresses", "The finite set contains exactly the root-first addresses of alpha leaves."),
            Def("UnSound", "Certificates without a composition promise", "Every complete source U matching all queried endpoint results must belong to ActualImage(d). No composition or leaf-count constraint is placed on U; the depth window is imposed separately."),
            Def("subtree", "Complete addressed subtree", "The addressed subtree is present exactly when the path reaches a node; otherwise it is absent."),
            Def("replace", "Subtree replacement", "Replacement changes the complete subtree at a valid address and retains the surrounding ordered tree. Invalid paths leave the tree unchanged."),
            Def("AlphaCovered", "Alpha coverage of branches", "Every internal node has an alpha leaf descendant, recursively throughout the tree."),
            Def("rightComb", "Right comb source", "The zero comb is beta. The successor comb pairs alpha on the left with the preceding comb on the right, giving m alpha side leaves and one terminal beta at m right steps."))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-image-address-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
