using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CIRPT;

internal sealed class SemanticIntegrityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/CIRPT/SemanticIntegrity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant observations and full-domain primitives preserve CIRPT semantic integrity.",
        H("CIRPT Semantic Integrity"),
        Blocks(
            DefinitionNode("constant-cut-bundle", "constantCutBundle", "Constant CUT bundle",
                "Each finite index is assigned the CUT kernel of a constant readout."),
            TheoremNode("closed-truth-universal-kernel",
                "closed_truth_readout_has_universal_kernel",
                "Closed truth has a universal kernel", ConstantKernelFormula(),
                "Every pair has equal values under a constant readout."),
            TheoremNode("constant-cut-bundle-universal-agreement",
                "constant_cut_bundle_has_universal_agreement",
                "Constant CUT bundles agree universally", ConstantBundleFormula(),
                "Coordinatewise universality makes the joint bundle relation universal."),
            DefinitionNode("bundle-with-atom", "bundleWithAtom", "Atom insertion",
                "An Option index inserts one atom while retaining every old atom index."),
            TheoremNode("full-domain-admit-encoding", "full_domain_admit_encoding",
                "ADMIT is its Boolean CUT", AdmitEncodingFormula(),
                "The canonical Boolean characteristic readout has exactly the ADMIT kernel."),
            TheoremNode("admit-antitone-agreement",
                "adding_admit_atom_cannot_increase_agreement",
                "ADMIT cannot increase agreement", AdmitAntitoneFormula(),
                "Every pair accepted by the extended bundle still satisfies every old atom."),
            TheoremNode("admit-preserves-off-diagonal-domain",
                "admit_atom_preserves_offDiagonalPairs",
                "ADMIT preserves the carrier domain", AdmitDomainFormula(),
                "The off-diagonal carrier is independent of atoms, while agreement is antitone."),
            TheoremNode("certificate-anchor-erasure", "certificate_anchor_erasure",
                "Certificates erase to object anchors", AnchorFormula(),
                "The anchor kernel retains only equality with the anchored object."),
            TheoremNode("constant-packed-observer-universal-kernel",
                "constant_packed_observer_has_universal_kernel",
                "Constant packed observers are universal", ObserverFormula(),
                "A proof-derived constant readout cannot distinguish carrier states."),
            TheoremNode("universal-atom-neutrality",
                "universal_kernel_atom_does_not_change_agrees",
                "Universal atoms are neutral", NeutralityFormula(),
                "Inserting a universally relating atom leaves bundle agreement unchanged."))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe TheoremNode(
        string id, string declaration, string title, Formula formula, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ConstantKernelFormula() => Disp(Seq(
        Forall, Sp, F.Id("c"), Comma, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        Call("relation", Call("cutKernel", Seq(LambdaLower, Sp, F.Id("z"), Comma, Sp,
            F.Id("c"))), F.Id("x"), F.Id("y")), Dot));

    private static Formula ConstantBundleFormula() => Disp(Seq(
        Forall, Sp, F.Id("v"), Comma, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        Call("agrees", Call("constantCutBundle", F.Id("v")), F.Id("x"), F.Id("y")), Dot));

    private static Formula AdmitEncodingFormula() => Disp(Seq(
        Forall, Sp, F.Id("A"), Comma, Sp, Call("admitKernel", F.Id("A")), Sp, Eq, Sp,
        Call("cutKernel", Seq(LambdaLower, Sp, F.Id("x"), Comma, Sp,
            Call("decide", Call("A", F.Id("x"))))), Dot));

    private static Formula AdmitAntitoneBody() => Seq(
        Call("agrees", Call("bundleWithAtom", F.Id("b"), Call("admitAtom", F.Id("A"))),
            F.Id("x"), F.Id("y")), Sp, Rightarrow, Sp,
        Call("agrees", F.Id("b"), F.Id("x"), F.Id("y")));

    private static Formula AdmitAntitoneFormula() =>
        Disp(Seq(AdmitAntitoneBody(), Dot));

    private static Formula AdmitDomainFormula() => Disp(Seq(
        Call("offDiagonalPairs", F.Id("X")), Sp, Eq, Sp,
        Call("offDiagonalPairs", F.Id("X")), Sp, Land, RowBreak,
        AdmitAntitoneBody(), Dot));

    private static Formula AnchorFormula() => Disp(Seq(
        Call("relation", Call("anchorKernel", F.Id("a"))), Sp, Eq, Sp,
        Call("ker", Seq(LambdaLower, Sp, F.Id("x"), Comma, Sp,
            Call("decide", Seq(F.Id("x"), Sp, Eq, Sp, F.Id("a"))))), Dot));

    private static Formula ObserverFormula() => Disp(Seq(
        Open, Forall, Sp, F.Id("x"), Comma, Sp,
        Call("observe", F.Id("o"), F.Id("x")), Sp, Eq, Sp, F.Id("c"), Close,
        Sp, Rightarrow, Sp, Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        Call("relation", Call("kernel", Call("toPrimitiveAtom", F.Id("r"), F.Id("o"))),
            F.Id("x"), F.Id("y")), Close, Dot));

    private static Formula NeutralityFormula() => Disp(Seq(
        Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
        Call("relation", Call("kernel", F.Id("p")), F.Id("x"), F.Id("y")), Close,
        Sp, Rightarrow, Sp,
        Open, Call("agrees", Call("bundleWithAtom", F.Id("b"), F.Id("p")),
            F.Id("x"), F.Id("y")), Sp, Iff, Sp,
        Call("agrees", F.Id("b"), F.Id("x"), F.Id("y")), Close, Dot));
}
