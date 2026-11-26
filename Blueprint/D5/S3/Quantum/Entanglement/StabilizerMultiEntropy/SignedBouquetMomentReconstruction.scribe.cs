using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class SignedBouquetMomentReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recover the full scalar boundary state sum of a signed ribbon bouquet.",
        H("Recover the full scalar boundary state sum of a signed ribbon bouquet"),
        Blocks(Describe.Lean(DescribeId.Create("literal-intrinsic-signed-bouquet"),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/SignedBouquetMomentReconstruction.literal_intrinsic_signed_bouquet"),
            H("Recover the full scalar boundary state sum of a signed ribbon bouquet"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The labels are intrinsic: quotient the binary chord space by the radical of the signed pairing, and take the images of the chord basis. The retained form rank is a function of the retained column span, and the quotient-code trace moments recover its loop weight. Walsh inversion yields the weighted literal four-flag boundary state sum for any nonzero real loop value and arbitrary smoothing weights, including zero. There is no genus bound and no separately supplied label table. This is a one-vertex theorem, not the writhe-normalized Jones invariant or a multi-vertex reconstruction."))), DescribeRole.Theorem))));
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Statement()
    {
        var x = F.Id("R"); var y = F.Id("d"); var z = F.Id("w");
        return Disp(All("R",Call("ValidSignedRibbonBouquets"),All("d",Call("NonzeroReals"),All("w",Call("RealSmoothingWeights",x),Equal(Call("PhysicalQuotientMomentWalsh",x,y,z),Call("LiteralBoundaryStateSum",x,y,z))))));
    }
}
