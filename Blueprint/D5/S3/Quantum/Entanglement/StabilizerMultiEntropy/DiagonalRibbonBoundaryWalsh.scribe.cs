using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class DiagonalRibbonBoundaryWalshDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalRibbonBoundaryWalsh.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact scalar ribbon boundary sum from five diagonal density-moment readouts.",
        H("The five physical code moments and literal ribbon boundaries"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-bouquet-bracket-walsh"),
                DeclarationHandle.Create(Owner+"actual_bouquet_bracket_walsh"),
                H("Actual ribbon boundary sum at a real Kauffman parameter"),
                StatementSource.FromAuthor(BracketStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For an oriented one-vertex ribbon the interlacing table is given by the standard alternating pairing on two binary coordinates per chord. Fix genuine retained-band switches and give two arbitrary real smoothing weights per edge. The five encoders retain no coordinate, one of the three line quotients, or both coordinates. Each readout is the trace moment of a normalized complex diagonal density on the selected sites.")),
                    Paragraph(Text("Write d for the negative sum of the square and inverse square of the positive real Kauffman parameter, and q for d squared. In these conventions q is at least four. The five coefficients are minus two, q, q, q, and minus two q, all divided by q minus two. The signed combination cancels the label dimensions not seen by the restricted pairing. Weighted Walsh inversion then recovers the literal boundary-circle state sum; no local smoothing weight is inverted.")),
                    Paragraph(Text("This theorem derives each boundary count from its actual retained-dart permutation. The result is the unnormalized scalar state sum, not the writhe-normalized Jones invariant or a classification of knots or links. A valid two-coordinate pairing table is required, and arbitrary multi-vertex ribbons are not yet covered."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-full-pair-readout"),
                DeclarationHandle.Create(Owner+"physical_full_pair_readout"),
                H("Exact full-pair physical readout"),
                StatementSource.FromAuthor(ReadoutStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the two standard binary coordinate vectors, with the three distinct line projections, full label and zero label. These five actual readouts mix to the reciprocal entropy base whenever the order is positive and that base differs from two."))),
                DescribeRole.Theorem))));
    private static Formula All(string n,Formula t,Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,b);
    private static Formula BracketStatement()
    {
        var r=F.Id("R"); var l=F.Id("ell"); var w=F.Id("weights"); var a=F.Id("A");
        return Disp(All("R",Call("ValidOrientedRibbonBouquets"),All("ell",Call("BinaryPairingTables",r),
            All("weights",Call("RealSmoothingWeights",r),All("A",Call("PositiveReals"),
                Equal(Call("ScaledFiveCodeWalsh",r,l,w,a),Call("LiteralBoundaryStateSum",r,w,a)))))));
    }
    private static Formula ReadoutStatement()
    {
        var k=F.Id("K");
        return Disp(All("K",Call("PositiveOrdersWithBaseNotTwo"),
            Equal(Call("PhysicalFullPairReadout",k),Call("Inverse",Call("Pow",Num(2),Call("Sub",k,Num(1)))))));
    }
}
