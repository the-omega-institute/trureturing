using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualFiveModeStencilDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual dyadic root stencil.",
        H("Actual dyadic root stencil"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualfivemodestencil-uniform-boundary-root-log-transfer"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.uniform_boundary_root_log_transfer"),
                H("Transfer to the actual clamped root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under both independent BHP suppliers and for each fixed j>=2, positive A,T precede every full record and original mu>0. The difference between j*log(layerPrime(m,j)) and log(P)+actualOffset(j,P) is at most A*P^(-19/(40*j)). The actual clamped cutoff and the occupied boundary remain distinct objects."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualfivemodestencil-actual-stencil-limits"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.actual_stencil_limits"),
                H("Four dyadic mesh limits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At infinity the four actual dyadic mesh limits are respectively log(2), log(2)^2, 2*log(2)^3 and 6*log(2)^4 after multiplication by log(X), log(X)^2, log(X)^3 and log(X)^4. The first expression is log(X)*(log(2)-mesh1(X)); the remaining expressions use mesh2, mesh3 and mesh4 directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualfivemodestencil-actual-root-greedy-stencil"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil.actual_root_greedy_stencil"),
                H("One signed vector on the actual roots"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There are positive B,T such that every real X>=T admits an integer vector on Fin 5 with sum zero and every coefficient at most B*log(X) in absolute value. The positive fourth mesh is at most B/log(X)^4; the deficit log(2)-sum(v(k)*rootMasses(X,k)) lies in [2*mesh4(X),3*mesh4(X)). These are simultaneous bounds for the same vector."))),
                DescribeRole.Theorem))));
}
