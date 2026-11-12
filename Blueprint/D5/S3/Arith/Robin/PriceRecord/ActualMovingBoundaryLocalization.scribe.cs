using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualMovingBoundaryLocalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite displaced-root actual boundary localization.",
        H("One-sided exchanges at the original full record"),
        Blocks(
            Paragraph(Text("FullRecord ranges over every positive integer below the same original m, at its arbitrary original positive mu. The comparison price is literally beta(1,largestPrime(m)). No recordhood at that price, own clock, global optimizer, nonnegative epsilon or unsigned fee is assumed.")),
            Paragraph(Text("These finite conditional results isolate the actual moving-boundary squeeze. A uniform eventual construction over j<=delta*log(P)/(log(log(P)))^2+1 remains unproved. The maximum-gap premise is separate from the universal real-center count law and is not used in the finite proof. No Robin, 5040 or RH conclusion is asserted. Typed Reg actual laws, exact source bridges and observational dependence are partial audit evidence; lawful source-bound four-slot registration remains unfinished under issue 29429.")),
            Describe.Lean(
                DescribeId.Create("actual-moving-displaced-root-boundary-squeeze"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.displaced_root_boundary_squeeze"),
                H("displaced_root_boundary_squeeze"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two strict one-sided exchanges constrain the boundary without assuming exact probe valuations. Above Q_j the insertion marginal dominates beta_j; below Q_j the deletion marginal is dominated by beta_j. Strict greedy subsets preserve exact mass ties and the original signed term -mu*(positive mass gap). The integrated lower logarithmic slope excludes the two probe pools separately."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-moving-counted-displaced-root-boundary-squeeze"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.counted_displaced_root_boundary_squeeze"),
                H("counted_displaced_root_boundary_squeeze"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The universal real-center short-interval count law is applied at P, rm and rp. The first upper closed interval is erased at its natural endpoint P; the two probe intervals stay closed. Equal finite cardinalities and logarithmic endpoints supply the mass comparisons and disjointness. The first-layer Lipschitz bound is used only at index 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-moving-counted-displaced-cutoff-log-localization"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualMovingBoundaryLocalization.counted_displaced_cutoff_log_localization"),
                H("counted_displaced_cutoff_log_localization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The root is the active cutoff at literal beta(1,P). At rm=rho*exp(-H*t) and rp=rho*exp(H*t), t=P^(-priceExponent j), the finite scalar conditions yield positive actual layerPrime and logarithmic error at most (H+16*C)*t. The constant contains no j. The finite count capacities, root activation, root geometry and smallness inequalities are explicit premises; this theorem does not establish one eventual threshold for growing j."))),
                DescribeRole.Theorem)
        )));
}
