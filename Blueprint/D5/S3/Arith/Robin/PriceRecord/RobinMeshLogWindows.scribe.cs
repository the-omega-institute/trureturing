using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class RobinMeshLogWindowsDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/RobinMeshLogWindows";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both critical Robin excursions carry positive gap weight in every late log window.",
        H("Two-sided Robin excursions in fixed logarithmic windows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-attained-canonical-critical-log-windows"),
                DeclarationHandle.Create(Gid + ".actual_attained_canonical_critical_log_windows"),
                H("Positive gap-weight shares for both signs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Analytic/crossley2026primeraceexcursions")),
                Blocks(
                    Paragraph(Text(
                        "Suppose a nontrivial zeta zero ρ attains the zero abscissa Θ with "
                        + "Re(ρ)>1/2. Let N be any strictly increasing sequence in ℕ with N(0)>0 "
                        + "and N(k+1)/N(k) tending to 1 in ℝ. Write y(k)=log(N(k)) and "
                        + "s(k)=N(k)^(1−Θ)y(k) robinLogMargin(strictInteger(firstLayerPrice(N(k)+1))). "
                        + "There exist T in ℝ and positive H, c and d such that every window "
                        + "[t,t+H) with t≥T has a nonempty block of exactly the indices a≤k<b "
                        + "with y(k) in the window. The samples s(k)>c and s(k)<−c each carry "
                        + "at least a fraction d of the block's total weight y(b)−y(a). "
                        + "Each index receives its full gap y(k+1)−y(k).")),
                    Paragraph(Text(
                        "The signed sample asymptotic and maximal-line projection give an "
                        + "absolutely summable phase series up to a null error. Real zeta "
                        + "nonvanishing makes the zero-frequency coefficient vanish. The attaining zero gives a nonzero "
                        + "twisted coefficient with its exact negative analytic multiplicity "
                        + "divided by ρ(1−ρ). The block estimates give uniform bounds for both "
                        + "moments on each late block. Absolute summability bounds the late samples, so a lower "
                        + "bound on the twisted moment and a small ordinary mean force a "
                        + "positive weight share on each side. The first mesh crossings of "
                        + "t and t+H select the block, whose span stays large as the gaps vanish.")),
                    Paragraph(Text("Crossley studies the change in the 547/727 split–inert prime-ideal race when the starting height doubles. Under primitive Dirichlet GRH, in every sufficiently late interval of log length at least 250,000, more than 10% of the log starting heights give a gain above 1.9735 log 2 and more than 10% give a loss above that magnitude."))),
                DescribeRole.Theorem))));
}
