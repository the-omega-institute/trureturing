using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class ConditionalMeanIntegrableDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Law => Call("ProbabilityMeasure", Real);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional means on equal quantile bins approximate integrable real probability laws in convex order.",
        H("Equal quantile bins for integrable real laws"),
        Blocks(
            Paragraph(Text("For a real probability law rho, Mean is its identity integral and IntegrableIdentity asserts its finite absolute first moment. StopLoss(rho,z) is the integral of max(x-z,0). Upper(rho,t) and Lower(rho,t) integrate the generalized quantile against Lebesgue measure on (t,1] and (0,t], respectively.")),
            Describe.Lean(DescribeId.Create("upperintegratedquantile-le-of-stoploss-le"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/ConditionalMeanIntegrable.upperIntegratedQuantile_le_of_stopLoss_le"),
                H("Upper integrated quantiles under stop-loss order"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Forall, Sp, V("mu"), Comma, V("nu"), Colon, Sp, Law, Comma, Sp,
                        Call("IntegrableIdentity", V("mu")), Sp, Rightarrow,
                        Call("IntegrableIdentity", V("nu")), Sp, Rightarrow),
                    Seq(Open, Forall, Sp, V("z"), Colon, Sp, Real, Comma, Sp,
                        Call("StopLoss", V("mu"), V("z")), Sp, Leq, Sp,
                        Call("StopLoss", V("nu"), V("z")), Close, Sp, Rightarrow),
                    Seq(Forall, Sp, V("t"), Sp, InMacro, Sp, Open, D(0), Comma, D(1), CloseBracket,
                        Comma, Sp, Call("Upper", V("mu"), V("t")), Sp, Leq, Sp,
                        Call("Upper", V("nu"), V("t")))
                ]))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Convexity/lyng2026compactstrassen")),
                Blocks(Paragraph(Text("Compare at the stop-loss threshold given by the right quantile. At an interior level this threshold attains the bound for the right law. At level one both upper integrals vanish."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lowerintegratedquantile-ge-of-upper-le"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/ConditionalMeanIntegrable.lowerIntegratedQuantile_ge_of_upper_le"),
                H("Lower quantile integrals from equal means"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Forall, Sp, V("mu"), Comma, V("nu"), Colon, Sp, Law, Comma, Sp,
                        Call("IntegrableIdentity", V("mu")), Sp, Rightarrow,
                        Call("IntegrableIdentity", V("nu")), Sp, Rightarrow),
                    Seq(Call("Mean", V("mu")), Sp, Eq, Sp, Call("Mean", V("nu")), Sp, Rightarrow,
                        Forall, Sp, V("t"), Sp, InMacro, Sp, Open, D(0), Comma, D(1), CloseBracket, Comma, Sp),
                    Seq(Call("Upper", V("mu"), V("t")), Sp, Leq, Sp,
                        Call("Upper", V("nu"), V("t")), Sp, Rightarrow,
                        Call("Lower", V("nu"), V("t")), Sp, Leq, Sp,
                        Call("Lower", V("mu"), V("t")))
                ]))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Convexity/lyng2026compactstrassen")),
                Blocks(Paragraph(Text("Split the integral of each quantile at the given level. The total quantile integral equals the original mean, so subtracting the upper integral gives the reverse inequality on the lower interval."))), DescribeRole.Theorem),
            Paragraph(Text("For a positive integer n, BinIntegrable(rho,n) asserts Lebesgue integrability of the quantile of rho on every bin (k/n,(k+1)/n] with k in Fin n. BinMean is n times that integral. PrefixSum sums the bin means through and including index K, and Lower integrates the same quantile over (0,t] at level t.")),
            Describe.Lean(DescribeId.Create("integrable-quantile-bin"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/ConditionalMeanIntegrable.integrableOn_quantile_bin_of_integrable"),
                H("Quantile integrability on every bin"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, V("mu"), Colon, Sp, Law, Comma, Sp,
                    Call("IntegrableIdentity", V("mu")), Sp, Rightarrow,
                    Forall, Sp, V("n"), Colon, Sp, Nat, Comma, Sp, D(0), Lt, V("n"),
                    Sp, Rightarrow, Call("BinIntegrable", V("mu"), V("n"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Convexity/lyng2026compactstrassen")),
                Blocks(Paragraph(Text("The quantile on (0,1] is integrable by the original law and its finite absolute first moment. Restrict to each quantile bin."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("condmeanatom-monotone-of-integrable-bins"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtom_monotone_of_integrable_bins"),
                H("Monotonicity of integrable quantile-bin means"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, V("mu"), Colon, Sp, Law, Comma, Sp,
                    Forall, Sp, V("n"), Colon, Sp, Nat, Comma, Sp, D(0), Lt, V("n"), Sp, Rightarrow,
                    Call("BinIntegrable", V("mu"), V("n")), Sp, Rightarrow,
                    Call("Monotone", Seq(V("k"), Mapsto, Call("BinMean", V("mu"), V("n"), V("k"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Convexity/lyng2026compactstrassen")),
                Blocks(Paragraph(Text("For two ordered bins, values of the quantile on the earlier bin are bounded above by values on the later bin almost everywhere. The bins have equal mass and their quantile integrals are finite."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("condmeanatomize-partial-sum-eq-of-integrable-bins"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtomize_partial_sum_eq_of_integrable_bins"),
                H("Prefix sums of integrable quantile-bin means"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Forall, Sp, V("mu"), Colon, Sp, Law, Comma, Sp,
                        Forall, Sp, V("n"), Colon, Sp, Nat, Comma, Sp, D(0), Lt, V("n"), Sp, Rightarrow,
                        Call("BinIntegrable", V("mu"), V("n")), Sp, Rightarrow),
                    Seq(Forall, Sp, V("K"), Colon, Sp, Call("Fin", V("n")), Comma, Sp,
                        Call("PrefixSum", V("mu"), V("n"), V("K")), Sp, Eq, Sp,
                        V("n"), Sp, Cdot, Sp,
                        Call("Lower", V("mu"), Seq(Open, V("K"), Plus, D(1), Close, Slash, V("n"))))
                ]))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Convexity/lyng2026compactstrassen")),
                Blocks(Paragraph(Text("The first K+1 right-closed bins form a disjoint union up to their final endpoint. Finite additivity of the integral sums their means, with the same scaling factor n on every bin."))), DescribeRole.Theorem),
            Paragraph(Text("BinLaw is the uniform finite law of the bin means. WeakLimit uses its embedding into probability measures. ConvexOrder compares the expectations of every convex real test for the two finite laws.")),
            Describe.Lean(DescribeId.Create("condmeanatomize-tendsto-of-integrable-bins"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtomize_tendsto_of_integrable_bins"),
                H("Weak convergence of integrable bin-mean laws"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Forall, Sp, V("mu"), Colon, Sp, Law, Comma, Sp,
                        Open, Forall, Sp, V("n"), Colon, Sp, Nat, Comma, Sp, D(0), Lt, V("n"),
                        Sp, Rightarrow, Call("BinIntegrable", V("mu"), V("n")), Close, Sp, Rightarrow),
                    Seq(Call("WeakLimit", Seq(V("n"), Sp, Mapsto, Sp,
                        Call("BinLaw", V("mu"), Seq(V("n"), Plus, D(1)))), V("mu")))
                ]))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Convexity/lyng2026compactstrassen")),
                Blocks(Paragraph(Text("At an interior continuity point of the quantile, the bin containing the point shrinks to it. The bin means converge there, and the exceptional set has measure zero. Bounded continuous tests give dominated convergence for the probability laws."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("condmeanatomize-convexorder-of-lowerintegratedquantile"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/ConditionalMeanIntegrable.condMeanAtomize_convexOrder_of_lowerIntegratedQuantile"),
                H("Convex order of the equiweighted bin-mean laws"), StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Forall, Sp, V("mu"), Comma, V("nu"), Colon, Sp, Law, Comma, Sp,
                        Call("IntegrableIdentity", V("mu")), Sp, Rightarrow,
                        Call("IntegrableIdentity", V("nu")), Sp, Rightarrow),
                    Seq(Call("Mean", V("mu")), Sp, Eq, Sp, Call("Mean", V("nu")), Sp, Rightarrow,
                        Forall, Sp, V("n"), Colon, Sp, Nat, Comma, Sp, D(0), Lt, V("n"), Sp, Rightarrow),
                    Seq(Open, Forall, Sp, V("t"), Sp, InMacro, Sp,
                        Open, D(0), Comma, D(1), CloseBracket, Comma, Sp,
                        Call("Lower", V("nu"), V("t")), Sp, Leq, Sp,
                        Call("Lower", V("mu"), V("t")), Close, Sp, Rightarrow),
                    Seq(Call("ConvexOrder", Call("BinLaw", V("mu"), V("n")),
                        Call("BinLaw", V("nu"), V("n"))))
                ]))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Convexity/lyng2026compactstrassen")),
                Blocks(Paragraph(Text("Both vectors of bin means are increasing and have equal total sums. The lower quantile integrals order their prefix sums at each bin endpoint. Finite majorization compares the expectations of every convex test."))), DescribeRole.Theorem))));
}
