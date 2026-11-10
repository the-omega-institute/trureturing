using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

// UNCOMPILED source proposal. No emission, registration, or kernel claim.
internal sealed class FirstPrimePrefixLocalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Robin/PriceRecord/FirstPrimePrefixLocalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every fixed logarithmic scale localizes the first prime prefix at bounded actual defect.",
        H("First prime prefix and the same actual pressure"),
        Blocks(
            Paragraph(Text(
                "This source proposal is uncompiled. It concerns the canonical objective "
                + "goldenResourceObjective(referencePrice(z),n), where referencePrice(z)=1/(z log z). "
                + "The canonical actualPressure is the supremum over ALL positive integers, "
                + "and actualDefect is that SAME pressure minus the SAME integer's objective. "
                + "The existing public sigma identity identifies this with log(sigma(n)/n)-log(n)/(z log z). "
                + "No new pressure, objective, mass, or global mask is introduced.")),
            Describe.Lean(
                DescribeId.Create("actual-first-layer-finite-charge"),
                DeclarationHandle.Create(Prefix + "actual_first_layer_charge"),
                H("Finite missing and occupied first layers pay the actual defect"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every z>1, n>=1, disjoint finite prime sets H and X, and rho>=0, "
                    + "assume vp(n)=0 and marginal(p,1)-referencePrice(z)>=rho on H, and "
                    + "vp(n)>=1 and referencePrice(z)-marginal(p,1)>=rho on X. Then "
                    + "rho*(sum_H log(p)+sum_X log(p))<=actualDefect(z,n). "
                    + "The native StageA owner extraction actual_local_gap_sum_le_defect is used once on H union X. "
                    + "Missing primes pay the local increment from 0 to 1. At an occupied prime with "
                    + "negative first marginal, all later local increments are nonpositive. "
                    + "The original owner's now-public count_maximal is directly consumed; its proof is not copied. "
                    + "No exponent cap, reference reserve, or selected optimizer premise is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-prefix-finite-displacement-charge"),
                DeclarationHandle.Create(Prefix + "first_prefix_displacement_charge"),
                H("The concrete eta squared charge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<eta<=1/4 and eta*z>=4, the below band is "
                    + "(z*(1-3eta/4),z*(1-eta/2)] and the above band is "
                    + "(z*(1+eta/2),z*(1+3eta/4)]. Assume each literal theta mass is at least eta*z/8. "
                    + "If the original n>=1 has EXACT support primesLE(P), P=largestPrime(n), and "
                    + "P<=z*(1-eta) or P>=z*(1+eta), then "
                    + "sqrt(z)*log(z)*actualDefect(z,n)>=eta^2*sqrt(z)/32. "
                    + "The lower first marginal bound is 1/((p+1)log p); the upper is 1/(p log p). "
                    + "They give a margin eta/(4*z*log z) on the respective finite bands. "
                    + "The bands' actual prime sums equal the two theta differences exactly. "
                    + "Initial support makes the entire lower band absent or the entire upper band occupied."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("global-theta-first-prefix-log-windows"),
                DeclarationHandle.Create(Prefix + "eventually_first_prefix_windows"),
                H("Global PNT supplies every fixed logarithmic window"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every fixed A in Nat and fixed 0<e<=1/4, put eta=e/log(z)^A. "
                    + "One eventual threshold simultaneously gives log z>=1, 0<eta<=1/4, eta*z>=4, "
                    + "and BOTH finite theta masses >=eta*z/8. The PUBLIC theta_error_log_power(A+1) "
                    + "gives a global bound |theta(y)-y|<=y/log(y)^(A+1) for all sufficiently large y. "
                    + "Uniformly on z/2<=y<=2z, log y>=log z/2 and the error is at most "
                    + "2^(A+2)*z/log(z)^(A+1). Taking log z>=16*2^(A+2)/e makes each endpoint "
                    + "error <=eta*z/16. Each band has width eta*z/4. No assumed short-interval PNT "
                    + "or dependence of the threshold on the chosen n occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-actual-defect-all-log-prefix-localization"),
                DeclarationHandle.Create(Prefix + "bounded_defect_first_prefix_localization"),
                H("All positive prime-prefix integers, one uniform threshold"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every A in Nat, K>=0 and epsilon>0, there exists Z>=2 BEFORE all real z>=Z "
                    + "and all n>=1. Assume n.primeFactors=primesLE(largestPrime(n)) and "
                    + "sqrt(z)*log(z)*actualDefect(z,n)<=K. Then "
                    + "abs(log(z)^A*(largestPrime(n)/z-1))<epsilon. "
                    + "The proof clips ONLY the fixed numerator e=min(epsilon,1/4); eta=e/log(z)^A. "
                    + "A violation forces the finite displacement charge, which diverges because "
                    + "log(z)^(2A)/sqrt(z)->0. This includes A=0 and the unit n=1: no extra n>=2 "
                    + "or P lower bound removes the unit; its missing band rules it out under bounded defect. "
                    + "There is no record assumption, bounded support hypothesis, or bounded exponent premise. "
                    + "The proof gives fixed logarithmic scales, not a power localization rate."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The StageA proof and its original quantitative second-layer theorem remain at their owner. "
                + "Only one finite-support decomposition is extracted there and consumed by both layers. "
                + "All Lean elaboration, axiom closure, Scribe validation, native checks and publication remain "
                + "future root integration. No RH, Robin sign, sharpness, novelty or CI acceptance is asserted."))
        )));
}
