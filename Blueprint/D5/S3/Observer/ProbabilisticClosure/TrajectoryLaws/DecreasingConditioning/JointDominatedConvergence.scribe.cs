using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.DecreasingConditioning;

internal sealed class JointDominatedConvergenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/blackwelldubins1962merging");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dominated varying inputs have joint AE and L1 conditional limits at a decreasing raw infimum.",
        H("Joint conditional dominated convergence for decreasing information"), Blocks(
            Paragraph(Text("Let Ω belong to any universe, let A be an arbitrary ambient sigma-algebra on Ω, and let μ be a probability measure on A. Let F be a natural-indexed antitone family of sigma-algebras with Fⱼ contained in A for every natural j. Put M = infimum over j of Fⱼ, the raw infimum in MeasurableSpace Ω. Write Cⱼf = Eμ[f | Fⱼ] and C∞f = Eμ[f | M]. Every conditional expectation is the actual receiving measurable version under the same μ.")),
            Describe.Lean(DescribeId.Create("decreasing-joint-conditional-dominated-convergence"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/JointDominatedConvergence.tendsto_condExp_of_dominated_convergence"),
                H("Both limits with two independent tail indices"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("For every universe, probability space and antitone family as above, every sequence of ambient-measurable real functions yₙ, every ambient-measurable real function yLim, and every μ-integrable real function g, assume that yₙ tends to yLim μ-almost everywhere and, for every natural n, |yₙ| ≤ g μ-almost everywhere. Then both conclusions hold: the actual Cⱼyₙ converge μ-almost everywhere to the actual C∞yLim as (n,j) tends to infinity in the product order, and the real integrals ∫ |Cⱼyₙ − C∞yLim| dμ tend to zero in that same product order.")),
                    Paragraph(Text("The first conclusion means there is one μ-null set Z such that for every ω outside Z and every ε > 0 there are natural N and J with |Cⱼyₙ(ω) − C∞yLim(ω)| < ε for all n ≥ N and j ≥ J. The set Z is fixed before ε, N and J. The thresholds can depend on ω and ε. The integral conclusion means that for every ε > 0 there are natural N and J with ∫ |Cⱼyₙ − C∞yLim| dμ < ε for all n ≥ N and j ≥ J; these thresholds depend on ε. Thus the assertion controls entire rectangles and permits independent relative speeds of the two indices.")),
                    Paragraph(Text("In the displayed typed formula, Universe and Type(u) express arbitrary universe level and carrier; Measure(Ω,A) means a measure on the specified ambient sigma-algebra. Measurable(A,f) means ambient measurability with the real Borel codomain. AE(μ,p) means that p holds μ-almost everywhere, CE(μ,f,B) is the actual conditional-expectation function Eμ[f | B], iInf(F) is the raw infimum over all natural indices, apply denotes function evaluation, and integral(μ,f) is the real Bochner integral. atTop in the two conclusions is the filter on Nat × Nat with the product order; in the input convergence premise it is the natural atTop filter.")),
                    Paragraph(Text("Intersect the countably many original domination sets with the original input-convergence set. On this common set, the limit satisfies |yLim| ≤ g. Define bᴺ(ω) = sup over natural k of |y_(N+k)(ω) − yLim(ω)|. Countability gives ambient measurability of each tail. The original real_tail_control declaration in JointConditionalDominatedConvergence supplies, on this set, nonnegativity, the bound bᴺ ≤ 2|g|, antitonicity in N, domination of every later input error, and bᴺ → 0. Its order statements apply under the established boundedness of the supremum; no order bound on the exceptional set is asserted.")),
                    Paragraph(Text("The integrable envelope 2|g| makes every bᴺ integrable, and dominated convergence gives ∫ bᴺ dμ → 0. Define qᴺ = C∞bᴺ at the raw M. Conditional positivity and order give qᴺ ≥ 0 and antitonicity almost everywhere. Preservation of integrals gives ∫ qᴺ dμ → 0. The pinned theorem tendsto_of_integral_tendsto_of_antitone, applied with integrable lower bound zero, yields qᴺ → 0 almost everywhere.")),
                    Paragraph(Text("Apply MeasureTheory.tendsto_ae_and_eLpNorm_condExp_iInf to yLim and to every bᴺ. It gives CⱼyLim → C∞yLim almost everywhere and Cⱼbᴺ → qᴺ almost everywhere for every N. Conditional subtraction, the conditional absolute-value inequality and conditional monotonicity give |Cⱼyₙ − CⱼyLim| ≤ Cⱼbᴺ whenever n ≥ N. Aggregate the fixed-input limits and all countable N,n,j inequalities into one common full-measure set before introducing ε. At any point in this set, choose N with |qᴺ| < ε/3, then choose J so both |Cⱼbᴺ − qᴺ| and |CⱼyLim − C∞yLim| are below ε/3 whenever j ≥ J. The triangle inequality controls all n ≥ N and j ≥ J at once.")),
                    Paragraph(Text("For the integral conclusion, the same fixed-input downward theorem gives exponent-one eLpNorm convergence for yLim. ENNReal.toReal continuity at zero, the exponent-one lintegral identity and the integral-of-norm identity turn this into ∫ |CⱼyLim − C∞yLim| dμ → 0. Conditional L1 contraction and the integral triangle inequality give ∫ |Cⱼyₙ − C∞yLim| dμ ≤ ∫ bⁿ dμ + ∫ |CⱼyLim − C∞yLim| dμ. The first coordinate limit, second coordinate limit and nonnegative squeeze prove the product-atTop integral limit.")),
                    Paragraph(Text("Raw-infimum provenance comes from the imported LevyDownward theorem, whose construction identifies its fixed-input limit with the actual conditional expectation at the uncompleted infimum of the Fⱼ. The proof here uses this endpoint directly; it does not assume downward convergence as a premise or replace M by an intersection of completed sigma-algebras. The source-preserving downward construction and its immutable upstream locators are recorded in "), Ref("D5/L/Observer/tauceti2026levydownward"), Text(".")),
                    Paragraph(Text("The result covers arbitrary probability spaces, unbounded integrable envelopes, constant and nontrivial decreasing families, all natural indices including zero, and null-set modifications of the inputs. No adaptedness, limit-field measurability, countable generation, standard-Borel structure, finite-state restriction, eventual constancy, convergence rate, Markov property or stationarity is assumed. It states the full varying-input Hunt limit and its L1 conjunction, with no future-opinion merging assertion.")),
                    Paragraph(Text("The mathematical theorem is the decreasing-field part of Blackwell and Dubins, Merging of Opinions with Increasing Information, Theorem 2, page 883, equation (2). Their integrability assumption on supₙ |yₙ| follows here from the common integrable envelope, since that countable supremum is at most |g| almost everywhere. The receiving formalization composes the original tail control, pinned analytic APIs and the imported fixed-input downward endpoint to obtain the varying-input rectangle and integral limits. This is a formalization of a known mathematical theorem; literature originality is not asserted."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula u = F.Id("u"), omegaType = F.Id("Omega"), ambient = F.Id("A"), mu = F.Id("mu");
        Formula fields = F.Id("F"), y = F.Id("y"), limit = F.Id("yLim"), g = F.Id("g");
        Formula n = F.Id("n"), j = F.Id("j"), k = F.Id("k"), omega = F.Id("omega");
        Formula nat = F.Id("Nat"), real = F.Id("Real"), pair = Call("Prod", nat, nat);
        Formula target = Call("apply", Call("CE", mu, limit, Call("iInf", fields)), omega);
        Formula current = Call("apply", Call("CE", mu,
            Call("apply", y, Call("fst", k)), Call("apply", fields, Call("snd", k))), omega);
        Formula aeLimit = Call("AE", mu, Lam("omega", omegaType,
            Call("Tendsto", Lam("k", pair, current), F.Id("atTop"), Call("nhds", target))));
        Formula lOneLimit = Call("Tendsto", Lam("k", pair,
            Call("integral", mu, Lam("omega", omegaType, Call("abs", Subtract(current, target))))),
            F.Id("atTop"), Call("nhds", D(0)));
        Formula statement = And(aeLimit, lOneLimit);
        statement = Imp(All("n", nat, Call("AE", mu, Lam("omega", omegaType,
            Rel(Call("abs", Call("apply", y, n, omega)), Le, Call("apply", g, omega))))), statement);
        statement = Imp(Call("Integrable", g, mu), statement);
        statement = Imp(Call("AE", mu, Lam("omega", omegaType,
            Call("Tendsto", Lam("n", nat, Call("apply", y, n, omega)),
                F.Id("atTop"), Call("nhds", Call("apply", limit, omega))))), statement);
        statement = Imp(Call("Measurable", ambient, limit), statement);
        statement = Imp(All("n", nat, Call("Measurable", ambient, Call("apply", y, n))), statement);
        statement = All("g", Arrow(omegaType, real), statement);
        statement = All("yLim", Arrow(omegaType, real), statement);
        statement = All("y", Arrow(nat, Arrow(omegaType, real)), statement);
        statement = Imp(All("j", nat, Rel(Call("apply", fields, j), Le, ambient)), statement);
        statement = Imp(Call("Antitone", fields), statement);
        statement = All("F", Arrow(nat, Call("MeasurableSpace", omegaType)), statement);
        statement = F.Seq(OpenBracket, Call("IsProbabilityMeasure", mu), CloseBracket, Sp, statement);
        statement = All("mu", Call("Measure", omegaType, ambient), statement);
        statement = All("A", Call("MeasurableSpace", omegaType), statement);
        statement = All("Omega", Call("Type", u), statement);
        return All("u", F.Id("Universe"), statement);
    }

    private static Formula Par(Formula body) => F.Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        F.Seq(Forall, Sp, F.Id(name), Colon, Sp, Par(type), Comma, Sp, Par(body));
    private static Formula Lam(string name, Formula type, Formula body) =>
        F.Seq(Open, F.Id(name), Colon, Sp, Par(type), Mapsto, Sp, body, Close);
    private static Formula Arrow(Formula source, Formula target) => F.Seq(Par(source), To, Sp, Par(target));
    private static Formula Imp(Formula premise, Formula conclusion) =>
        F.Seq(Par(premise), Implies, Sp, Par(conclusion));
    private static Formula And(Formula left, Formula right) => F.Seq(Par(left), Land, Sp, Par(right));
    private static Formula Rel(Formula left, Formula relation, Formula right) => F.Seq(left, relation, Sp, right);
    private static Formula Call(string name, params Formula[] args)
    {
        Formula result = F.Seq(Operatorname, Grp(F.Id(name)), Open);
        for (int i = 0; i < args.Length; i++)
            result = i == 0 ? F.Seq(result, args[i]) : F.Seq(result, Comma, Sp, args[i]);
        return F.Seq(result, Close);
    }
}
