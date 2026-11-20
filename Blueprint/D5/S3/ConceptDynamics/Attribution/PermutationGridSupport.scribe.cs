using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class PermutationGridSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/PermutationGridSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact seed budgets on finite probability grids under all label permutations.",
        H("Permutation-equivariant calibration on a finite grid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("permutation-grid-calibrating-law"),
                DeclarationHandle.Create(Prefix + "CalibratingLaw"),
                H("Calibrating law with permutation symmetry"),
                StatementSource.FromAuthor(Disp(Call("CalibratingLaw",
                    F.Id("k"), F.Id("m"), F.Id("S"), F.Id("w"), F.Id("f")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The labels are the first k natural numbers and the profiles are natural coordinate "
                    + "vectors with sum m. A finite seed set S carries an action of the full permutation "
                    + "group on the labels. Its real weights w are positive, sum to one and are invariant "
                    + "under this action. The mass of the seeds that f sends to a label equals that "
                    + "profile coordinate divided by m. Relabeling the profile and acting by the same "
                    + "permutation on the seed relabels the output of f."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("permutation-grid-support-budget"),
                DeclarationHandle.Create(Prefix + "grid_support_budget_iff"),
                H("Sharp support budget for the complete probability grid"),
                StatementSource.FromAuthor(BudgetStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k be at least two, let q be a positive natural number and set m to k times "
                        + "k minus one times q, with parentheses around k minus one. Suppose every "
                        + "positive integer through k divides m. SeedBudget(k,m,B) means there is a "
                        + "calibrating law with at most B seeds. For any natural n the budget k factorial "
                        + "times n is feasible exactly when k times q plus one is at most k plus one "
                        + "to the power n, with parentheses around the base.")),
                    Paragraph(Text(
                        "At denominator zero the all-zero profile requires total mass zero across all labels. "
                        + "The seed law has total mass one. The bounds on k and q guarantee a positive "
                        + "denominator. For the lower bound, the full divisibility premise guarantees "
                        + "the integer profile supported on the moved labels of each permutation.")),
                    Paragraph(Text(
                        "For any nonidentity permutation, the profile constant on its moved labels and "
                        + "zero elsewhere has integer coordinates. A fixed seed would return a fixed label "
                        + "at that profile, which has zero mass. Each seed orbit is therefore regular. "
                        + "At a profile tying k minus one labels, the subgroup fixing the distinguished label "
                        + "divides each regular orbit into k blocks. For a tied label the number of seeds "
                        + "selected in each block is either zero or the factorial of k minus two. The "
                        + "possible per-orbit block counts are the k plus one digits from zero through k.")),
                    Paragraph(Text(
                        "For attainment, group the labels by their coordinate values. Let H be the product "
                        + "of the group-size factorials and let D be the factorial of k minus two. "
                        + "Each regular seed orbit has k factorial divided by H blocks for the profile "
                        + "stabilizer action. The desired block mass for a group of size s and coordinate "
                        + "value v is D times s times v divided by H. The frozen factorial divisibility "
                        + "theorem gives integer demands. If there are t groups, each orbit has at least "
                        + "k times t minus one blocks, with parentheses around t minus one.")),
                    Paragraph(Text(
                        "Use clipped powers of k plus one, summing to q, as common orbit weights. The "
                        + "rounded capacities of each group suffice to assign all new blocks while the "
                        + "earlier orbits realize the remainder. The bounded-digit weights use Rødseth, "
                        + "Minimal r-Complete Partitions, Journal of Integer Sequences 10 (2007), "
                        + "Article 07.8.3, Lemmas 3.1–3.2. The allocation step follows by comparing the "
                        + "sum of the remainders with the mass needed for one more block.")),
                    Paragraph(Text(
                        "A block assigned to a group has an equivariant map to that label orbit, giving "
                        + "each of its labels H divided by s seeds. Extend the readout from one profile "
                        + "representative per orbit and normalize the weights on positive support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-orbit-spectrum"),
                DeclarationHandle.Create(Prefix + "weighted_orbit_spectrum"),
                H("Tied profiles determine a weighted digit covering"),
                StatementSource.FromAuthor(SpectrumStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k be the cardinality of the finite label type I, with k at least two. "
                        + "The full permutation group acts freely on the finite seed type S. Its real "
                        + "weights are invariant, and the readout is equivariant and calibrated in "
                        + "denominator units on every natural profile of total m.")),
                    Paragraph(Text(
                        "There are r regular orbits. Multiply each representative's weight by "
                        + "the factorial of k minus two to get its digit weight. The seed cardinality "
                        + "is k factorial times r. Multiplying the sum of the digit weights by "
                        + "k factorial gives the sum of seed weights times the factorial of k minus two. "
                        + "For every integer from zero through the floor of m divided by k minus one, "
                        + "with k minus one as the denominator, that integer is a weighted sum of "
                        + "digits from zero through k using this same family of weights."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula SpectrumStatement()
    {
        Formula i = F.Id("I");
        Formula s = F.Id("S");
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula w = F.Id("w");
        Formula f = F.Id("f");
        return Disp(Seq(Forall, Sp, i, Sp, s, Sp, m, Sp, w, Sp, f, Comma, Sp,
            D(2), Sp, Le, Sp, Call("Card", i), Sp, Land, Sp, Call("FreeAction", i, s),
            Sp, Land, Sp, Call("Invariant", w), Sp, Land, Sp, Call("Calibrated", m, w, f),
            Sp, Land, Sp, Call("Equivariant", f), Sp, Rightarrow, Sp,
            Call("OrbitDigitSpectrum", Call("Card", i), s, m, w)));
    }

    private static Formula BudgetStatement()
    {
        Formula k = F.Id("k");
        Formula q = F.Id("q");
        Formula n = F.Id("n");
        Formula denominator = Seq(k, Cdot, Open, k, Minus, D(1), Close, Cdot, Sp, q);
        Formula budget = Seq(Call("factorial", k), Cdot, Sp, n);
        return Disp(Seq(Forall, Sp, k, Sp, q, Sp, n, Comma, Sp,
            D(2), Sp, Le, Sp, k, Sp, Land, Sp, D(0), Sp, Lt, Sp, q, Sp, Land, Sp,
            Call("DivisibleThrough", k, denominator), Sp, Rightarrow, Sp,
            Open, Call("SeedBudget", k, denominator, budget), Sp, Iff, Sp,
            k, Cdot, Sp, q, Plus, D(1), Sp, Le, Sp, Open, k, Plus, D(1), Close, Caret, n, Close));
    }
}
