using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class CoinfiniteExhaustionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Divergence/CoinfiniteExhaustion.";
    private static readonly LibraryNoteRef Yang = LibraryNoteRef.Create("D5/L/Divergence/yang2026quantumdataprocessing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible nested finite restrictions of one faithful diagonal bit-erasure model have different entropy-loss limits.",
        H("Exhaustion dependence for bit erasure"),
        Blocks(
            Paragraph(Text("The physical first coordinate is k = i + 1 for i a natural number. Its two fixed laws have masses p(k) = 1/(k(k+1)) and q(k) = 2⁻ᵏ. Both use the same independent fair bit. A cutoff m keeps the first m singletons and merges the remaining coordinates into an atom with respective masses 1/(m+1) and 2⁻ᵐ.")),
            Entry("fixed_source_states", "Fixed faithful countable laws",
                "Both source laws on the product with the bit are strictly positive and sum to one."),
            Entry("fine_states_are_restrictions", "Restriction of the fixed laws",
                "Summing each source law over the fiber of the finite cutoff, with the bit retained, gives its corresponding fine input mass."),
            Entry("finite_states", "Faithful finite laws",
                "At each cutoff the two marginal laws and their two fair-bit lifts are strictly positive and have sum one."),
            Entry("partitionMap_cutIndex", "Compatibility of the cutoffs",
                "For n ≤ a the coarse atom of a physical coordinate equals the coarse image of its fine atom."),
            Entry("partitionMap_comp", "Nested clipping",
                "If n ≤ m, clipping a fine atom first at m and then at n gives its direct image at n."),
            Entry("eventually_resolves_atom", "Eventual resolution of each physical atom",
                "For every compatible sequence a with n ≤ a(n), every fixed first coordinate eventually lies in a singleton atom."),
            Entry("partitionChannel_stochastic", "The finite bit-erasure channel",
                "The finite stochastic matrix sends each fine atom and bit pair to its coarse atom with probability one. All entries are nonnegative and each input row sums to one."),
            Entry("partitionChannel_outputs", "The two actual channel outputs",
                "For n ≤ a the actual outputs of the fine restrictions are the respective coarse cutoff laws."),
            Entry("loss_exact", "Exact finite KL loss",
                "The common fair bit cancels by product additivity. The finite cross entropy is log(2) times the harmonic number because the expected truncated first coordinate grows by the preceding tail mass. Subtracting the fine and coarse KL values yields the displayed identity.",
                ExactLoss()),
            Entry("tendsto_cut_shannon", "Finite limit of cutoff Shannon entropy",
                "The cutoff entropies converge to the Shannon series of the countable first law. The singleton series has a summable power bound with exponent 3/2, and the entropy of the merged tail tends to zero."),
            Entry("tendsto_loss_sub_log_ratio", "Asymptotic loss along any compatible sequence",
                "For every natural cutoff sequence a with n ≤ a(n), the loss at cutoffs a(n) and n minus log(2) log(a(n)/n) tends to zero at infinity. No monotonicity of a is required for this estimate."),
            Entry("tendsto_loss_of_ratio", "Limit when the cutoff ratio converges",
                "For every compatible natural cutoff sequence a and real R, if a(n)/n converges to R, the actual losses converge to log(2) log(R). Compatibility implies R ≥ 1 and permits continuity of the natural logarithm."),
            Entry("nonunique_exhaustion_loss", "Different limits for two compatible exhaustions",
                "Taking the fine cutoff to be n or 2n produces different limits of the true finite loss for the same two source laws and bit-erasure map. The diagonal loss vanishes at each cutoff. The doubled cutoff has ratio two for all positive indices.",
                Disp(And(Limit(Sequence(false), D(0)),
                    And(Limit(Sequence(true), Mul(LogTwo, LogTwo)), LeStrict(D(0), Mul(LogTwo, LogTwo)))))),
            Entry("no_common_exhaustion_limit", "No common limit over nested exhaustions",
                "There is no real limit shared by all monotone cutoff sequences a with n ≤ a(n), coherent nested clipping, and stochastic channels. The identity and doubled sequences are both monotone and compatible, so uniqueness of limits would equate zero with the positive square of log(2). Yang's section V.3 provides the von Neumann algebra setting for this diagonal counterexample."))));

    private static DocumentBlock Entry(string name, string title, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Yang), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula ExactLoss()
    {
        var a = V("a");
        var n = V("n");
        var harmonicDifference = Sub(Call("harmonic", a), Call("harmonic", n));
        var entropyDifference = Sub(Entropy(a), Entropy(n));
        var identity = Eq(Call("loss", a, n), Sub(Mul(LogTwo, harmonicDifference), entropyDifference));
        return Disp(All("a", Naturals, All("n", Naturals, Imp(Le(n, a), identity))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula LogTwo => Call("log", D(2));
    private static Formula Entropy(Formula cutoff) => Call("shannonEntropy", Call("pCut", cutoff));
    private static Formula Limit(Formula sequence, Formula value) =>
        Call("Tendsto", sequence, V("atTop"), Call("nhds", value));
    private static Formula Sequence(bool doubled) =>
        Seq(Open, V("n"), Sp, Mapsto, Sp, Call("loss", doubled ? Mul(D(2), V("n")) : V("n"), V("n")), Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LeStrict(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
