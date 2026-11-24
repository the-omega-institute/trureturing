using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class FiniteNegativeRegressionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Probability/FiniteNegativeRegression.";
    private static readonly LibraryNoteRef SuHu = LibraryNoteRef.Create("D5/L/Dynamics/suhu2026fullnegative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full negative regression implies negative association below rectangular size 81.",
        H("Negative association below rectangular size 81"),
        Blocks(
            Entry("FullNRD", "Full negative regression", DescribeRole.Definition,
                "For disjoint response and conditioning blocks, the conditional mean of every increasing real response test "
                + "decreases between coordinatewise comparable conditioning tuples of positive mass. The comparison includes "
                + "pairs separated by zero-mass fibers."),
            Entry("NA", "Negative association", DescribeRole.Definition,
                "The covariance of every pair of increasing real tests on disjoint blocks is nonpositive."),
            Entry("marginalProduct", "Actual marginal-support product", DescribeRole.Definition,
                "Take the product of the sizes of the supports of the one-coordinate marginal probability mass functions."),
            Entry("fullNRD_of_upper", "Upper events suffice for full negative regression", DescribeRole.Theorem,
                "UpperNRD denotes the full negative regression condition with the response test restricted to upper-set indicators. A finite increasing test can be built from a constant and nonnegative multiples of its upper-level indicators. "
                + "The two positive-fiber conditional laws give the same expectation to constants."),
            Entry("na_of_fullNRD_of_marginalProduct_lt_81", "The lower bound for arbitrary finite products", DescribeRole.Theorem,
                "Restrict to the coordinate supports and omit singleton factors in each observed block. For disjoint blocks, "
                + "the product of their sizes is below 81, so at least one has size at most eight. The nonconstant possibilities "
                + "are a chain, a binary factor times a chain, and three binary factors. Conditional means under the actual "
                + "marginal retain all subblock comparisons by the finite tower identity. The binary-by-chain proof compares "
                + "the upper row tail and the corresponding marginal tail. The cube case uses the upper-event sign on "
                + "the three-bit cube. Decomposing increasing real tests into upper-level indicators gives the covariance sign."))));

    private static DocumentBlock Entry(string name, string heading, DescribeRole role, string narrative) =>
        Describe.Lean(DescribeId.Create("finite-negative-regression-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading),
            role == DescribeRole.Definition ? StatementSource.WithoutFormula() :
                StatementSource.FromAuthor(Disp(name == "fullNRD_of_upper"
                    ? Seq(Forall, Sp, F.Id("p"), Comma, Sp, Apply("UpperNRD"), Sp, Rightarrow, Sp, Apply("FullNRD"))
                    : Seq(Forall, Sp, F.Id("p"), Comma, Sp, Apply("FullNRD"), Sp, Land, Sp,
                        Apply("marginalProduct"), Sp, Lt, Sp, D(8, 1), Sp, Rightarrow, Sp, Apply("NA")))),
            AssessedProvenance.FromRepo(SuHu), Blocks(Paragraph(Text(narrative))), role);
    private static Formula Apply(string name) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, F.Id("p"), Close);
}
