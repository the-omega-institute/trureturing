using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arithmetic.HigherOrderFourier;

internal sealed class FiniteGowersCubeMomentDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arithmetic/HigherOrderFourier/FiniteGowersCubeMoment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Iterated multiplicative derivatives define manifestly nonnegative finite Gowers correlation energies.",
        H("Finite Gowers Cube Moment"),
        Blocks(
            Def("derivative", "multiplicativeDerivative", "Multiplicative derivative",
                "One additive direction compares a shifted value with the conjugate of the original value."),
            Def("iterated", "iteratedDerivative", "Iterated multiplicative derivative",
                "A direction list applies multiplicative derivatives in order."),
            Def("correlation", "iteratedCorrelation", "Iterated derivative correlation",
                "The values of an iterated derivative are summed over the finite additive group."),
            Def("energy", "finiteGowersDerivativeEnergy", "Finite derivative energy",
                "Squared norms of all depth-indexed correlations are summed over the finite direction cube."),
            Def("u2", "finiteGowersU2Energy", "Finite U2 energy",
                "Depth-one derivative correlations define the unnormalized fourth-power U2 energy."),
            Thm("append", "iteratedDerivative_append", "Direction append composition",
                "Appending direction lists applies the earlier derivative block before the later block."),
            Thm("product", "multiplicativeDerivative_mul", "Derivative product law",
                "Multiplicative differentiation distributes over pointwise products."),
            Thm("nonnegative", "finiteGowersDerivativeEnergy_nonneg", "Derivative energy is nonnegative",
                "Every finite correlation contributes a squared complex norm."),
            Thm("u2-zero", "finiteGowersU2Energy_eq_zero_iff", "Zero U2 energy is zero correlation",
                "The U2 energy vanishes exactly when every directional correlation vanishes."),
            Thm("depth-one", "finiteGowersDerivativeEnergy_one", "Depth one equals U2",
                "The general derivative energy at depth one is exactly the finite U2 energy.")),
        []));

    private static DocumentBlock.Describe Def(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
