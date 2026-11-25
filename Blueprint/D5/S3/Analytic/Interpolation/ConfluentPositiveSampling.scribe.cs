using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class ConfluentPositiveSamplingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Interpolation/ConfluentPositiveSampling";
    private const string Digest =
        "Confluent Newton samples recover weighted polynomial coefficients on positive intervals.";
    private const string DeBoor = "D5/L/Estimation/deboor2005divideddifferences";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, Digest, "analytic-sampling-bound-without-executable-mirror"),
        H("Confluent positive polynomial sampling"),
        Blocks(
            Paragraph(Text("A fixed positive interval gives uniform recovery from a tail of Newton "
                + "coefficients, including when all sample nodes coincide.")),
            Describe.Lean(
                DescribeId.Create("confluent-weighted-newton-tail"),
                DeclarationHandle.Create(Module + ".weightedNewtonTail"),
                H("The weighted Newton tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(DeBoor)),
                Blocks(
                    Paragraph(Text("Let a_0, ..., a_m be the nodes in their supplied order and "
                        + "v_0, ..., v_(m-1) the coefficients. Start with "
                        + "p_0 = X^r * sum_(k<m) v_k X^k. For j < m, let p_(j+1) be the "
                        + "quotient of p_j by the monic factor X - a_j. The output coordinate "
                        + "j - 1 is p_j(a_j) for 1 <= j <= m. The order-zero value p_0(a_0) "
                        + "is omitted.")),
                    Paragraph(Text("For distinct nodes, p_j(a_j) is the divided difference on "
                        + "the prefix a_0, ..., a_j. At complete coalescence at a, it is "
                        + "p_0^(j)(a)/j!. The same monic division defines the data for mixed "
                        + "multiplicities. De Boor supplies the classical interpolation convention."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("confluent-weighted-newton-tail-uniform-lower"),
                DeclarationHandle.Create(Module + ".weightedNewtonTail_uniform_lower"),
                H("One lower bound holds for every node vector in the interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(DeBoor)),
                Blocks(
                    Paragraph(Text("For natural numbers m, r > 0 and real endpoints "
                        + "0 < lo <= hi, there is a real delta > 0 such that "
                        + "delta * ||v||_infinity <= ||weightedNewtonTail(r, a)(v)||_infinity "
                        + "for every indexed node vector a in [lo, hi]^(m+1) and every signed "
                        + "real coefficient vector v of length m. Delta is chosen before a and v. "
                        + "Coincident nodes and lo = hi are allowed.")),
                    Paragraph(Text("If the measured tail vanishes, the weighted polynomial minus "
                        + "its order-zero value is divisible by the product of all nodal factors. "
                        + "It has at most m + 1 nonzero monomials. Descartes' rule counts positive "
                        + "roots with multiplicity and forces this polynomial to vanish. The "
                        + "positive weight exponent then forces the coefficient vector to vanish.")),
                    Paragraph(Text("Finite coefficient sums give joint continuity through node "
                        + "collisions. The data norm has a positive minimum on the product of "
                        + "the node cube and the unit coefficient sphere. Homogeneity extends "
                        + "this lower bound to all coefficient vectors."))),
                DescribeRole.Theorem),
            Paragraph(Text("The separated-grid coefficient-energy bound is a related frozen result. "),
                Ref("D5/S3/Analytic/Interpolation/DiscreteCoefficientSampling.discrete_coefficient_sampling_lower")))));
}
