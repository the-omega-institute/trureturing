using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicNativeFiveProbesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Good native reductions give uniform repeated-root and irreducible mod-five Frobenius inputs.",
        H("Exact group point counts for the native mod-five Frobenius probes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-five-actual-point-cardinality"),
                DeclarationHandle.Create(Module + "card_curve_points"),
                H("The pair enumeration counts the actual curve group"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The good short Weierstrass model has exactly one point at infinity. Nonsingular affine "
                    + "points correspond bijectively to all pairs satisfying the finite-field curve equation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-five-repeated-root-probe"),
                DeclarationHandle.Create(Module + "native_repeated_root_probe"),
                H("Every native level has a good repeated-root probe at eleven or thirty-one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four-state Lucas cycles give point counts 9 or 15 at eleven on odd levels and 24 or "
                    + "40 at thirty-one on even levels. The trace squared is four modulo five, and neither the "
                    + "point count nor its complementary twist count is divisible by twenty-five."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-five-nonsplit-probe"),
                DeclarationHandle.Create(Module + "native_nonsplit_probe23"),
                H("At twenty-three the trace polynomial has no root modulo five"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four relevant native Lucas residues give counts 24, 16, 24 and 32. At every level "
                    + "the actual good-reduction point count therefore gives a root-free quadratic over F5. No "
                    + "Galois-inertia theorem is asserted by this endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-five-good-prime17-probe"),
                DeclarationHandle.Create(Module + "native_good_probe17"),
                H("At seventeen the whole native orbit has point count fifteen"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The initial Lucas state four enters the two-cycle eight and nine. All three reduced "
                    + "models have nonzero discriminant and exactly fifteen points."))),
                DescribeRole.Theorem))));
}
