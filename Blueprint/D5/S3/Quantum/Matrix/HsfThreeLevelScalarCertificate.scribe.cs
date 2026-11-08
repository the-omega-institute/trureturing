using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfThreeLevelScalarCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfThreeLevelScalarCertificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex PSD3 cubic geometry and exact scalar coefficients.",
        H("HsfThreeLevelScalarCertificate"),
        Blocks(
            Entry("monomialSymmetric", "monomialSymmetric",
                "For a partition i>=j>=k, the sum over distinct permutations of p^i q^j r^k, with repeated exponents counted only once.", DescribeRole.Definition),
            Entry("pairedMonomial", "pairedMonomial",
                "The degree-fifty-one partition term and its complementary partition, except at the middle row j=17.", DescribeRole.Definition),
            Entry("boundaryW", "boundaryW",
                "The factored nonnegative boundary polynomial (p-q)^2(p+q)H(p,q)^2(p^2-pq+q^2)^2(p^2+7pq+q^2)^2.", DescribeRole.Definition),
            Entry("boundaryCertificate", "boundaryCertificate",
                "The three cyclic boundary terms of the complete P396 quotient, retained in their nonnegative factorization.", DescribeRole.Definition),
            Entry("positiveSlice1", "positiveSlice1",
                "The fixed positive symmetric terms in row 1 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice2", "positiveSlice2",
                "The fixed positive symmetric terms in row 2 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice3", "positiveSlice3",
                "The fixed positive symmetric terms in row 3 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice4", "positiveSlice4",
                "The fixed positive symmetric terms in row 4 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice5", "positiveSlice5",
                "The fixed positive symmetric terms in row 5 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice6", "positiveSlice6",
                "The fixed positive symmetric terms in row 6 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice7", "positiveSlice7",
                "The fixed positive symmetric terms in row 7 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice8", "positiveSlice8",
                "The fixed positive symmetric terms in row 8 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice9", "positiveSlice9",
                "The fixed positive symmetric terms in row 9 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice10", "positiveSlice10",
                "The fixed positive symmetric terms in row 10 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice11", "positiveSlice11",
                "The fixed positive symmetric terms in row 11 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice12", "positiveSlice12",
                "The fixed positive symmetric terms in row 12 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice13", "positiveSlice13",
                "The fixed positive symmetric terms in row 13 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice14", "positiveSlice14",
                "The fixed positive symmetric terms in row 14 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice15", "positiveSlice15",
                "The fixed positive symmetric terms in row 15 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice16", "positiveSlice16",
                "The fixed positive symmetric terms in row 16 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveSlice17", "positiveSlice17",
                "The fixed positive symmetric terms in row 17 of the complete P396 table; this row is used in the exact quotient decomposition.", DescribeRole.Definition),
            Entry("positiveCertificate", "positiveCertificate",
                "The complete boundary contribution plus all 81 table entries, representing 145 positive symmetric monomial terms.", DescribeRole.Definition),
            Entry("certificate_nonneg", "certificate nonneg",
                "The explicit quotient certificate is nonnegative on every nonnegative triple.", DescribeRole.Theorem),
            Entry("certificate_pos", "certificate pos",
                "The central positive term ensures strict positivity of the quotient on every positive triple.", DescribeRole.Theorem),
            Paragraph(Text("The statements concern the explicitly defined closed algebraic kernels. "
                + "The commutant equality classification, identification with the original integrals, "
                + "dominated differentiation and original HSF derivative/source bridge remain outside these results. "
                + "No assertion about arbitrary matrix dimension or literature novelty follows.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsfthreelevelscalarcertificate-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
