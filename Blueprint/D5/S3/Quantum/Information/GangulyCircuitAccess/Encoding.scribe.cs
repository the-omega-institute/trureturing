using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GangulyCircuitAccess;

internal sealed class GangulyEncodingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GangulyCircuitAccess/Encoding.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/ganguly2026stabilizersecretsharing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two distinct logical pure states have exactly the same retained density matrix.",
        H("Operational reduction of the graph-state encoding"),
        Blocks(
            Node("encoding-dealerslices", "dealerSlices", "Normalized dealer slices",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "Take the complex cast of the integer graph sign for joint configuration (c,a,s) and divide by the complex cast of the real square root of 2 raised to n − 1. The exponent uses natural subtraction. Rows are ordered discarded first and retained second. Columns are dealer bits. For the witness the denominator is 8."),
            Node("encoding-reducedencoding", "reducedEncoding", "Encode and take the discarded partial trace",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "Form VρV† using the dealer-slice matrix V and the logical matrix ρ. At retained row a and column b, take the trace of the block with rows (c,a) and columns (c,b). This equals the sum of (VρV†)((c,a),(c,b)) over discarded configurations c."),
            Node("encoding-witness-encoding-isometry", "witness_encoding_isometry", "Orthonormal encoding columns",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "For the witness, V†V equals the two by two identity. The integer Gram matrix is 64 times the identity and normalization divides it by 64."),
            Node("encoding-logicaldensity", "logicalDensity", "Logical density matrix at the two signs",
                StatementSource.WithoutFormula(), DescribeRole.Definition,
                "The logical matrix has both diagonal entries 1/2 and both off-diagonal entries sign/2 for a complex sign. The pure-state assertion below concerns the two real signs +1 and −1."),
            Node("encoding-logical-x-pure", "logical_x_pure", "Pure logical inputs",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "For each Boolean selecting the negative sign, there is a vector v in the logical two-dimensional complex space with sum of v(i) times its conjugate equal to one, whose outer product equals the selected logical matrix. These are the projectors onto (|0⟩ + |1⟩)/√2 and (|0⟩ − |1⟩)/√2."),
            Node("encoding-logical-x-distinct", "logical_x_distinct", "Distinct logical matrices",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "The logical matrices at +1 and −1 differ at entry (0, 1)."),
            Node("encoding-witness-reduced-density-eq", "witness_reduced_density_eq", "Exact equality of the retained states",
                StatementSource.WithoutFormula(), DescribeRole.Theorem,
                "On the witness graph with dealer 4 and retained set {2, 5, 6}, the two input projectors give the same partial trace. The two diagonal entries of the input difference vanish, and both off-diagonal entries are one. Each entry of the output difference is the sum of the forward and reverse cross sums divided by 64. The forward sum vanishes by the integer certificate and the reverse sum follows by swapping a with b and commuting the integer factors."))));

    private static DocumentBlock Node(string id, string name, string title, StatementSource statement,
        DescribeRole role, string prose) => Describe.Lean(
        DescribeId.Create("ganguly-circuit-access-" + id), DeclarationHandle.Create(Prefix + name),
        H(title), statement, AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
