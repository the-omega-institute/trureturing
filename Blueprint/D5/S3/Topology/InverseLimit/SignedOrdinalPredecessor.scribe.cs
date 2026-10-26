using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalPredecessorDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalPredecessor.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Old carriers and permanent arrivals at the next ordinal predecessor",
        H("Actual predecessor data"), Blocks(
            Describe.Lean(DescribeId.Create("actual-next-predecessor"),
                DeclarationHandle.Create(Owner + "nextP"), H("Executed split to next predecessor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("Fix the original Prefix H, omega<=a, Predecessor P, launch, Prepared Q, treatment t and executed Result R. A row below the new row a+1 has value at most a and is a current Rows(a) value. Every next coordinate d<a+1 is exactly a current Cols(a) value, including d=a. The next reservoirs use the actual R.I and R.J. Their disjointness and infinite intersections follow from R.B and R.C after R.birth_readback identifies the actual arrival at succ(max(row,label)) with R.N.")),
            Paragraph(Text("The old carrier equation R.coordinates.old_carrier transports support families and regular signed sequences by literal equality. At row a the support enumeration is Q.U; at every older row it is P.U. Each row uses the actual Q.V and Q.nu on all Label values, with their original surjectivity certificates. The enlarged Prefix has genuine onto coordinate restrictions. Its restriction onto the original omega cube follows by composing its restriction to stage a with P.base_onto. Properness is succ(a)<omega-one.")),
            Paragraph(Text("nextP constructs the actual Predecessor on R.coordinates.extended with omega<=succ(a). Its E and F fields apply Result.literal_e and Result.literal_f. Top-carrier and old-base equalities identify the literal projections, support membership and original signed pushforwards. Equality transport preserves total variation and weak-dual convergence. The next F coordinate d<a+1 becomes the current column d<=a, with the same original Q.nu label and no additional convergence assumption.")),
            Paragraph(Text("The original Q and R remain available in the telescope for the full historical construction. In particular Q.U and Q.nu retain every Label value, Q.B retains every natural enumeration index, and Q.V retains every current row. A Predecessor contains no old B enumeration, and R.arrival stores only N-entry functions. Neither arrival nor a next predecessor reconstructs the complete original birth data. No historical execution or final omega-one construction follows from these data alone."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("regular-bounded-next-f"),
                DeclarationHandle.Create(Owner + "next_regular_f"), H("Regular bounded convergence from the same Result"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every eligible old row and label of the next predecessor, any original norm-one signed lift sequence on its literal top carrier converges along that predecessor's J to a signed measure with regular Jordan parts and real total variation at most one. The proof applies the same R.literal_f after exact top and row carrier equality. The entire current U, V and nu functions are retained by next_U_readback, next_V_readback and next_nu_readback, including all whole birth labels."))), DescribeRole.Theorem))));
}
