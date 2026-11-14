using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233178ChromaticDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233178Chromatic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact three-label transfer on the five-row horizontal and diagonal exclusion graph.",
        H("Literal columns and continuation counts"),
        Blocks(
            Paragraph(Text("A column is encoded in base three, with row r stored in digit r. "
                + "Bond tests precisely the pairs of rows at distance at most one across consecutive "
                + "columns. No condition is imposed within a column, or between the first and last columns.")),
            Node("colour", "The five literal row entries", "The base-three digits of an integer below 243 "
                + "give the five independent row entries, in their original row order.", DescribeRole.Definition),
            Node("Bond", "Horizontal and diagonal exclusion", "Every entry in one column differs from "
                + "the entries in the next column at the same row and either adjacent row.", DescribeRole.Definition),
            Node("T", "Exact transfer matrix", "The integer matrix has an entry one precisely for "
                + "a legal pair of consecutive columns, and zero otherwise.", DescribeRole.Definition),
            Node("v", "Continuation readout", "The nth transfer power applied to the constant one "
                + "vector counts n-column continuations of a specified boundary column.", DescribeRole.Definition),
            Node("result", "Continuation recurrence beyond the transient", "For every integer vector w "
                + "and every natural n, put b(k)=dotProduct(w,v(k)). Then "
                + "b(n+11)=6*b(n+10)+31*b(n+9)-97*b(n+8)-163*b(n+7) "
                + "+417*b(n+6)+93*b(n+5)-514*b(n+4)+192*b(n+3)+72*b(n+2)-36*b(n+1). "
                + "The proof checks the finite continuation certificate and applies the existing "
                + "TransferMatrix.scalarRelationShift theorem. This is an auxiliary three-label result; "
                + "it does not by itself prove the normalized six-colour A233178 recurrence.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
