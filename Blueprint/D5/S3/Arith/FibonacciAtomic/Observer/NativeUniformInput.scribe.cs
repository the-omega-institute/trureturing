using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeUniformInputDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformInput.";
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeuniforminput-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed native common input and cell factory", H("NativeUniformInput"), Blocks(
            Paragraph(Text("CommonCode is the product of the existing rowWord constructor list, the lexicographically sorted finite Q address list, the existing chronological mixed-epoch history codes and N. The four reply codes remain 0,1,2,3. Contradictory and unreachable finite histories remain computation inputs. The decoder and cell factory are uniformly primitive recursive before quantification over old rows, Q, H and N. Numeric old class names are preserved, including gaps and repeated occurrences; names are never replaced by dense class ranks. The exact depth is the current requiredDepth. This stage does not decide feasible cells, run the unifier, compute the ground-binding criterion or budget, or certify the whole controller.")),
            Paragraph(Text("The matching Reg mirror proves typed whole-family reconstruction, variation, role sensitivity and actual observational dependence on the complete infinite domain. Contract source-selection coordinates and raw source-occurrence binding remain unregistered. No validated four-slot audit status is claimed.")),
            Entry("codeCommon", "codeCommon", "Encode the actual old literal row, finite sorted address presentation, arbitrary chronological coded history and unbounded epoch without a source value or a reachability oracle.", DescribeRole.Definition),
            Entry("materializeCells", "materializeCells", "Decode the fixed common input and return the exact required depth, original numeric class names and complete list of coded native pattern families. Malformed row or reply codes return none.", DescribeRole.Definition),
            Entry("uniform_common_codec", "uniform common codec", "There is one primitive recursive parseCommon. For every C,Q,H,N it round-trips codeCommon to C, sorted Q, H and N. This computational supplier is consumed by uniform_cell_materializer.", DescribeRole.Theorem),
            Entry("uniform_cell_materializer", "uniform cell materializer", "There is one primitive recursive materializeCells. For every common input it returns exactly requiredDepth Q H, classList C mapped to original labels, and allPatterns C at that depth mapped through familyWord. Structural row-name folding, duplicate elimination, numeric sorting and exact dependent family enumeration lie on the proof path. The variable-cell materializer consumes this result.", DescribeRole.Theorem))));
}
