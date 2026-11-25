using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy;
internal sealed class DiagonalLinearCodeMomentsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/DiagonalLinearCodeMoments.";
    private static readonly LibraryNoteRef Gce = LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real-order subsystem moments of separable diagonal finite-field codes are controlled by the column ranks.",
        H("Partial trace of a diagonal code is uniform on the projected code"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-column-moment"), DeclarationHandle.Create(Owner + "actual_column_moment"),
                H("The exact reduced-state power trace"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(Gce), Blocks(
                    Paragraph(Text("Choose a uniformly distributed linear functional on the message space and evaluate it on each column. The joint density matrix is explicitly a convex sum of products of computational-basis projectors. Tracing out the complement computes an ordinary coordinate pushforward. Nonempty fibers are translates of the kernel, and the image has dimension equal to the span of the selected columns by dual restriction.")),
                    Paragraph(Text("The normalized marginal is a scaled projector of rank Q to the power r(S), so continuous functional calculus gives its actual real power trace. This covers arbitrary finite fields and K strictly positive. It does not assume a coverage law."))), DescribeRole.Theorem))));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Statement()
    {
        var c = F.Id("C"); var s = F.Id("S"); var k = F.Id("K");
        return Disp(All("C", Call("FiniteFieldColumnConfiguration"), All("S", Call("Subsets", Call("Sites", c)),
            All("K", Call("PositiveReals"), Equal(Call("TrPower", Call("ActualMarginal", c, s), k),
                Call("Pow", Call("AlphabetSize", c), Call("Mul", Call("Sub", Num(1), k), Call("ColumnRank", c, s))))))));
    }
}
