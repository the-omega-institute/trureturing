using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class TraceAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic trace norms and bounded trace pairings on arbitrary complete complex Hilbert spaces.",
        H("Cyclicity with a bounded factor"), Blocks(Describe.Lean(
            DescribeId.Create("attributed-traceclass-tracealgebra"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/TraceAlgebra.trace_mul_cycle"),
            H("Cyclicity with a bounded factor"), StatementSource.FromAuthor(Endpoint()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/diem2026traceclass")),
            Blocks(Paragraph(Text("For a bounded A and an actual trace-class T, the analytic traces of A T and T A agree. Scalar homogeneity and additivity use the basis-independent absolutely summable diagonals. No finite-dimensional algebraic trace is substituted.")),
                Paragraph(Text("Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The original copyright notice and license are preserved. No mathematical originality is claimed for these suppliers."))),
            DescribeRole.Theorem))));
    private static Formula Endpoint()
    {
        Formula h = F.Id("H"), a = F.Id("A"), t = F.Id("T");
        Formula op = Call("BoundedComplexOperator", h);
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")),
             new(FormulaIdentifier.Create("A"), op), new(FormulaIdentifier.Create("T"), op)],
            new Formula.Logic(Call("IsTraceClass", t), FormulaLogicOperator.Implies,
                Equal(Call("trace", Call("mul", a, t)), Call("trace", Call("mul", t, a)))));
    }
}
