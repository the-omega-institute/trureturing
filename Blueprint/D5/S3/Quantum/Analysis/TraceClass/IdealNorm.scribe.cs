using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class IdealNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic trace norms and bounded trace pairings on arbitrary complete complex Hilbert spaces.",
        H("The two-sided trace-norm ideal estimate"), Blocks(Describe.Lean(
            DescribeId.Create("attributed-traceclass-idealnorm"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/IdealNorm.traceNorm_mul_mul_le"),
            H("The two-sided trace-norm ideal estimate"), StatementSource.FromAuthor(Endpoint()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/diem2026traceclass")),
            Blocks(Paragraph(Text("For arbitrary bounded A and B and an actual trace-class T, the operator A T B is trace class and has trace norm at most the product of the operator norms of A and B and the trace norm of T. The supplied proof uses polar factorization and the Hilbert-Schmidt product estimate.")),
                Paragraph(Text("Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The original copyright notice and license are preserved. No mathematical originality is claimed for these suppliers."))),
            DescribeRole.Theorem))));
    private static Formula Endpoint()
    {
        Formula h = F.Id("H"), a = F.Id("A"), t = F.Id("T"), b = F.Id("B");
        Formula op = Call("BoundedComplexOperator", h), atb = Call("mul", Call("mul", a, t), b);
        Formula bound = new Formula.Relation(Call("traceNorm", atb), FormulaRelationOperator.LessThanOrEqual,
            Call("mul", Call("mul", Call("norm", a), Call("traceNorm", t)), Call("norm", b)));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")),
             new(FormulaIdentifier.Create("A"), op), new(FormulaIdentifier.Create("T"), op),
             new(FormulaIdentifier.Create("B"), op)],
            new Formula.Logic(new Formula.Logic(Call("IsTraceClass", t), FormulaLogicOperator.And,
                Call("IsTraceClass", atb)), FormulaLogicOperator.Implies, bound));
    }
}
