using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class BanachDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic trace norms and bounded trace pairings on arbitrary complete complex Hilbert spaces.",
        H("The genuine trace-class Banach space"), Blocks(Describe.Lean(
            DescribeId.Create("attributed-traceclass-banach"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/Banach.isTraceClass_of_tendsto_of_traceNorm_bounded"),
            H("The genuine trace-class Banach space"), StatementSource.FromAuthor(Endpoint()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/diem2026traceclass")),
            Blocks(Paragraph(Text("The trace norm equips the trace-class submodule with a complete complex normed-space structure. The operator norm is bounded by the trace norm. Uniformly trace-norm-bounded operator-norm limits are trace class with the same bound; this supplies the completeness proof.")),
                Paragraph(Text("Attributed to Tom Ole Diem, Physlib at immutable revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. The original copyright notice and license are preserved. No mathematical originality is claimed for these suppliers."))),
            DescribeRole.Theorem))));
    private static Formula Endpoint()
    {
        Formula h = F.Id("H"), tn = F.Id("Tn"), t = F.Id("T"), c = F.Id("C");
        Formula op = Call("BoundedComplexOperator", h);
        Formula premise = new Formula.Logic(Call("EachTraceClass", tn), FormulaLogicOperator.And,
            new Formula.Logic(Call("UniformTraceNormBound", tn, c), FormulaLogicOperator.And,
                Call("TendstoOperatorNorm", tn, t)));
        Formula conclusion = new Formula.Logic(Call("IsTraceClass", t), FormulaLogicOperator.And,
            new Formula.Relation(Call("traceNorm", t), FormulaRelationOperator.LessThanOrEqual, c));
        return new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")),
             new(FormulaIdentifier.Create("Tn"), Call("Sequence", op)),
             new(FormulaIdentifier.Create("T"), op), new(FormulaIdentifier.Create("C"), F.Id("Real"))],
            new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion));
    }
}
