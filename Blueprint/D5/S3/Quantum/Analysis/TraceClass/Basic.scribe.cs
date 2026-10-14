using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attributed analytic trace infrastructure, used by the original-operator quantum bridge.",
        H("Positive analytic trace in every basis"), Blocks(Describe.Lean(
            DescribeId.Create("attributed-traceclass-basic"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/Basic.trace_eq_of_hilbertBasis_of_nonneg"),
            H("Positive analytic trace in every basis"), StatementSource.FromAuthor(Endpoint()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/diem2026traceclass")),
            Blocks(Paragraph(Text("For any positive trace-class bounded operator T on a complete complex Hilbert space, its actual analytic trace is the sum of its diagonal in any set-indexed Hilbert basis. Trace-class membership is defined through the absolute operator and summability. The finite-dimensional algebraic trace is used only in compatibility statements; the infinite-dimensional consumer uses the analytic trace.")),
                Paragraph(Text("Attributed to Tom Ole Diem, Physlib at immutable revision "
                    + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. "
                    + "The minimal five-module closure is consumed by the concrete quadratic-reference "
                    + "Hilbert-Schmidt bridge. This supplier adoption claims no mathematical originality. "
                    + "An equivalent consumed result at the repository-pinned Mathlib replaces the transplant."))),
            DescribeRole.Theorem))));
    private static Formula Endpoint()
    {
        Formula h = F.Id("H"), w = F.Id("w"), e = F.Id("e"), t = F.Id("T");
        Formula r = F.Id("R"), s = F.Id("S"), i = F.Id("i");
        Formula f = F.Id("f"), g = F.Id("g");
        Formula op = Call("BoundedComplexOperator", h), real = Seq(Mathbb, Grp(F.Id("R")));
        Formula ei = new Formula.Apply(e, [i]);
        Formula assumptions = And(Call("IsTraceClass", t), Call("Nonnegative", t));
        Formula conclusion = Equal(Call("trace", t), Call("tsum", new Formula.Sequence(
            Call("inner", ei, new Formula.Apply(t, [ei])), i, w)));
        return All([new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")), new(FormulaIdentifier.Create("w"), Call("Set", h)),
            new(FormulaIdentifier.Create("e"), Call("HilbertBasis", w, h)), new(FormulaIdentifier.Create("T"), op)], Implies(assumptions, conclusion));
    }
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(Formula.BoundVariable[] xs, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. xs], body);
}
