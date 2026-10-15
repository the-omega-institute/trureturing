using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class GeneralIdealDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attributed analytic trace infrastructure, used by the original-operator quantum bridge.",
        H("Analytic trace in an arbitrary basis"), Blocks(Describe.Lean(
            DescribeId.Create("attributed-traceclass-generalideal"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/GeneralIdeal.trace_eq_of_hilbertBasis"),
            H("Analytic trace in an arbitrary basis"), StatementSource.FromAuthor(Endpoint()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/diem2026traceclass")),
            Blocks(Paragraph(Text("For every trace-class bounded operator T and every set-indexed Hilbert basis e, the genuine trace of T equals the convergent sum of inner products of e of i with T applied to e of i. No positivity or self-adjointness premise on T is required. The consumer uses this for the original products rho B and sigma B squared.")),
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
        Formula conclusion = Equal(Call("trace", t), Call("tsum", new Formula.Sequence(
            Call("inner", ei, new Formula.Apply(t, [ei])), i, w)));
        return All([new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")), new(FormulaIdentifier.Create("w"), Call("Set", h)),
            new(FormulaIdentifier.Create("e"), Call("HilbertBasis", w, h)), new(FormulaIdentifier.Create("T"), op)], Implies(Call("IsTraceClass", t), conclusion));
    }
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(Formula.BoundVariable[] xs, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. xs], body);
}
