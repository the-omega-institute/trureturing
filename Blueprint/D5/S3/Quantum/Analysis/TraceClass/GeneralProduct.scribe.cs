using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class GeneralProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attributed analytic trace infrastructure, used by the original-operator quantum bridge.",
        H("The actual trace-class product and ideal"), Blocks(Describe.Lean(
            DescribeId.Create("attributed-traceclass-generalproduct"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/GeneralProduct.isTraceClass_mul_of_isHilbertSchmidt"),
            H("The actual trace-class product and ideal"), StatementSource.FromAuthor(Endpoint()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/diem2026traceclass")),
            Blocks(Paragraph(Text("For two arbitrary Hilbert-Schmidt bounded operators R and S on a complete complex Hilbert space, their product is trace class. The supplied proof uses the general polar factor and the supplied scalar square-sum estimate. Its two-sided bounded ideal consequence is used to form the original analytic traces in the quantum bridge.")),
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
        return All([new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")), new(FormulaIdentifier.Create("R"), op), new(FormulaIdentifier.Create("S"), op)],
            Implies(And(Call("IsHilbertSchmidt", r), Call("IsHilbertSchmidt", s)),
                Call("IsTraceClass", Mul(r, s))));
    }
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(Formula.BoundVariable[] xs, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. xs], body);
}
