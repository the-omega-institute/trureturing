using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class PolarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attributed analytic trace infrastructure, used by the original-operator quantum bridge.",
        H("Actual polar factorization"), Blocks(Describe.Lean(
            DescribeId.Create("attributed-traceclass-polar"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/Polar.polarFactor_mul_absOperator"),
            H("Actual polar factorization"), StatementSource.FromAuthor(Endpoint()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/diem2026traceclass")),
            Blocks(Paragraph(Text("For every bounded operator T on a complete complex Hilbert space, the supplied contraction polarFactor of T multiplied by the actual continuous-functional-calculus absolute operator is T. No invertibility, closed range, finite dimension, or self-adjointness premise is introduced.")),
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
        return All([new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")), new(FormulaIdentifier.Create("T"), op)],
            Equal(Mul(Call("polarFactor", t), Call("absOperator", t)), t));
    }
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(Formula.BoundVariable[] xs, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. xs], body);
}
