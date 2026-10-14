using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class HilbertSchmidtDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Attributed analytic trace infrastructure, used by the original-operator quantum bridge.",
        H("Scalar square-sum Cauchy-Schwarz"), Blocks(Describe.Lean(
            DescribeId.Create("attributed-traceclass-hilbertschmidt"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt.tsum_mul_le_sqrt_mul_sqrt"),
            H("Scalar square-sum Cauchy-Schwarz"), StatementSource.FromAuthor(Endpoint()),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/diem2026traceclass")),
            Blocks(Paragraph(Text("For nonnegative real families f and g on any set-indexed basis carrier, summability of their squares bounds the sum of their products by the product of the square roots of their square sums. The same supplied module gives product summability, basis-independent Hilbert-Schmidt square sums, and bounded multiplication closure. The consumer applies these supplied estimates directly rather than reproving them.")),
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
        Formula fi = new Formula.Apply(f, [i]), gi = new Formula.Apply(g, [i]);
        Formula fsq = Call("tsum", new Formula.Sequence(Call("square", fi), i, w));
        Formula gsq = Call("tsum", new Formula.Sequence(Call("square", gi), i, w));
        Formula assumptions = And(Call("Summable", new Formula.Sequence(Call("square", fi), i, w)),
            And(Call("Summable", new Formula.Sequence(Call("square", gi), i, w)),
                And(Call("NonnegativeFamily", f), Call("NonnegativeFamily", g))));
        return All([new(FormulaIdentifier.Create("H"), F.Id("Type")), new(FormulaIdentifier.Create("w"), Call("Set", h)),
            new(FormulaIdentifier.Create("f"), new Formula.TypeArrow(w, real)), new(FormulaIdentifier.Create("g"), new Formula.TypeArrow(w, real))],
            Implies(assumptions, new Formula.Relation(
                Call("tsum", new Formula.Sequence(Mul(fi, gi), i, w)), FormulaRelationOperator.LessThanOrEqual,
                Mul(Call("sqrt", fsq), Call("sqrt", gsq)))));
    }
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(Formula.BoundVariable[] xs, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. xs], body);
}
