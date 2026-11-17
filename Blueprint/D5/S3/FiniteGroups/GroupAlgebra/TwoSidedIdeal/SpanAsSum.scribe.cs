using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra.TwoSidedIdeal;

internal sealed class TwoSidedIdealSpanAsSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite multiplier sums in a simple ring.", H("Finite multiplier sums in a simple ring."), Blocks(
            Paragraph(Ref("D5/S3/FiniteGroups/GroupAlgebra/TwoSidedIdeal/SpanAsSum")),
            Paragraph(Text("The statement and proof are reused from AxiomMath/Stacks contributors, revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. The source retains the exact upstream paths and SHA-256 hashes. This is classical algebra used for the actual finite-group representation image; no new algebra theorem is claimed.")),
            Paragraph(Math(Disp(Statement()))),
            Paragraph(Text("In a simple ring, every nonzero element generates the unit two-sided ideal. Membership in a generated two-sided ideal is expressed by a finite sum of left and right multiples. Applying this to one gives the displayed finite multiplier identity. It normalizes a nonzero coefficient in the tensor-simplicity proof; the length is existential and no bounded search is used.")))));

    private static Formula Statement()
    {
        Formula r = I("R"), a = I("a"), i = I("i"), x = I("x"), y = I("y"), n = I("n");
        Formula sum = Seq(Sum, Underscore, Grp(i, Colon, App(I("Fin"), n)), Sp, Mul(Mul(App(x, i), a), App(y, i)));
        Formula p = Ex("n", I("Nat"), Ex("x", Arr(App(I("Fin"), n), r),
            Ex("y", Arr(App(I("Fin"), n), r), Eq(sum, D(1)))));
        p = All("a", r, ImpTo(new Formula.Not(Eq(a, D(0))), p));
        p = Inst(App(I("IsSimpleRing"), r), p);
        p = Inst(App(I("Ring"), r), p);
        return All("R", Ty(), p);
    }

    private static Formula I(string s) => F.Id(s);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Ex(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, p);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula ImpTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Inst(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
    private static Formula Ty() => Seq(I("Type"), Star);

}
