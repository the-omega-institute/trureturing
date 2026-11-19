using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra.Morita;

internal sealed class MoritaSimpleRingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dimensions determine modules over a finite simple algebra.", H("Dimensions determine modules over a finite simple algebra."), Blocks(
            Paragraph(Ref("D5/S3/FiniteGroups/GroupAlgebra/Morita/SimpleRing")),
            Paragraph(Text("The statement and proof are reused from AxiomMath/Stacks contributors, revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. The source retains the exact upstream paths and SHA-256 hashes. This is classical algebra used for the actual finite-group representation image; no new algebra theorem is claimed.")),
            Paragraph(Math(Disp(Statement()))),
            Paragraph(Text("Over a finite-dimensional simple algebra, finite modules are equivalent exactly when their dimensions over the base field agree. Matrix Morita equivalence expresses both as sums of one simple module. Finite dimension makes the multiplicity sets finite, and equality of dimensions identifies those sets. The zero module is handled separately. This criterion compares the two twisted regular modules in the Skolem-Noether argument.")))));

    private static Formula Statement()
    {
        Formula k = I("K"), a = I("A"), m = I("M"), n = I("N");
        Formula p = IffTo(App(I("Nonempty"), App(I("LinearEquiv"), App(Q("RingHom", "id"), a), m, n)),
            Eq(App(Q("Module", "finrank"), k, m), App(Q("Module", "finrank"), k, n)));
        foreach (string s in new[] { "N", "M" })
        {
            Formula v = I(s);
            p = Inst(App(Q("Module", "Finite"), a, v), p);
            p = Inst(App(I("IsScalarTower"), k, a, v), p);
            p = Inst(App(I("Module"), k, v), p);
            p = Inst(App(I("Module"), a, v), p);
            p = Inst(App(I("AddCommGroup"), v), p);
        }
        p = All("M", Ty(), All("N", Ty(), p));
        p = Inst(App(Q("Module", "Finite"), k, a), p);
        p = Inst(App(I("IsSimpleRing"), a), p);
        return AlgebraInputs(p, false);
    }

    private static Formula I(string s) => F.Id(s);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(I(a)), Dot, Operatorname, Grp(I(b)));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Inst(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
    private static Formula Ty() => Seq(I("Type"), Star);
    private static Formula AlgebraInputs(Formula p, bool two)
    {
        if (two) { p = Inst(App(I("Algebra"), I("K"), I("B")), p); p = Inst(App(I("Ring"), I("B")), p); }
        p = Inst(App(I("Algebra"), I("K"), I("A")), p);
        p = Inst(App(I("Ring"), I("A")), p);
        p = Inst(App(I("Field"), I("K")), p);
        if (two) p = All("B", Ty(), p);
        return All("K", Ty(), All("A", Ty(), p));
    }
}
