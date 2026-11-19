using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class SkolemNoetherDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inner automorphisms of a finite central simple algebra.", H("Inner automorphisms of a finite central simple algebra."), Blocks(
            Paragraph(Ref("D5/S3/FiniteGroups/GroupAlgebra/SkolemNoether")),
            Paragraph(Text("The statement and proof are reused from AxiomMath/Stacks contributors, revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. The source retains the exact upstream paths and SHA-256 hashes. This is classical algebra used for the actual finite-group representation image; no new algebra theorem is claimed.")),
            Paragraph(Math(Disp(Statement()))),
            Paragraph(Text("The Skolem-Noether theorem identifies every algebra automorphism of a finite central simple algebra with conjugation by a unit. The regular representations twisted by the automorphism and by the identity have equal scalar dimensions. Morita theory gives an equivalence; commutation with right multiplication identifies it with multiplication by its value at one. In the representation application the base field is the actual image center, and the unit is obtained only after center-fixing has been proved.")))));

    private static Formula Statement()
    {
        Formula k = I("K"), a = I("A"), e = I("e"), x = I("x"), z = I("z");
        Formula p = Ex("x", App(I("Units"), a), All("z", a,
            Eq(App(e, z), Mul(Mul(x, z), App(Q("Inv", "inv"), x)))));
        p = All("e", App(I("AlgEquiv"), k, a, a), p);
        p = Inst(App(I("IsSimpleRing"), a), p);
        p = Inst(App(Q("Algebra", "IsCentral"), k, a), p);
        p = Inst(App(Q("Module", "Finite"), k, a), p);
        return AlgebraInputs(p, false);
    }

    private static Formula I(string s) => F.Id(s);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(I(a)), Dot, Operatorname, Grp(I(b)));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Ex(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, p);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
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
