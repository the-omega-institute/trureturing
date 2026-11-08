using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Frobenius;

internal sealed class FiniteIsotypicImageSimpleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simplicity of the actual image on an isotypic semisimple module.", H("Simplicity of the actual image on an isotypic semisimple module."),
        Blocks(
            Paragraph(Text("The matrix and double-centralizer theorems are reused from Mathlib. The constructed range identification supplies simplicity of the actual restricted group-algebra image used by the normalizer center action. The field, acting algebra and carrier universes are independent.")),
            Describe.Lean(DescribeId.Create("finiteisotypicimagesimple-issimplering-actionrange"), DeclarationHandle.Create("D5/S3/FiniteGroups/Frobenius/FiniteIsotypicImageSimple.isSimpleRing_actionRange"), H("isSimpleRing actionRange"), StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a nonzero finite-dimensional semisimple isotypic module, its endomorphism algebra is a matrix algebra over a division ring. The same holds for the bicommutant. The finite double-centralizer surjectivity theorem identifies that bicommutant with the actual action range by an explicitly bijective ring map. Thus the image itself is simple; simplicity is not an extra assumption."))), DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula k = I("k"), r = I("R"), u = I("U");
        Formula action = Seq(App(Q("Algebra", "lsmul"), k, k, u), Open, Operatorname, Grp(I("A")), Colon, F.Eq, r, Close);
        Formula p = App(I("IsSimpleRing"), App(Q("AlgHom", "range"), action));
        p = All("hU", App(I("IsIsotypic"), r, u), p);
        p = Inst(App(I("IsSemisimpleModule"), r, u), p);
        p = Inst(App(I("Nontrivial"), u), p);
        p = Inst(App(Q("Module", "Finite"), k, u), p);
        p = Inst(App(I("IsScalarTower"), k, r, u), p);
        p = Inst(App(I("Module"), r, u), p); p = Inst(App(I("Module"), k, u), p);
        p = Inst(App(I("AddCommGroup"), u), p);
        p = Inst(App(I("Algebra"), k, r), p); p = Inst(App(I("Ring"), r), p); p = Inst(App(I("Field"), k), p);
        return All("k", Ty(), All("R", Ty(), All("U", Ty(), p)));
    }

    private static Formula I(string s) => F.Id(s);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(I(a)), Dot, Operatorname, Grp(I(b)));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Inst(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
    private static Formula Ty() => Seq(I("Type"), Star);
}
