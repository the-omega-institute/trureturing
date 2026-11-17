using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra.SimpleRing;

internal sealed class SimpleRingTensorProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tensor simplicity for the group-algebra image argument.", H("Tensor simplicity for the group-algebra image argument."), Blocks(
            Paragraph(Ref("D5/S3/FiniteGroups/GroupAlgebra/SimpleRing/TensorProduct")),
            Paragraph(Text("The statement and proof are reused from AxiomMath/Stacks contributors, revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. The source retains the exact upstream paths and SHA-256 hashes. This is classical algebra used for the actual finite-group representation image; no new algebra theorem is claimed.")),
            Paragraph(Math(Disp(Statement()))),
            Paragraph(Text("The tensor product of a simple algebra and a central simple algebra is simple. In the left-central proof, a nonzero tensor coefficient is normalized by a finite left-right multiplier sum. Commutators reduce the support until centrality forces the coefficients into the base field. Ideal extension and contraction then identify every ideal with the ideal induced from the other factor. Tensor symmetry gives the displayed right-central statement. Applied to the actual image and its opposite algebra, it supports Skolem-Noether without assuming an inner implementer.")))));

    private static Formula Statement()
    {
        Formula k = I("K"), a = I("A"), b = I("B");
        Formula tensor = App(Q("Algebra", "TensorProduct"), k, a, b);
        Formula p = App(I("IsSimpleRing"), tensor);
        p = Inst(App(I("IsSimpleRing"), a), p);
        p = Inst(App(Q("Algebra", "IsCentral"), k, b), p);
        p = Inst(App(I("IsSimpleRing"), b), p);
        return AlgebraInputs(p, true);
    }

    private static Formula I(string s) => F.Id(s);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(I(a)), Dot, Operatorname, Grp(I(b)));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
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
