using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra.TwoSidedIdeal;

internal sealed class TwoSidedIdealOperationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ideal extension and contraction in the tensor-simplicity argument.", H("Ideal extension and contraction in the tensor-simplicity argument."), Blocks(
            Paragraph(Ref("D5/S3/FiniteGroups/GroupAlgebra/TwoSidedIdeal/Operations")),
            Paragraph(Text("The statement and proof are reused from AxiomMath/Stacks contributors, revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache-2.0. The source retains the exact upstream paths and SHA-256 hashes. This is classical algebra used for the actual finite-group representation image; no new algebra theorem is claimed.")),
            Paragraph(Math(Disp(Statement()))),
            Paragraph(Text("For a function carrying a nonunital ring-homomorphism structure, extension of a two-sided ideal is left adjoint to contraction. The formula retains both nonassociative ring assumptions and the function-class hypotheses. The additional zero, kernel and surjective-image identities in the source are the ideal calculations used by the tensor-simplicity proof.")))));

    private static Formula Statement()
    {
        Formula r = I("R"), s = I("S"), f = I("f"), ii = I("I"), j = I("J");
        Formula p = IffTo(LeqTo(App(Q("TwoSidedIdeal", "map"), ii, f), j),
            LeqTo(ii, App(Q("TwoSidedIdeal", "comap"), j, f)));
        p = All("I", App(I("TwoSidedIdeal"), r), All("J", App(I("TwoSidedIdeal"), s), p));
        p = All("f", I("F"), p);
        p = Inst(App(I("NonUnitalRingHomClass"), I("F"), r, s), p);
        p = Inst(App(I("FunLike"), I("F"), r, s), p);
        p = Inst(App(I("NonUnitalNonAssocRing"), s), p);
        p = Inst(App(I("NonUnitalNonAssocRing"), r), p);
        return All("R", Ty(), All("S", Ty(), All("F", Ty(), p)));
    }

    private static Formula I(string s) => F.Id(s);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(I(a)), Dot, Operatorname, Grp(I(b)));
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula LeqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula IffTo(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Inst(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
    private static Formula Ty() => Seq(I("Type"), Star);

}
