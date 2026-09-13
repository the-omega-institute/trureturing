using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class ToralReturnPrimeTwoCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Dynamics/ToralReturnPrimeTwoCriterion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A division-free intertwiner normal form gives a quadratic norm determinant and a sharp odd-modulus conjugacy criterion.",
        H("The exact prime-two observation boundary"),
        Blocks(
            Paragraph(Text("C_k and D_k are the original integer matrices of ToralReturnModuleSpectrum. "
                + "Their coefficients are mapped by the canonical integer ring homomorphism. "
                + "N(k,a,b)=[[a,b],[2k((k+1)b-a),2(a-kb)]]. "
                + "The first two statements hold over every commutative ring R, including characteristic two.")),
            Describe.Lean(DescribeId.Create("complete-intertwiner-normal-form"),
                DeclarationHandle.Create(Prefix + "intertwiner_normal_form"),
                H("All intertwiners are determined by their top row"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("R"), Comma, Sp, Call("CommRing", F.Id("R")), Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("k"), Colon, Sp, Call("Nat"), Comma, Sp,
                    Forall, Sp, F.Id("U"), Colon, Sp, Call("Matrix2", F.Id("R")), Comma, Sp,
                    Call("Intertwines", F.Id("C"), F.Id("U"), F.Id("D")), Sp, Seq(Operatorname, Grp(F.Id("iff"))), Sp,
                    F.Id("U"), Sp, Eq, Sp,
                    Call("N", F.Id("k"), Call("entry", F.Id("U"), D(0), D(0)),
                        Call("entry", F.Id("U"), D(0), D(1)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The top two intertwining equations solve for the bottom entries without "
                    + "dividing by two or by k. Substitution into all four equations proves the converse. "
                    + "Intertwines(C,U,D) denotes exactly C U=U D for the transported original matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("intertwiner-quadratic-norm"),
                DeclarationHandle.Create(Prefix + "intertwiner_quadratic_norm"),
                H("The exact determinant, beyond its evenness"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("R"), Comma, Sp, Call("CommRing", F.Id("R")), Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("k"), Colon, Sp, Call("Nat"), Comma, Sp,
                    Forall, Sp, F.Id("U"), Colon, Sp, Call("Matrix2", F.Id("R")), Comma, Sp,
                    Call("Intertwines", F.Id("C"), F.Id("U"), F.Id("D")), Sp, Rightarrow, Sp,
                    Call("det", F.Id("U")), Sp, Eq, Sp,
                    Call("mul", D(2), Call("sub", Call("square", Call("entry", F.Id("U"), D(0), D(0))),
                        Call("mul", F.Id("k"), Call("add", F.Id("k"), D(1)),
                            Call("square", Call("entry", F.Id("U"), D(0), D(1))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Writing a=U_00,b=U_01, the determinant is 2(a^2-k(k+1)b^2). "
                    + "This is a polynomial identity valid in every commutative ring. Over the integers "
                    + "it makes the Pell-type norm and the index-two obstruction explicit; "
                    + "it does not identify the variable quadratic field with the golden field."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("modular-conjugacy-iff-odd"),
                DeclarationHandle.Create(Prefix + "modular_conjugacy_iff_odd"),
                H("Conjugacy holds exactly at odd moduli"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k,m"), Colon, Sp, Call("Nat"), Comma, Sp,
                    Call("ModularConjugacy", F.Id("k"), F.Id("m")), Sp, Seq(Operatorname, Grp(F.Id("iff"))), Sp,
                    Call("Odd", F.Id("m"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ModularConjugacy is the existence of actual matrices P,Q over ZMod(m) "
                    + "with PQ=QP=I and C_k P=P D_k. If m=2r+1, set u=-r modulo m, so 2u=1. "
                    + "The explicit matrices P=[[1,0],[-2k,2]] and Q=[[1,0],[k,u]] satisfy all three equations. "
                    + "If 2 divides m, reduce the determinant equation through the actual ring homomorphism "
                    + "ZMod(m) to ZMod(2). The norm formula turns an alleged invertibility equation into 0=1. "
                    + "The theorem includes m=0 and m=1. This exact local criterion concerns only the stated "
                    + "family; no general profinite-rigidity or mapping-class CSP conclusion is asserted."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
