using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FiniteCompanionSquareDefectDocument : IScribeDocumentDefinition
{
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Domain(bool normal) => normal
        ? Call("normalDomainEquiv", I("J"), I("n"), I("v"))
        : Call("domainEquiv", I("n"), I("v"));
    private static DocumentBlock Result(string name, string id, string title, bool normal) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S1/Recurrence/FiniteCompanionSquareDefect." + name),
            H(title), StatementSource.FromAuthor(Disp(All(Equal(
                Call(normal ? "normalCodomainEquiv" : "codomainEquiv", I("J"), I("n"),
                    Call("squareDefect", I("J"), Call("succ", I("n")), I("v"))),
                Call("pair", Call(normal ? "headNormal" : "headResidual", I("J"),
                    Call("add", I("n"), Num(2)),
                    Call("head", Domain(normal))),
                    Call("tail", Domain(normal)))),
                B("A", I("AddCommGroupType")), B("J", Call("InvolutiveAddEnd", I("A"))),
                B("n", I("Nat")), B("v", Call("Row", I("A"), Call("add", I("n"), Num(2))))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(normal
                ? "The residue-dependent head column changes are (a+Jb,b), (a,b+Ja), "
                    + "(a,b+2a+Ja), and (a+b,b). The row change is identity except in residue two, "
                    + "where (r,s) goes to (r+Jr-s,r). Each has an explicit additive inverse. "
                    + "Their normal heads are (a,b), (2a,b), (3a+2Ja,b), and (a+Ja,b+Jb). "
                    + "The tail remains identity. These are two-sided operator equivalences, not conjugacy."
                : "Domain coordinates are ((v(0),v(1)),t) with t(j)=v(j+2)+v(j). "
                    + "Reconstruction uses v(j+2)=t(j)-v(j), over any additive commutative group. "
                    + "Split reconstruction into the homogeneous seeds and the zero-seed tail. "
                    + "The codomain subtracts the two actual squareDefect heads of that zero-seed tail. "
                    + "The homogeneous recurrence is a,b,-a,-b. Induction computes (sum,last) "
                    + "as (0,-b), (a,a), (a+b,b), or (b,-a), according to q modulo four. "
                    + "Under hJ, headResidual is (a+s+J(s-l),b+Js), where (s,l)=boundary(q,a,b)."))),
            DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-sided integral normal form of identity plus squared reset time.",
        H("The quarter-turn boundary recurrence"),
        Blocks(
            Paragraph(Text("A is any additive commutative group and J is an additive endomorphism. "
                + "Row(A,q) means Fin q -> A. Genuine time has head J(sum v) and successor v(j). "
                + "squareDefect J n is id+(time(J,n) composed with time(J,n)), on length n+1. "
                + "For the two-head coordinates write q=n+2, n>=0, and L=squareDefect J (n+1). "
                + "The raw elimination below needs no involution, invertibility, torsion freedom, "
                + "division, finite generation or field. The formal eliminate and normal_form statements "
                + "additionally require hJ: J(Ja)=a for every a; InvolutiveAddEnd includes that premise. "
                + "At length one time=J and the defect is id+(J composed with J); it is doubling under hJ.")),
            new DocumentBlock.Section(H("Raw elimination for an arbitrary additive head"), Blocks(
            Paragraph(Text("Let S(v)=sum over Fin q of v(i) and P(v)=sum over Fin(n+1) of v(j.castSucc). "
                + "The actual coordinates of L are (Lv)(0)=v(0)+J(J(S(v))+P(v)), "
                + "(Lv)(1)=v(1)+J(S(v)), and (Lv)(j+2)=v(j+2)+v(j) for every j in Fin n. "
                + "domainEquiv(n) sends v to ((a,b),t), with a=v(0), b=v(1) and "
                + "t(j)=v(j+2)+v(j). Its inverse is reconstruct(n,a,b,t): start with a,b and "
                + "set v(j+2)=t(j)-v(j). These are exact additive inverse coordinates, including "
                + "n=0, where the tail is empty and the carrier still has two coordinates.")),
            Paragraph(Text("Write H(u)=(u(0),u(1)) and U(y)(j)=y(j+2). The correction is "
                + "c(t)=H(L(reconstruct(n,0,0,t))); it uses the two actual defect heads. "
                + "codomainEquiv(J,n)(y)=(H(y)-c(U(y)),U(y)). Its inverse at ((r,s),t) "
                + "is Fin.cons(r+c(t)(first),Fin.cons(s+c(t)(second),t)). Thus the codomain "
                + "shear is independent of the free domain seeds and recovers every original row, "
                + "rather than discarding the suffix or replacing it by a quotient.")),
            Paragraph(Text("For h=reconstruct(n,a,b,0), define the raw boundary notation "
                + "B(J,n)(a,b)=H(Lh)=(a+J(J(S(h))+P(h)),b+J(S(h))). "
                + "Reconstruction splits as reconstruct(n,a,b,t)=h+reconstruct(n,0,0,t), "
                + "by the inverse and additivity of domainEquiv. Applying the additive L gives "
                + "head B(J,n)(a,b)+c(t) and tail t. The codomain subtracts exactly c(t), so "
                + "codomainEquiv(J,n)(Lv)=(B(J,n)(v(0),v(1)),(domainEquiv(n)(v))(tail)). "
                + "This raw identity is an application of the existing coordinate and additive facts "
                + "for every n>=0 and every additive J; B is notation for actual heads, not headResidual.")),
            Paragraph(Text("The homogeneous recurrence h is a,b,-a,-b, repeating without any assumption "
                + "on J. The existing homogeneous_boundary computation gives (S(h),last(h)) "
                + "equal to (0,-b), (a,a), (a+b,b), or (b,-a) in residues q=0,1,2,3 modulo four. "
                + "Since P(h)=S(h)-last(h), the arbitrary-J boundary is "
                + "(a+J(J(S(h))+S(h)-last(h)),b+J(S(h))). Under hJ, its first component "
                + "simplifies to a+S(h)+J(S(h)-last(h)), which is the existing headResidual. "
                + "At q=4m+3 the raw heads are (a+J(Jb+a+b),b+Jb); under hJ they become "
                + "((id+J)(a+b),(id+J)b). The integral seed shear (a,b)->(a+b,b) then "
                + "separates the two resonant blocks. The simplified formal statements retain hJ.")))),
            Result("eliminate", "square-companion-elimination", "Independent tail elimination", false),
            Result("normal_form", "square-companion-normal-form", "Complete period-four normal form", true),
            Paragraph(Text("The stride-two recurrence has two independent seeds, whereas the adjacent-sum "
                + "recurrence has one. Specializing J to the literal "
                + "swap on Int[C2] produces a new cyclic-five obstruction and a rank-two resonance. "
                + "On a torsion group, doubling or 3id+2J can have kernels; the integer classifications "
                + "therefore belong to the reset arithmetic specialization, not to this general theorem.")))));
}
