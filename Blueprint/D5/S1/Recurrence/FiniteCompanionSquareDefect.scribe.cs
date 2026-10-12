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
                    + "The raw headResidual is (a+s+J(s-l),b+Js), where (s,l)=boundary(q,a,b)."))),
            DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-sided integral normal form of identity plus squared reset time.",
        H("The quarter-turn boundary recurrence"),
        Blocks(
            Paragraph(Text("A is any additive commutative group; J is additive and J(Ja)=a for every a. "
                + "Row(A,q) means Fin q -> A. Genuine time has head J(sum v) and successor v(j). "
                + "squareDefect J n is id+(time(J,n) composed with time(J,n)), on length n+1. "
                + "It is not the square of id+time. InvolutiveAddEnd records both "
                + "the additive map and its universally quantified involution premise. "
                + "All formulas use q=n+2. At length one, time=J, so the defect is exactly doubling. "
                + "The proof does not require torsion freedom, division, finite generation or a field.")),
            Result("eliminate", "square-companion-elimination", "Independent tail elimination", false),
            Result("normal_form", "square-companion-normal-form", "Complete period-four normal form", true),
            Paragraph(Text("The stride-two recurrence has two independent seeds, whereas the adjacent-sum "
                + "recurrence has one. Specializing J to the literal "
                + "swap on Int[C2] produces a new cyclic-five obstruction and a rank-two resonance. "
                + "On a torsion group, doubling or 3id+2J can have kernels; the integer classifications "
                + "therefore belong to the reset arithmetic specialization, not to this general theorem.")))));
}
