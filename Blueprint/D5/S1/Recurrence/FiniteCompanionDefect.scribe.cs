using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FiniteCompanionDefectDocument : IScribeDocumentDefinition
{
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constructive elimination of a finite additive reset companion.",
        H("Finite companion defect"),
        Blocks(
            Paragraph(Text("Let A be any additive commutative group, J an additive endomorphism, "
                + "and n a natural number. The carrier is Fin(n+1) -> A, so length one is included. "
                + "No involution, field, torsion-free or finite-generation hypothesis is imposed. "
                + "The domain coordinates D(v) are (v(0), t), where t(j)=v(j+1)+v(j). "
                + "Their inverse is the integral recurrence v(0)=a and v(j+1)=t(j)-v(j). "
                + "Put R(t)=sum over j in Fin n with Odd(n-j) of t(j). "
                + "The independent codomain coordinates C(y) are (y(0)-J(R(tail(y))), tail(y)). "
                + "Their inverse adds J(R(t)) back to the head. Both changes are additive equivalences.")),
            Describe.Lean(DescribeId.Create("finite-companion-additive-elimination"),
                DeclarationHandle.Create("D5/S1/Recurrence/FiniteCompanionDefect.eliminate"),
                H("Separate domain and codomain elimination"),
                StatementSource.FromAuthor(Disp(All(
                    Equal(
                        Call("C", I("J"), I("n"), Call("L", I("J"), I("n"), I("v"))),
                        Call("pair",
                            Call("add", Call("head", Call("D", I("n"), I("v"))),
                                Call("apply", I("J"), Call("if", Call("Odd", Call("succ", I("n"))),
                                    Call("head", Call("D", I("n"), I("v"))), Num(0)))),
                            Call("tail", Call("D", I("n"), I("v"))))),
                    B("A", I("AddCommGroupType")), B("J", Call("AddEnd", I("A"))),
                    B("n", I("Nat")), B("v", Call("Row", I("A"), Call("succ", I("n"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Row(A,m) means Fin m -> A; AddEnd(A) means A ->+ A. "
                    + "AddCommGroupType displays the Lean type and its additive commutative group instance. "
                    + "D=domainEquiv and C=codomainEquiv; head and tail are product projections. "
                    + "L=companion has head v(0)+J(sum v) and adjacent-sum tails. "
                    + "The finite sum identity sum v = (if Odd(n+1) then v(0) else 0) + R(t) "
                    + "is proved by induction using cancellation of each adjacent pair. "
                    + "Thus C L D inverse is identity on the tail, and its head is a+J(a) "
                    + "at odd length or a at even length. C and D are separately defined codomain and domain equivalences: this is "
                    + "equivalence of an additive operator's domain and codomain, with no conjugacy claim. "
                    + "For A=Int, J=id and length one the remaining map is multiplication by two. "
                    + "Involutivity of J alone therefore does not imply a torsion-free cokernel. "
                    + "The original two-coefficient integer reset operator uses this same elimination, "
                    + "with J given by right multiplication by the nonidentity sign."))),
                DescribeRole.Theorem))));
}
