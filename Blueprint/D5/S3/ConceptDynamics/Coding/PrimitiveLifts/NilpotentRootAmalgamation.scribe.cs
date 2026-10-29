using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class NilpotentRootAmalgamationDocument : IScribeDocumentDefinition
{
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. v], f);
    private static Formula And(Formula a, Formula b) => Seq(Open,a,Sp,Land,Sp,b,Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open,a,Sp,Implies,Sp,b,Close);
    private static Formula Iff(Formula a, Formula b) => Seq(Open,a,Sp,F.Iff,Sp,b,Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Root(Formula z) => And(Equal(I("x"),Pow(z,I("n"))),Equal(I("y"),Pow(z,I("m"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nilpotency makes equal coprime powers arise from exactly one common root, without excluding torsion or infinite groups.",
        H("Unique coprime root amalgamation in nilpotent groups"),Blocks(
        Describe.Lean(DescribeId.Create("nilpotent-coprime-root-amalgamation"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PrimitiveLifts/NilpotentRootAmalgamation.pow_eq_pow_iff_exists_unique"),
            H("Exact unique common root"),StatementSource.FromAuthor(Disp(
                Q(Seq(OpenBracket,Call("Group",I("G")),CloseBracket,
                    OpenBracket,Call("IsNilpotent",I("G")),CloseBracket,
                    Q(Imp(Call("Coprime",I("m"),I("n")),
                        Iff(Equal(Pow(I("x"),I("m")),Pow(I("y"),I("n"))),
                            Ex(And(Root(I("z")),Q(Imp(Root(I("w")),Equal(I("w"),I("z"))),
                                B("w",I("G")))),B("z",I("G"))))),
                        B("x",I("G")),B("y",I("G")),B("m",I("Nat")),B("n",I("Nat")))),
                    B("G",I("Type"))))),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("For every group G with Group.IsNilpotent G, every x,y:G and every coprime m,n:Nat, x^m=y^n holds if and only if there exists exactly one z:G satisfying x=z^n and y=z^m. The group may be infinite, noncommutative and have torsion. If either exponent is zero, coprimality forces (m,n)=(0,1) or (1,0), and the equations respectively give y=1 with z=x, or x=1 with z=y.")),
                Paragraph(Text("First, central-quotient induction proves that Commute(x^m,y) and Commute(x,y^n) force Commute(x,y). The quotient induction makes the commutator central. Its mth and nth powers then equal the two trivial power commutators, and coprimality kills it. Equal powers supply precisely these commuting hypotheses. This adapts the established central-quotient argument in Mathlib's Group.IsNilpotent.commute_of_orderOf_coprime; equality of coprime powers does not imply that the element orders are coprime.")),
                Paragraph(Text("Choose integers A=Nat.gcdA m n and B=Nat.gcdB m n, so m*A+n*B=1. Since x and y commute, z=x^B*y^A has the required powers. For every candidate w the same identity reconstructs w=(w^n)^B*(w^m)^A=x^B*y^A, proving uniqueness. This is uniqueness from the two specified powers together; it makes no assertion that an individual power map is injective. For example the quaternion group has distinct elements with equal squares. The converse only uses the commutation of powers of one element and holds in every group.")),
                Paragraph(Text("The reused inputs are the pinned Mathlib nilpotent_center_quotient_ind, commutatorElement_pow_left/right, pow_eq_one_iff_of_coprime and the integer Bezout identity Nat.gcd_eq_gcd_ab. Mathlib's similarly named Commute.pow_eq_pow_iff_of_coprime is stated for GroupWithZero and is not applied to an ordinary group. These are mature commutator and Bezout methods; their combination here is a repository derivation, with no claim of literature priority."))),DescribeRole.Theorem),
        Paragraph(Text("For root compatibility in signed return charts, this identifies a structural setting in which prescribed coprime roots amalgamate. In particular, a homomorphism from the coprime torus-knot presentation with generators x,y and relation x^m=y^n into a nilpotent group has cyclic two-generator image, because both images are powers of z and z is their integer word. Separate roots in an arbitrary nonnilpotent group need not have this compatibility. This is an interpretation of the theorem, not an additional formal declaration."))
        )));
}
