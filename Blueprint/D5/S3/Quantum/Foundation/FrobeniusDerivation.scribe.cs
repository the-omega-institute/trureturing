using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FrobeniusDerivationDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula S(Formula x, Formula y) => C("S", x, y);
    private static Formula G(Formula x, Formula y) => C("inner", x, y);
    private static Formula Der(Formula x) => C("d", x);

    private static Formula Statement()
    {
        var space = V("V");
        var x = V("x"); var y = V("y"); var z = V("z");
        var comm = All("x", space, All("y", space, Eq(S(x,y), S(y,x))));
        var unit = All("x", space, Eq(S(V("e"),x),x));
        var frob = All("x", space, All("y", space, All("z", space,
            Eq(G(S(x,y),z),G(y,S(x,z))))));
        var derivation = All("x", space, All("y", space,
            Eq(Der(S(x,y)), Add(S(Der(x),y),S(x,Der(y))))));
        var conclusion = All("x", space, All("y", space,
            Eq(G(Der(x),y), Seq(Minus,G(x,Der(y))))));
        return All("V", C("Type"), Seq(
            OpenBracket,C("NormedAddCommGroup",space),CloseBracket,Sp,
            OpenBracket,C("InnerProductSpace",C("Real"),space),CloseBracket,Sp,
            OpenBracket,C("FiniteDimensional",C("Real"),space),CloseBracket,Sp,
            All("S",C("RealBilinearMap",space,space,space),
            All("e",space, Imp(And(comm,And(unit,frob)),
            All("d",C("RealLinearMap",space,space),Imp(derivation,conclusion)))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derivations preserve the positive pairing of a finite commutative unital Frobenius multiplication.",
        H("Derivations of positive Frobenius comparisons are skew-adjoint"), Blocks(
            Paragraph(Text("Let V be a finite-dimensional real inner-product space, e a unit, and S a commutative real bilinear multiplication satisfying the Frobenius identity. Every real linear derivation d of this same multiplication preserves its inner product infinitesimally. The statement also includes the zero space. Neither a normalized unit nor associativity, a Jordan identity, a Lie bracket or a selected basis is required.")),
            Describe.Lean(DescribeId.Create("derivation-skew-adjoint"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FrobeniusDerivation.derivation_skew_adjoint"),
                H("Every derivation is skew-adjoint"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write L_c(x)=S(c,x). First consider c for which L_c commutes with every L_x. The derivation law gives C=L_(dc)=[d,L_c]. Consequently [L_c,C]=0, and trace cyclicity gives Tr(C^2)=Tr([d,L_c]C)=Tr(d[L_c,C])=0. Frobenius invariance makes C self-adjoint. In a complete orthonormal basis the same trace is the sum of the squared norms of C applied to the basis vectors. Positivity therefore gives C=0, and evaluating at the original unit gives dc=0.")),
                    Paragraph(Text("For an arbitrary derivation d, the unit law gives de=0. Taking adjoints of [d,L_a]=L_(da) shows that H=d+d* commutes with all L_a. The original unit and commutativity then identify H=L_h with h=He=d*e. The preceding central-multiplier argument gives dh=0. Thus inner(h,h)=inner(e,dh)=0, so h=0 and H=0. This is exactly inner(dx,y)=-inner(x,dy) for all x,y.")),
                    Paragraph(Text("This supplies the generic derivation fact invoked in the original V96 section 8.1 and in the Q97 continuation's original-space estimates. For a label-linear assignment D, apply the theorem separately to d=D(a); nonzero activity of D is unnecessary for this conclusion. No assertion about alternation of B(a,b)=D(a)b, Jacobi, the first-slot unit D(e), or a quantitative curvature estimate follows from this theorem alone."))),
                DescribeRole.Theorem))));
}
