using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FunctionField;

internal sealed class CarlitzFiveCharacteristicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constructed integer in the closed-five-orbit ideal confines every prime characteristic.",
        H("A Global Characteristic Obstruction for Carlitz Five-Orbits"),
        Blocks(
            Paragraph(Text("The residual is the actual nested Carlitz residual already defined "
                + "in CarlitzFiveOrbit. A ring endomorphism sigma is iterated by composition. "
                + "The theorem keeps every field, every prime characteristic and every "
                + "closed five-orbit in its quantified domain.")),
            Describe.Lean(
                DescribeId.Create("carlitz-five-global-characteristic"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FunctionField/CarlitzFiveCharacteristic.result"),
                H("The finite characteristic support forced by all five equations"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every field K and natural prime p with CharP K p, "
                        + "every ring endomorphism sigma of K, and every theta in K, assume "
                        + "sigma^5(theta)=theta and the residual at sigma^i(theta)-theta, "
                        + "i=1,2,3,4, is zero. Then p divides "
                        + "8*25*19*263*519555805809266011. Primality of the last explicit "
                        + "factor is not a premise or conclusion of this declaration.")),
                    Paragraph(Text("Applying sigma supplies the other four cyclic-origin "
                        + "residual equations. An explicitly authored degree-ten integer "
                        + "polynomial with 508 terms has a cyclic weighted residual sum "
                        + "equal to 4673196650932024062540600. The Lean proof checks the "
                        + "integer identity by ring normalization. Its factorization has "
                        + "an extra factor nine, which is removed by a second 340-term "
                        + "cyclic certificate equal to one in characteristic three.")),
                    Paragraph(Text("The coefficients in both certificates are on the live "
                        + "proof path. Neither a Groebner-basis result, a list of tested "
                        + "characteristics, nor the desired characteristic support is "
                        + "assumed. The conclusion is a global exclusion statement for "
                        + "the literal orbit equations, not an extrapolation from a scan.")),
                    Paragraph(Text("The unified Wieferich dossier gives additional ordinary "
                        + "proofs of the two newly constructed characteristic families and "
                        + "their exact extension-degree classes. Those are not additional "
                        + "conclusions silently attached to this declaration. The integer "
                        + "Wall-Sun-Sun existence problem remains a separate unresolved "
                        + "subproblem within the same lifting-and-elimination family."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), xs);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Iter(int n)
    {
        Formula x = V("theta");
        for (var i = 0; i < n; ++i) { x = C("sigma", x); }
        return x;
    }
    private static Formula Statement()
    {
        var root = Eqn(C("residual", Sub(Iter(1),V("theta")),
            Sub(Iter(2),V("theta")), Sub(Iter(3),V("theta")),
            Sub(Iter(4),V("theta"))), D(0));
        var orbit = And(Eqn(Iter(5),V("theta")),root);
        var support = Mul(Mul(Mul(Mul(D(8),D(2,5)),D(1,9)),D(2,6,3)),
            D(5,1,9,5,5,5,8,0,5,8,0,9,2,6,6,0,1,1));
        var conclusion = new Formula.Relation(V("p"),FormulaRelationOperator.Divides,support);
        var characteristic = And(C("CharP",V("K"),V("p")),C("Nat.Prime",V("p")));
        return Disp(All("K",C("Type"),Implies(C("Field",V("K")),
            All("p",Seq(Mathbb,Grp(V("N"))),Implies(characteristic,
                All("sigma",C("RingHom",V("K"),V("K")),
                    All("theta",V("K"),Implies(orbit,conclusion))))))));
    }
}
