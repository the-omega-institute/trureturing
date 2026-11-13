using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class NiceConeFacesDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static DocumentBlock Def(string name, string title, StatementSource statement, string text) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create("D5/S3/Quantum/Foundation/NiceConeFaces." + name),
            H(title), statement, AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        Formula r = Seq(Mathbb, Grp(V("R"))), space = V("V"), cone = V("C"), face = V("F"), a = V("a"), x = V("x");
        Formula dual = C("LinearMap", r, space, r);
        Formula pos = All("x", space, Imp(In(x, cone), new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, C("apply", a, x))));
        Formula section = new Formula.SetBuilder(x, x, Seq(cone, Sp, Land, Sp, Eq(C("apply", a, x), D(0))));
        Formula body = All("C", C("PointedCone", r, space), Imp(C("IsClosed", cone), Imp(C("Nice", cone),
            All("F", C("Face", cone), Ex("a", dual, And(pos, Eq(face, section)))))));
        Formula statement = All("V", V("Type"), Seq(
            OpenBracket, C("NormedAddCommGroup", space), CloseBracket, Sp,
            OpenBracket, C("NormedSpace", r, space), CloseBracket, Sp,
            OpenBracket, C("FiniteDimensional", r, space), CloseBracket, Sp, body));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Facial dual completeness exposes every original face in the ambient finite-dimensional real space.",
            H("Nice cones and exact exposure of all original faces"), Blocks(
                Def("ambientDual", "The original ambient algebraic dual cone", StatementSource.WithoutFormula(),
                    "For a subset s of V, ambientDual(s) is the cone of all original real-linear a:V->R with a(x)>=0 for every x in s. Both dual cones below live in the same V*, including when the face has proper linear span."),
                Def("Nice", "Facial dual completeness", StatementSource.WithoutFormula(),
                    "For every original E:C.Face, ambientDual(E) equals the Minkowski sum of ambientDual(C) and the annihilator of span(E) in V*. The sum is a set sum, not a separately chosen restriction dual or an assumed exposing functional."),
                Describe.Lean(DescribeId.Create("every-face-exposed"),
                    DeclarationHandle.Create("D5/S3/Quantum/Foundation/NiceConeFaces.every_face_exposed"),
                    H("Every original cone face is an exact support-zero section"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("For every finite-dimensional real normed V, every closed PointedCone C, and every original face F of C, facial dual completeness gives a real-linear a nonnegative on C such that F={x in C | a(x)=0}. PointedCone means a cone containing zero; salience is not assumed. The quantifiers include subspace cones, their lineality face, zero-dimensional V and the whole face. The whole face permits a=0. Empty convex-set faces are outside the native cone-face type.")),
                        Paragraph(Text("Choose a nonnegative a annihilating F whose support-zero section has least span dimension. Let E be that section. If F is proper in E, restrict both cones to span(E), where E generates. The original ExclusionBallFaces.proper_cone_face_support provides a functional nonzero on this relative ambient space, positive on E and zero on F. Extend it linearly to V. The nice identity at this same original E splits the extension into b positive on C and a term annihilating span(E). Thus b agrees with the relative support on E and is nonzero somewhere in E. The positive functional a+b still vanishes on F, while its zero section has strictly smaller span dimension, a contradiction. This proves equality with F rather than mere containment.")),
                        Paragraph(Text("This is the nice-to-facially-exposed consequence in the existing IX119.12 chain. The mature attribution is Lourenco, Roshchina and Saunderson, arXiv:2011.07745v2, Proposition 2.3, and Pataki, arXiv:1202.4043v4, Theorem 3(1). No literature originality is claimed. It proves neither the other arrows in that chain nor all of Corollary 119.3. It supplies no unit-preserving projection, uniform error-bound constant, moving-face regularity or quantum realization. In the maximizing convention of IsExposed the corresponding exposing functional is -a."))),
                    DescribeRole.Theorem))));
    }
}
