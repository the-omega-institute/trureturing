using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class CurvatureAffineRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local affine rigidity of a convex function forces full support of its right-derivative Stieltjes curvature unless the function is globally affine.",
        H("Affine rigidity and curvature support"), Blocks(
            Paragraph(Text("Let f be a real convex function on (0,infinity). Affine rigidity means that for every real a,b,alpha,beta with 0<a<b, equality f(x)=alpha*x+beta for all a<x<b implies that same equality for every x>0. Nonaffineness means there are no real alpha,beta representing f on the entire positive ray. These are the complete hypotheses of the theorem below. Curvature is the existing actual right-derivative Stieltjes measure, and support is taken in the subtype Positive=(0,infinity).")),
            Describe.Lean(DescribeId.Create("curvature-affine-rigidity-full-support"),
                DeclarationHandle.Create("D5/S3/Analytic/Convexity/CurvatureAffineRigidity.full_support_of_affine_rigidity"),
                H("Full support from local affine rigidity"),
                StatementSource.FromAuthor(Disp(All("f", Seq(Real(), To, Real()),
                    All("hf", Call("ConvexOn", Real(), Call("Ioi", D(0)), Id("f")),
                        Imp(Call("AffineRigidity", Id("f")), Imp(Call("Nonaffine", Id("f")),
                            new Formula.Relation(Call("support", Call("curvature", Id("hf"))),
                                FormulaRelationOperator.Equal, Call("univPositive")))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The theorem quantifies over every real function f, its scalar convexity proof hf, the full local-to-global rigidity property stated above, and global nonaffineness. If the right derivatives at two positive endpoints were equal, the convex secant slope is squeezed between them. This gives an affine formula throughout their open interval. Rigidity would then contradict nonaffineness. Thus the right derivative is strictly increasing. The exact curvature_Ioc identity gives positive mass to every positive half-open interval. Every neighborhood in Positive contains such an interval, which proves the displayed support equality.")),
                    Paragraph(Text("This scalar bridge assumes no curvature support, strict convexity, smoothness, atomlessness, finite total mass or endpoint regularity. OperatorConvexCurvature supplies its affine rigidity property by actual two-dimensional operator-convex functional calculus. The bridge is a classical necessary supplier; it does not settle the Hiai–Mosonyi–Tomamichel divergence equality classification."))),
                DescribeRole.Theorem)
        )));

    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, Open, body, Close);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
