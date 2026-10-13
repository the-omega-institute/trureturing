using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleEnvelopesDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FourCycleEnvelopes.cosine_mixed_comparison";
    private static readonly LibraryNoteRef Zhao =
        LibraryNoteRef.Create("D5/L/zhao2026cfmpincidence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact six-variable formula, mixed-coordinate monotonicity and a shared-center inverse-angle application.",
        H("The shared mixed-coordinate comparison"),
        Blocks(
            Paragraph(Text("All variables below are real numbers. Icc(a,b) denotes the closed "
                + "interval [a,b]. In the local edge order (12,13,14,34,24,23), the inputs "
                + "(x,y,z,o,v,w) keep all six coordinates independent. Coordinates x and o "
                + "are opposite.")),
            Paragraph(Text("Define rad(x,y,z)=2xyz+x^2+y^2+z^2-1 and "
                + "P(x,y,z,o,v,w)=yz+vw+xyv+xzw-(x^2-1)o. The function cosine "
                + "is P divided first by sqrt(rad(x,y,w)) and then by sqrt(rad(x,z,v)). "
                + "This is the exact six-variable formula used by the cited source. "
                + "Both radicands are proved positive on the box.")),
            Paragraph(Text("The inverse-angle application uses a different parameter domain from the comparison theorem below. Its six angles have the original order (12,13,14,34,24,23)=(theta,a,b,g,c,d). Set z=cos(theta), D(theta,alpha,beta)=rad(z,cos(alpha),cos(beta)) and I=cosine(z,cos(a),cos(d),cos(g),cos(c),cos(b)). The permutation of the third and sixth inputs retains the original endpoint triples. The comparison theorem on [1,2] is not applied to these cosine inputs.")),
            Paragraph(Text("Assume theta,a,b,c,d>0, theta+a+b<pi and theta+c+d<pi; g may be any real number. Both D(theta,a,b) and D(theta,c,d) are positive. Expanding the existing numerator and using sin(theta)^2=1-z^2 writes I as [sin(theta)^2 cos(g)+cos(a)cos(d)+cos(b)cos(c)+z(cos(a)cos(c)+cos(b)cos(d))]/sqrt(D(theta,a,b)D(theta,c,d)). The same scalar expression occurs in Frigerio-Moraschini, On volumes of truncated tetrahedra with constrained edge lengths, arXiv:1801.05326v3, Section 1.1, formulas (1), (3) and (4), https://arxiv.org/html/1801.05326v3.")),
            Paragraph(Text("For one endpoint split (alpha,beta), put k=cos(alpha+beta), h=cos(alpha-beta), A=z+k, C=cos(alpha)+cos(beta) and E=cos(alpha)-cos(beta). Strict decrease of cosine on [0,pi] gives A>0 from alpha+beta<pi-theta. Sine positivity gives h-k=2sin(alpha)sin(beta)>0, while -1<z<1 and -1<=k<=1. Cosine addition and subtraction and sin^2+cos^2=1 give D=A(z+h), C^2=(1+k)(1+h) and E^2=(1-k)(1-h). Consequently D-A^2=A(h-k)>0, so sqrt(D)>A and D>0.")),
            Paragraph(Text("The squared coordinate gaps factor as (1+k)^2D-A^2C^2=A(1+k)(1-z)(h-k)>=0 and (1-k)^2D-A^2E^2=A(1-k)(1+z)(h-k)>=0. All factors have the indicated signs. Comparing nonnegative squares therefore gives A|C|<=(1+k)sqrt(D) and A|E|<=(1-k)sqrt(D). These estimates use the same z at both endpoints; they do not optimize unrelated endpoint states.")),
            Paragraph(Text("Apply the estimates to (a,b) and (d,c). Write k1=cos(a+b), k2=cos(c+d), A=z+k1, B=z+k2, S=sin(theta)^2 and R=sqrt(D(theta,a,b)D(theta,c,d)). Then R>AB>0 and S>0. Take C1=cos(a)+cos(b), C2=cos(d)+cos(c), E1=cos(a)-cos(b) and E2=cos(d)-cos(c). The numerator N is S cos(g)+(1+z)C1C2/2+(1-z)E1E2/2. In particular, the sign of E2 is fixed by the original six-slot pairing.")),
            Paragraph(Text("Multiplication of the two endpoint bounds and use of the nonnegative weights (1+z)/2 and (1-z)/2 gives AB[N-S cos(g)]<=R[1+k1 k2+z(k1+k2)]=R(AB+S). Since cos(g)<=1 and R>AB with S>0, AB N<=AB S+R(AB+S)<R(AB+2S). Dividing by positive AB and R yields the strict shared-center bound I<1+2sin(theta)^2/[(cos(theta)+cos(a+b))(cos(theta)+cos(c+d))]. This includes obtuse theta and arbitrary g; it assumes no equality of endpoint angles.")),
            Paragraph(Text("The full genuine-angle domain additionally imposes g>0, a+d+g<pi and b+c+g<pi, so it is contained in the scalar domain just used. The trigonometric, product-order and square-root facts combine to give this application of the existing expression. It is distinct from the mixed-coordinate comparison theorem below. Identification of I with cosh of an actual native edge length remains a separate geometric requirement; neither a tetrahedron from angles nor common global lengths, complete face gluing or same-manifold realization follows from this scalar estimate.")),
            Describe.Lean(
                DescribeId.Create("hyperideal-mixed-coordinate-comparison"),
                DeclarationHandle.Create(Declaration),
                H("Increasing neighbours and decreasing the opposite coordinate"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromLiterature(Zhao),
                Blocks(
                    Paragraph(Text("All eleven variables lie in [1,2]. Increasing the four "
                        + "neighbouring coordinates and decreasing the opposite coordinate cannot "
                        + "decrease the actual cosine. The proof differentiates the original "
                        + "square-root expression and derives the nonnegative coupled numerator "
                        + "(x^2-1)(xow+xv+yo+yvw+z(1-w^2)). It retains endpoint continuity, "
                        + "positive denominators and the two actual tetrahedral symmetries.")),
                    Paragraph(Text("Endpoint envelopes used by later incidence arguments are "
                        + "obtained there by direct specialization and normalization. They are "
                        + "not separate formal declarations. Geometric identification with a "
                        + "tetrahedron, face-pairing topology and the global co-volume existence "
                        + "argument remain outside this analytic theorem."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        string[] names = ["x", "y", "z", "o", "v", "w", "Y", "Z", "O", "V", "W"];
        var a = names.Select(F.Id).ToArray();
        var intervals = a.Select(t => In(t, F.D(1), F.D(2))).ToArray();
        Formula[] orders = [Le(a[1], a[6]), Le(a[2], a[7]), Le(a[8], a[3]),
            Le(a[4], a[9]), Le(a[5], a[10])];
        return ForAll(names, Implies(And([.. intervals, .. orders]),
            Le(Call("cosine", a[0], a[1], a[2], a[3], a[4], a[5]),
               Call("cosine", a[0], a[6], a[7], a[8], a[9], a[10]))));
    }

    private static Formula ForAll(string[] names, Formula body)
    {
        var real = new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
        Formula.BoundVariable[] binders = names.Select(name =>
            new Formula.BoundVariable(FormulaIdentifier.Create(name), real)).ToArray();
        return new Formula.BindMany(FormulaQuantifier.ForAll, [.. binders], body);
    }

    private static Formula And(params Formula[] clauses)
    {
        if (clauses.Length == 0) throw new ArgumentException("Empty conjunction.");
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula In(Formula value, Formula lower, Formula upper) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, Call("Icc", lower, upper));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
