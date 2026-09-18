using System;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FourCycleEnvelopesDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/FourCycleEnvelopes.fourcycle_envelopes";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform real angle envelopes on the three boundary faces of a hyper-ideal four-cycle box.",
        H("Whole-face hyper-ideal angle envelopes"),
        Blocks(
            Paragraph(Text("All variables below are real numbers. Icc(a,b) denotes the closed "
                + "interval [a,b]. In the local edge order (12,13,14,34,24,23), the inputs "
                + "(x,y,z,o,v,w) keep all six coordinates independent. The four-cycle occupies "
                + "coordinates x,y,o,v. Coordinates x and o are opposite.")),
            Paragraph(Text("Define rad(x,y,z)=2xyz+x^2+y^2+z^2-1 and "
                + "P(x,y,z,o,v,w)=yz+vw+xyv+xzw-(x^2-1)o. The function cosine "
                + "is P divided first by sqrt(rad(x,y,w)) and then by sqrt(rad(x,z,v)). "
                + "This is the actual formula in Zhao, arXiv:2601.15174v2, Lemma 2.2. "
                + "Both radicands are proved positive on the box. No assertion about an "
                + "abstract angle with assumed bounds is substituted for this formula.")),
            Describe.Lean(
                DescribeId.Create("hyperideal-mixed-coordinate-comparison"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/FourCycleEnvelopes.cosine_mixed_comparison"),
                H("The shared mixed-coordinate comparison"),
                StatementSource.FromAuthor(F.Disp(ComparisonStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All eleven variables lie in [1,2]. Increasing the four "
                    + "neighbouring coordinates and decreasing the opposite coordinate cannot "
                    + "decrease the actual cosine. The proof differentiates the original "
                    + "square-root expression and derives the nonnegative coupled numerator "
                    + "(x^2-1)(xow+xv+yo+yvw+z(1-w^2)). It retains endpoint continuity, "
                    + "positive denominators and the two actual tetrahedral symmetries. This "
                    + "is the former local comparison proof exposed at the same source owner; "
                    + "the original envelope theorem now consumes it without copying the derivative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fourcycle-whole-face-envelopes"),
                DeclarationHandle.Create(Declaration),
                H("The cube envelope and the three four-cycle face bounds"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Holding x,z,o,v,w in [1,2], differentiate with respect to y. "
                        + "After multiplication by positive denominators, the derivative numerator "
                        + "is (x^2-1)Q, where Q=xow+xv+yo+yvw+z(1-w^2). "
                        + "The first four terms are bounded below by w,1,1,w. The final term "
                        + "is at least 2(1-w^2), so Q is at least 2(2-w)(w+1), which is nonnegative. "
                        + "The proof constructs the derivative through the pinned square-root and "
                        + "quotient calculus and applies the mean-value monotonicity theorem on "
                        + "the closed interval, including endpoint continuity.")),
                    Paragraph(Text("Two verified symmetries give the other three adjacent-coordinate "
                        + "comparisons. Dependence on o is affine decreasing because x^2-1 is "
                        + "nonnegative. These comparisons are composed without identifying any "
                        + "distinct global edges. Endpoint evaluation then gives the whole cube "
                        + "envelope and the three stated rational bounds.")),
                    Paragraph(Text("The three rational bounds occur respectively at "
                        + "(5/4,5/4,1,2,5/4,1), (2,2,8/5,5/4,2,8/5), and "
                        + "(8/5,2,2,1,2,2). The quantified theorem covers every real point "
                        + "on the corresponding faces, not a finite grid or just those corners.")),
                    Paragraph(Text("This declaration supplies the analytic envelope used in "
                        + "CFMP_GEOMETRIC_REALIZATION.md Section 16. Geometric identification "
                        + "with a tetrahedron, face-pairing topology, strict trigonometric "
                        + "thresholds, and the global co-volume existence argument are outside "
                        + "this declaration. It does not claim the complete CFMP conjecture."))),
                DescribeRole.Theorem))));

    private static Formula ComparisonStatement()
    {
        string[] names=["x","y","z","o","v","w","Y","Z","O","V","W"];
        var a=names.Select(F.Id).ToArray();
        var intervals=a.Select(t=>In(t,F.D(1),F.D(2))).ToArray();
        Formula[] orders=[Le(a[1],a[6]),Le(a[2],a[7]),Le(a[8],a[3]),
            Le(a[4],a[9]),Le(a[5],a[10])];
        return ForAll(names,Implies(And([..intervals,..orders]),
            Le(Call("cosine",a[0],a[1],a[2],a[3],a[4],a[5]),
               Call("cosine",a[0],a[6],a[7],a[8],a[9],a[10]))));
    }

    private static Formula Statement()
    {
        var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z");
        var o = F.Id("o"); var v = F.Id("v"); var w = F.Id("w");
        var one = F.D(1); var two = F.D(2);
        var a = Rat(5,4); var b = Rat(8,5);
        var value = Call("cosine", x,y,z,o,v,w);
        var lower = F.Seq(F.Frac,
            F.Grp(two,F.Open,two,F.Minus,x,F.Close), F.Grp(x,F.Plus,one));
        var upper = F.Seq(F.Frac,F.Grp(F.D(9),F.Minus,x),F.Grp(F.D(7),F.Plus,x));
        var cube = ForAll(["x","y","z","o","v","w"],
            Implies(And(In(x,one,two),In(y,one,two),In(z,one,two),
                In(o,one,two),In(v,one,two),In(w,one,two)),
                And(Le(lower,value),Le(value,upper))));
        var face = And(In(y,a,two),In(z,one,b),In(o,a,two),In(v,a,two),In(w,one,b));
        var low = ForAll(["y","z","o","v","w"],
            Implies(face,Le(Rat(293,400),Call("cosine",a,y,z,o,v,w))));
        var high = ForAll(["y","z","o","v","w"],
            Implies(face,Le(Call("cosine",two,y,z,o,v,w),Rat(1577,2236))));
        var other = ForAll(["y","z","o","v","w"],
            Implies(And(In(y,one,two),In(z,one,two),In(o,one,two),In(v,one,two),In(w,one,two)),
                Le(Call("cosine",b,y,z,o,v,w),Rat(37,43))));
        return And(cube,low,high,other);
    }

    private static Formula ForAll(string[] names, Formula body)
    {
        var real = new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
        Formula.BoundVariable[] binders = names.Select(name =>
            new Formula.BoundVariable(FormulaIdentifier.Create(name), real)).ToArray();
        return new Formula.BindMany(FormulaQuantifier.ForAll,[.. binders],body);
    }

    private static Formula And(params Formula[] clauses)
    {
        if (clauses.Length == 0) throw new ArgumentException("Empty conjunction.");
        var result = clauses[^1];
        for (var i = clauses.Length-2; i >= 0; i--)
            result = new Formula.Logic(clauses[i],FormulaLogicOperator.And,result);
        return result;
    }

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise,FormulaLogicOperator.Implies,conclusion);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left,FormulaRelationOperator.LessThanOrEqual,right);
    private static Formula In(Formula value, Formula lower, Formula upper) =>
        new Formula.Relation(value,FormulaRelationOperator.MemberOf,Call("Icc",lower,upper));
    private static Formula Rat(int n, int d) => F.Seq(F.Frac,F.Grp(Number(n)),F.Grp(Number(d)));
    private static Formula Number(int value) => value switch
    {
        4 => F.D(4), 5 => F.D(5), 8 => F.D(8), 37 => F.D(3, 7), 43 => F.D(4, 3),
        293 => F.D(2, 9, 3), 400 => F.D(4, 0, 0),
        1577 => F.D(1, 5, 7, 7), 2236 => F.D(2, 2, 3, 6),
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };
    private static Formula Call(string name, params Formula[] args)
        => new Formula.Apply(F.Id(name), [.. args]);
}
