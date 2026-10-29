using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class NativeCommandPathTightnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint fourth oscillations of the actual native commands on blocks no longer than one mesh cell.",
        H("Submesh oscillations of stopped native commands"),
        Blocks(
            Paragraph(Text("A raw model B determines the original command triple (a,b,j), with j its ordinary chronological area. Each complete word consists of n cubed independent sign pairs and has mass 4 to the power minus n cubed. Unused suffixes after the first wall contact retain this same mass. Write delta=1/n squared. The final forced upper-wall leg begins at time n if no earlier wall has been reached.")),
            Paragraph(Text("For an anchored block I=[a,min(R,a+h)], blockFourthOscillation is the supremum over s,t in I of the fourth power of the norm of command(t)-command(s). The norm is the maximum coordinate norm on the joint real triple. blockFourthExpectation is the sum of this quantity over all complete words with their original common mass.")),
            Describe.Lean(
                DescribeId.Create("actual-short-block-estimate"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/NativeCommandPathTightness.actual_short_block_estimate"),
                H("Fourth oscillations on submesh blocks"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The constant is common to every horizon and every complete word law satisfying the displayed conditions. The area identity holds at every nonnegative time. The restriction R+1<n places the observed interval before the terminal upper-wall leg.")),
                    Paragraph(Text("Periodicity reduces the compact coefficient estimate to a single phase fundamental domain. Smoothness bounds both drift entries and both diagonal covariance entries there. The positive matrix square root identity bounds every noise coefficient by those diagonal entries, yielding a common bound L sqrt(delta) for both horizontal increments from every alive node.")),
                    Paragraph(Text("The stopped height lies between the two walls, so the first real control is bounded during each executed chord. The polynomial chord formula then bounds the change of all three coordinates by a constant times sqrt(delta) times the change of its interpolation parameter. Clipping this parameter at the first wall contact preserves its Lipschitz bound.")),
                    Paragraph(Text("Induction over the original word joins the chord estimates at the actual surviving nodes. Splitting at a node also covers a block which straddles that node. On the interval before the terminal leg, the resulting path has Lipschitz constant at most K/sqrt(delta). Its fourth oscillation on a block of length h is at most K to the fourth power times h to the fourth power divided by delta squared. For h<=delta this is bounded by K to the fourth power times h squared. Summing the pointwise bound over the complete uniform word law preserves the constant.")),
                    Paragraph(Text("This estimate applies only to blocks of length at most delta. Control of larger blocks, and tightness in continuous path space, require a further probabilistic oscillation estimate."))),
                DescribeRole.Theorem))));

    private static Formula V(string x) => F.Id(x);
    private static Formula D(int x) => new Formula.Number(x);
    private static Formula R => Seq(Mathbb,Grp(V("R")));
    private static Formula N => Seq(Mathbb,Grp(V("N")));
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname,Grp(V(name))),[..args]);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall,Sp,V(x),Colon,Sp,type,Comma,Sp,body);
    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists,Sp,V(x),Colon,Sp,type,Comma,Sp,body);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Par(x),FormulaLogicOperator.And,Par(y));
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Par(x),FormulaLogicOperator.Implies,Par(y));

    private static Formula Statement()
    {
        var B=V("B"); var n=V("n"); var a=V("a"); var h=V("h");
        var horizon=V("R"); var t=V("t"); var w=V("w"); var C=V("C");
        var words=new Formula.TypeArrow(Call("Fin",new Formula.Power(n,D(3))),V("SignPair"));
        var area=All("w",words,All("t",R,Imp(Le(D(0),t),
            Eq(Call("commandArea",B,n,w,t),Call("coordinate",Call("command",B,n,w,t),D(2))))));
        var estimate=Le(Call("blockFourthExpectation",B,n,horizon,a,h),
            Multiply(C,new Formula.Power(h,D(2))));
        var block=Imp(Le(D(0),a),Imp(Le(a,horizon),
            Imp(Lt(D(0),h),Imp(Le(h,Call("mesh",n)),And(estimate,area)))));
        var mesh=All("n",N,Imp(Lt(Add(horizon,D(1)),n),All("a",R,All("h",R,block))));
        var horizons=All("R",R,Imp(Lt(D(0),horizon),mesh));
        return All("B",V("Model"),Some("C",R,And(Le(D(0),C),horizons)));
    }
}
