using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a;

internal sealed class HardinA229538StripCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229538StripCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite vector relation for one-defect HDA strips", H("Finite vector relation for one-defect HDA strips"), Blocks(
            Paragraph(Text("Continuation counts are resolved by the number of remaining monochromatic bonds. Zero-defect continuations follow the five-row proper-colouring transfer.")),
            Node("countCut",CountCut(),false,"The cost counts the colour coincidences at the thirteen oriented pairs of row positions."),
            Node("cost_countCut",CutEquality(),true,"The sum of the thirteen indicators equals the number of monochromatic bonds on the cut."),
            Node("movesOne",Moves(),false,"The entries are the successor columns that exhaust one unit of the remaining defect budget."),
            Node("step_one",StepOne(),true,"The action of the exact-one-cut matrix is a sum over its successors."),
            Node("weights",Weights(),false,"These coefficients express zero-defect continuations in terms of the first twelve continuation vectors."),
            Node("classIndex",ClassIndex(),false,"The lookup classifies five-entry boundary columns under colour permutation and row reversal."),
            Node("tableOne",TableOne(),false,"Each row gives one-defect continuations at one exponent, indexed by the class of the boundary column."),
            Node("zeroValues",ZeroValues(),false,"For larger exponents the zero-defect values are linear combinations of the twelve proper-colouring vectors."),
            Node("weight_eq",WeightEquality(),true,"The same coefficient formula also holds at the tabulated exponents."),
            Node("zero_values",PowerZero(),true,"The reconstructed value is the proper-colouring continuation vector at each exponent."),
            Node("table_powers",TablePowers(),true,"The first coordinate gives the one-defect continuations and the second gives the inherited proper-colouring continuations."),
            Node("coefficients538",Coefficients(),false,"The entries are ordered from the smallest shift of the recurrence to the largest."),
            Node("vector_polynomial",Polynomial(),true,"The relation holds simultaneously for all boundary columns and both residual budgets."))));

    private static DocumentBlock Node(string name, Formula statement, bool theorem, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name), H(name), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229538")),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i)=>i==0?new[]{Seq(Operatorname,Grp(V(p)))}:new[]{Dot,Seq(Operatorname,Grp(V(p)))}).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula App(Formula f,params Formula[] a) => new Formula.Apply(f,[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Fin(int n) => Call("Fin",N(n));
    private static Formula Val(Formula a) => Call("Fin.val",a);
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Multiply,Parenthesized(b));
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula If(Formula c,Formula a,Formula b) =>
        Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,a,Sp,Q("else"),Sp,b));
    private static Formula AsInt(Formula a) => Typed(a,Q("Int"));
    private static Formula SumOver(string n,Formula t,Formula body) =>
        Seq(F.Sum,Underscore,Grp(Typed(V(n),t)),Sp,Parenthesized(body));
    private static Formula Pow(Formula a,Formula b) => Seq(Parenthesized(a),Caret,Grp(b));


    private static Formula VectorLiteral(long[] entries)
    {
        Formula tail = Q("Matrix.vecEmpty");
        for (int i = entries.Length - 1; i >= 0; i--)
            tail = Call("Matrix.vecCons", N(entries[i]), tail);
        return tail;
    }
    private static Formula Column() => Q("HardinA233178Chromatic.Column");
    private static Formula D(string n,params Formula[] a) => Call("HardinA229538StripData."+n,a);
    private static Formula C(string n,params Formula[] a) => Call("HardinA233178Chromatic."+n,a);

    private static Formula Cert(string n,params Formula[] a) => Call("HardinA229538StripCertificate."+n,a);
    private static Formula Coefficients() =>
        Eq(Typed(Cert("coefficients538"),Arrow(Fin(20),Q("Int"))),VectorLiteral([-1296, 5184, 8640, -64656, 43848, 214008, -371692, -48036, 498819, -211910, -256127, 183692, 55115, -59620, -4121, 8804, -123, -566, 26, 12]));
    private static Formula Polynomial() {
        Formula Power(Formula n)=>Call("Matrix.mulVec",Pow(D("transfer"),n),D("terminal"));
        return Eq(Power(N(22)),SumOver("k",Fin(20),
            Call("SMul.smul",Cert("coefficients538",V("k")),Power(Add(N(2),Val(V("k")))))));
    }

    private static Formula CountCut() {
        var p=V("p");var q=V("q");
        var bonds=new[]{new[]{0,0},new[]{0,1},new[]{1,0},new[]{1,1},new[]{1,2},new[]{2,1},new[]{2,2},new[]{2,3},new[]{3,2},new[]{3,3},new[]{3,4},new[]{4,3},new[]{4,4}};
        var terms=bonds.Select(e=>If(Eq(C("colour",p,N(e[0])),C("colour",q,N(e[1]))),N(1),N(0)));
        return All("p",Column(),All("q",Column(),Eq(Typed(Cert("countCut",p,q),Q("Nat")),terms.Aggregate(Add))));
    }
    private static Formula CutEquality() => All("p",Column(),All("q",Column(),Eq(D("cost",V("p"),V("q")),
        Cert("countCut",V("p"),V("q")))));
    private static Formula Moves() => Typed(Cert("movesOne"),Arrow(Column(),Call("List",Column())));
    private static Formula StepOne() => All("w",Arrow(Column(),Q("Int")),All("p",Column(),
        Eq(App(Call("Matrix.mulVec",D("oneDefect"),V("w")),V("p")),
            Call("List.sum",Call("List.map",V("w"),Cert("movesOne",V("p")))))));
    private static Formula Weights() => Typed(Cert("weights"),Arrow(Fin(23),Arrow(Fin(12),Q("Int"))));
    private static Formula ClassIndex() => Typed(Cert("classIndex"),Arrow(Column(),Fin(25)));
    private static Formula TableOne() => Typed(Cert("tableOne"),Arrow(Fin(23),Arrow(Column(),Q("Int"))));
    private static Formula Expansion() => SumOver("j",Fin(12),
        Mul(Cert("weights",V("n"),V("j")),C("table",V("j"),V("p"))));
    private static Formula ZeroValues() => All("n",Fin(23),All("p",Column(),Eq(AsInt(Cert("zeroValues",V("n"),V("p"))),
        If(Typed(V("h"),Lt(Val(V("n")),N(12))),C("table",Call("Fin.castLT",V("n"),V("h")),V("p")),Expansion()))));
    private static Formula WeightEquality() => All("n",Fin(23),Eq(Cert("zeroValues",V("n")),
        SumOver("j",Fin(12),Call("SMul.smul",Cert("weights",V("n"),V("j")),C("table",V("j"))))));
    private static Formula OldPower(Formula n) => Call("Matrix.mulVec",Pow(C("T"),n),Typed(N(1),Arrow(Column(),Q("Int"))));
    private static Formula PowerZero() => All("n",Fin(23),Eq(Cert("zeroValues",V("n")),OldPower(Val(V("n")))));
    private static Formula TablePowers() {
        var n=V("n");
        return All("n",Fin(23),Eq(Call("Matrix.mulVec",Pow(D("transfer"),Val(n)),D("terminal")),
            Call("Sum.elim",Cert("tableOne",n),OldPower(Val(n)))));
    }
}
