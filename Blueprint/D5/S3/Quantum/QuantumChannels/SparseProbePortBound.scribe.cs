using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class SparseProbePortBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Quantum/QuantumChannels/SparseProbePortBound.";
    private static DocumentBlock Node(string id,string name,Formula f,string text,DescribeRole role=DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create(Prefix+(name == "Port.kraus" ? "kraus" : name == "Port.channel" ? "channel" : name)),H(name),
            StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite classical-quantum port incurs a uniform two-setting total-variation error when its quantum block is smaller than the input dimension.",
        H("Operational sparse-probe compression bound"),Blocks(
            Node("port","Port",PortFormula(),"FiniteType denotes an arbitrary type equipped with Fintype, FiniteFamily(F) denotes an F-indexed family of such types, and Branch(F,a,b) is the dependent sum of a(f) times b(f). A port has arbitrary finite classical flags F and finite, flag-dependent encoder and decoder Kraus families. Its encoder matrices have size q by d and its decoder matrices have size d by q. Encoder completeness holds after summing all flags. Each decoder is trace preserving on the entire q-dimensional block. The same encoder and decoder are used at both future settings. All input-dependent quantum information passes through the block; the flag is a classical record. This is the measurement-relative compression model of Bluhm, Rauber and Wolf, arXiv:1708.04898v4. Mayer and Knill, arXiv:1805.04491v1, Theorem 1 supplies connected-probe rigidity, with broader nondisturbance structure in Koashi and Imoto, quant-ph/0101144."),
            Node("port-kraus","Port.kraus",KrausFormula(),"The composite branch is Rfb Bfa, indexed by the actual flag and both finite Kraus indices."),
            Node("port-channel","Port.channel",ChannelFormula(),"Completeness gives an actual channel in the canonical completely positive, trace-preserving interface. Its action on every matrix is the sum of composite Kraus conjugations."),
            Node("readout-probabilities","probabilities",ProbabilityFormula(),"The notation matrix(rho) is CStarMatrix.ofMatrix.symm applied to the underlying density-state matrix. These are the Born probabilities of a complete coordinate readout after the displayed unitary. The input is any complex positive semidefinite density matrix of trace one."),
            Node("two-setting-error","twoSettingError",ErrorFormula(),"The supremum ranges over every density input. Both errors use the same channel. Total variation is one half of the finite sum of absolute probability differences."),
            Node("port-estimate","PortEstimate",EstimateFormula(),"The record contains the composite rank bound, total Hilbert--Schmidt square, trace-square bound, both total-loss estimates, and the actual two-setting error lower bound. Dimension differences and the quantitative bounds use real arithmetic; matrix rank and block dimension use natural numbers."),
            Node("attainable-port-errors","portErrors",ErrorsFormula(),"The attainable errors allow every finite flag carrier and every finite dependent pair of Kraus-index families, without a bound on the number of flags."),
            Node("sparse-probe-port-bound","sparse_probe_port_bound",BoundFormula(),"For every actual composite Kraus matrix, the original factorized trace inequality is applied with U=Rfb adjoint and W=Bfa. Encoder and decoder completeness imply that the total Hilbert--Schmidt square is d and the total trace square is at most qd. The complex coercivity estimate gives total survival loss at least mu(d-q)/(2+mu). Each of the d coordinate inputs and the additional pure input v has an ideal event of probability one, whose loss is bounded by its actual TV error. Summing these d+1 tests yields the pointwise bound. The same non-strict constant passes to the infimum. An identity port attains zero when q=d. This concerns two fixed settings; no lower bound for a larger menu is used. No optimality or novelty assertion is made.",DescribeRole.Theorem))));
    private static Formula V(string n) => F.Id(n);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Call(string n, params Formula[] x) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. x]);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula.BoundVariable[] b, Formula p) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. b], p);
    private static Formula Rel(Formula x, FormulaRelationOperator r, Formula y) => new Formula.Relation(x, r, y);
    private static Formula Eq(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x,y);
    private static Formula Fin(Formula d) => Call("Fin",d);
    private static Formula Mat(Formula d) => Call("Matrix",Fin(d),Fin(d),C);
    private static Formula Vec(Formula d) => Seq(Fin(d), Sp, To, Sp, C);
    private static Formula Sum(string i, Formula domain, Formula f) => Seq(F.Sum, Underscore, Grp(V(i), Sp, Colon, Sp, domain), Sp, f);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula At(Formula f, params Formula[] x) => Seq(f, Sp, Parenthesized(x.Length == 1 ? x[0] : Seq(x[0], Comma, Sp, x[1])));
    private static Formula Norm(Formula x) => Call("normSq",x);

    private static Formula PortType(Formula d,Formula q,Formula f,Formula a,Formula b) => Call("Port",d,q,f,a,b);
    private static Formula PortFormula()
    {
        Formula d=V("d"),q=V("q"),f=V("F"),a=V("a"),b=V("b"),p=V("P");
        Formula flag=V("f"),i=V("i"),j=V("j"),encoder=Call("encode",p,flag,i),decoder=Call("decode",p,flag,j);
        return All([B("d",N),B("q",N),B("F",Call("FiniteType")),B("a",Call("FiniteFamily",f)),B("b",Call("FiniteFamily",f)),B("P",PortType(d,q,f,a,b))],
            And(Eq(Sum("f",f,Sum("i",At(a,flag),Mul(Call("adjoint",encoder),encoder))),Num(1)),
                All([B("f",f)],Eq(Sum("j",At(b,flag),Mul(Call("adjoint",decoder),decoder)),Num(1)))));
    }
    private static Formula KrausFormula()
    {
        Formula d=V("d"),q=V("q"),f=V("F"),a=V("a"),b=V("b"),p=V("P"),x=V("x");
        return All([B("d",N),B("q",N),B("F",Call("FiniteType")),B("a",Call("FiniteFamily",f)),B("b",Call("FiniteFamily",f)),B("P",PortType(d,q,f,a,b)),B("x",Call("Branch",f,a,b))],Eq(Call("kraus",p,x),Mul(Call("decode",p,Call("flag",x),Call("decoderIndex",x)),Call("encode",p,Call("flag",x),Call("encoderIndex",x)))));
    }
    private static Formula ChannelFormula()
    {
        Formula d=V("d"),q=V("q"),f=V("F"),a=V("a"),b=V("b"),p=V("P"),x=V("x"),m=V("M");
        Formula k=Call("kraus",p,x);
        return All([B("d",N),B("q",N),B("F",Call("FiniteType")),B("a",Call("FiniteFamily",f)),B("b",Call("FiniteFamily",f)),B("P",PortType(d,q,f,a,b)),B("M",Mat(d))],Eq(Call("channelAction",Call("channel",p),m),Sum("x",Call("Branch",f,a,b),Mul(Mul(k,m),Call("adjoint",k)))));
    }
    private static Formula ProbabilityFormula()
    {
        Formula d=V("d"),u=V("U"),rho=V("rho"),i=V("i");
        return All([B("d",N),B("U",Mat(d)),B("rho",Call("DensityState",Fin(d))),B("i",Fin(d))],Eq(At(Call("probabilities",u,rho),i),Call("re",At(Parenthesized(Mul(Mul(u,Call("matrix",rho)),Call("adjoint",u))),i,i))));
    }
    private static Formula ErrorFormula()
    {
        Formula d=V("d"),u=V("U"),t=V("T"),rho=V("rho");
        Formula TV(Formula m) => Call("totalVariation",Call("probabilities",m,rho),Call("probabilities",m,Call("mapState",t,rho)));
        return All([B("d",N),B("U",Mat(d)),B("T",Call("QuantumChannel",Fin(d),Fin(d)))],Eq(Call("twoSettingError",u,t),Call("sSup",new Formula.SetBuilder(Call("max",TV(Num(1)),TV(u)),rho,Call("DensityState",Fin(d))))));
    }
    private static Formula ErrorsFormula()
    {
        Formula d=V("d"),q=V("q"),u=V("U"),e=V("e"),f=V("F"),a=V("a"),b=V("b"),p=V("P");
        return All([B("d",N),B("q",N),B("U",Mat(d)),B("e",R)],new Formula.Logic(Rel(e,FormulaRelationOperator.MemberOf,Call("portErrors",d,q,u)),FormulaLogicOperator.Iff,
            new Formula.BindMany(FormulaQuantifier.Exists,[B("F",Call("FiniteType")),B("a",Call("FiniteFamily",f)),B("b",Call("FiniteFamily",f)),B("P",PortType(d,q,f,a,b))],Eq(e,Call("twoSettingError",u,Call("channel",p))))));
    }
    private static Formula EstimateFormula()
    {
        Formula d=V("d"),q=V("q"),f=V("F"),a=V("a"),b=V("b"),p=V("P"),u=V("U"),v=V("v"),mu=V("mu"),x=V("x");
        Formula branch=Call("Branch",f,a,b), k=Call("kraus",p,x);
        Formula hs=Sum("x",branch,Call("hsSq",k)), tr=Sum("x",branch,Norm(Call("trace",k))), loss=Sum("x",branch,Call("probeLoss",k,v));
        Formula lower=Frac(Mul(mu,Sub(d,q)),Mul(Add(Num(2),mu),Add(d,Num(1))));
        Formula body=And(All([B("x",branch)],Le(Call("rank",k),q)),And(Eq(hs,d),And(Le(tr,Mul(q,d)),And(Le(Mul(Frac(mu,Add(Num(2),mu)),Sub(d,q)),loss),And(Le(loss,Mul(Add(d,Num(1)),Call("twoSettingError",u,Call("channel",p)))),Le(lower,Call("twoSettingError",u,Call("channel",p))))))));
        return All([B("d",N),B("q",N),B("F",Call("FiniteType")),B("a",Call("FiniteFamily",f)),B("b",Call("FiniteFamily",f)),B("P",PortType(d,q,f,a,b)),B("U",Mat(d)),B("v",Vec(d)),B("mu",R)],new Formula.Logic(Call("PortEstimate",p,u,v,mu),FormulaLogicOperator.Iff,body));
    }
    private static Formula BoundFormula()
    {
        Formula d=V("d"),q=V("q"),u=V("U"),v=V("v"),r=V("r"),mu=V("mu"),i=V("i"),f=V("F"),a=V("a"),b=V("b"),p=V("P");
        Formula lower=Frac(Mul(mu,Sub(d,q)),Mul(Add(Num(2),mu),Add(d,Num(1))));
        Formula h=And(Rel(Num(0),FormulaRelationOperator.LessThan,d),And(Rel(Num(0),FormulaRelationOperator.LessThan,q),And(Eq(Mul(Call("adjoint",u),u),Num(1)),And(Eq(Sum("i",Fin(d),Norm(At(v,i))),Num(1)),And(All([B("i",Fin(d))],Eq(At(u,r,i),Call("conj",At(v,i)))),And(Rel(Num(0),FormulaRelationOperator.LessThan,mu),All([B("i",Fin(d))],Le(mu,Norm(At(v,i))))))))));
        Formula point=All([B("F",Call("FiniteType")),B("a",Call("FiniteFamily",f)),B("b",Call("FiniteFamily",f)),B("P",PortType(d,q,f,a,b))],Call("PortEstimate",p,u,v,mu));
        return All([B("d",N),B("q",N),B("U",Mat(d)),B("v",Vec(d)),B("r",Fin(d)),B("mu",R)],Imp(h,And(point,And(Le(lower,Call("sInf",Call("portErrors",d,q,u))),Eq(Call("sInf",Call("portErrors",d,d,u)),Num(0))))));
    }
}
