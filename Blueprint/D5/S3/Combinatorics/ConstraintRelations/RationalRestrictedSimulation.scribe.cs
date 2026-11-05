using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ConstraintRelations;

internal sealed class RationalRestrictedSimulationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ConstraintRelations/RationalRestrictedSimulation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite restricted ternary factors preserve each full original assignment weight and the complete visible law.",
        H("Constructive simulation with a multiplicative face equality"),
        Blocks(
            Def("restricted", "Full-table restriction", "Restricted",
                "Restricted T means that the canonical normalized rational Table T is Strict and T(000)T(110)=T(100)T(010). Its eight entries are tested before assigning a scope. Consequently unvisited entries under identified scope variables retain positivity, support and normalization."),
            Def("activity", "Normalized vertex activities", "activityTable",
                "For a positive rational t the allowed entries 000,100,010,110,001 are respectively (1,t,1,t,1)/(3+2t), with zero at 101,011,111. Their sum is one and both sides of the face equality are t divided by the square of (3+2t). The canonical pinTable has all five allowed entries 1/5 and also satisfies the equality. At a zero pin o, activityTable on (u,o,o) supplies weight t when u is one and weight one when u is zero, divided by 3+2t. pinTable on (a,a,b) supplies the exclusion of simultaneous ones, divided by five."),
            Def("local-index", "The finite local factor list", "LocalIndex",
                "LocalIndex is Unit plus ((Fin 3 plus Fin 4) plus Unit): one support factor, three edge factors, four activity factors and one top activity factor. Each entry is an actual normalized ternary Table, and repeated factors remain separate entries in the product."),
            Def("local-factors", "Replacement on actual variable names", "localFactors",
                "Given a Strict Table T and names x,y,z,o,p,q of an arbitrary type V, localFactors keeps the original ordered scope (x,y,z) as a pinTable support factor, implements the bottom binary table B(u,v)=T(u,v,0) by three edges and four activities, and appends the activity tau=T(001)/T(000) on (z,o,o). All names are actual variables. The parameters p,q are fresh hidden names in the local extension, while o is shared by the entire replacement network."),
            Def("local-scalar", "The local normalization scalar", "localScale",
                "The binary data consist of a shape, positive rational internal activities alpha,beta, positive terminal activities lambda,mu and scalar c. Write D=1/[5 cubed (3+2alpha)(3+2beta)(3+2lambda)(3+2mu)]. Then localScale(T,hT)=D c/[5(3+2tau)] is positive rational. It excludes the outer common pin and includes every edge and activity normalization in the nine local factors."),
            Def("local-extension", "Retaining arbitrary original variables", "localExtension",
                "For a Factor f on V, the replacement variable type is V plus (Unit plus Bool). The injection of V retains every original variable. The Unit name is the common zero pin; the two Bool names are the fresh internal bits. Only the ordered original factor scope is passed to the local construction, so repeated or coincident terminals are permitted without an equality primitive."),
            Node("local-simulation", "Pointwise complete local simulation", "local_simulation",
                StatementSource.FromAuthor(LocalFormula()),
                "For every type V, every canonical Factor f on V and proof hf that its full table is Strict, all local replacement factors are Restricted, localScale is positive, and for every complete original assignment b, summing every assignment h of both fresh bits with the common pin set to zero gives localScale times f.value(b). The formula writes sumElim for the canonical Sum.elim operation and const(Unit,false) for the constant zero pin assignment. The scalar depends on the original table, never on b. This is an identity on all eight formal triples and therefore remains valid after arbitrary terminal identifications.", DescribeRole.Theorem),
            Paragraph(Text("The binary construction is explicit. Put r=B(0,0)B(1,1)/(B(1,0)B(0,1)). When r=1 use internal activities alpha=beta=1 and three harmless edges to the shared zero. The two free hidden bits give the constant matrix M=4. When r>1 use alpha=r-1,beta=1, edges u-p and p-v, and a harmless edge from v to the zero pin. Summing the isolated q gives M=2 times the matrix with rows (r,1) and (1,1). When r<1 use alpha=2/r-1 and beta=2(1-r)/r with the path u-p-q-v. Its rows are (1+alpha+beta,1+alpha) and (1+beta,1). Every case has positive rational entries and M(0,0)M(1,1)=r M(1,0)M(0,1).")),
            Paragraph(Text("Set c=M(0,0)/B(0,0), lambda=B(1,0)M(0,0)/(B(0,0)M(1,0)), and mu=B(0,1)M(0,0)/(B(0,0)M(0,1)). The terminal activities give lambda to the power u times mu to the power v times M(u,v)=c B(u,v) at all four inputs. Both terminal activities and all internal activities use activityTable. The two unused bits in the flat case are freely summed, rather than discarded. No additional zero pin is introduced by these padding slots. Finally T(x,y,z)=pinRaw(x,y,z)B(x,y)tau to the power z at all eight triples, including the three forbidden ones.")),
            Def("replacement-hidden", "All hidden names", "ReplacementHidden",
                "ReplacementHidden(m,k)=Fin m plus (Unit plus (Fin k times Bool)). The original hidden variables remain present even when no factor mentions them. One Unit variable supplies the single shared pin, and each original factor receives its own two fresh bits."),
            Def("replacement-index", "The global factor list", "ReplacementIndex",
                "ReplacementIndex(k)=Unit plus (Fin k times LocalIndex). The first factor is pinTable on the single shared pin repeated three times. Every original factor then contributes its nine local factors. In particular k=0 leaves precisely the common pin factor."),
            Def("original-embedding", "Embedding before numbering", "originalEmbedding",
                "The canonical original variable type Fin n plus Fin m embeds into Fin n plus ReplacementHidden(m,k) by the identity on visible labels and the first injection on old hidden labels."),
            Def("family", "The actual restricted family", "replacementFamily",
                "replacementFamily(net,hs) constructs the one common pin and each localFactors family on the injected original scope, using the private pair (j,false),(j,true) for old factor j. All factors are canonical Factor values with full Restricted tables. Different old factors may share any original variable or their entire scopes."),
            Def("replacement", "The canonical replacement network", "replacement",
                "replacement(net,hs) is numberedNetwork applied to replacementFamily. It has the original visible count n, hidden count card(ReplacementHidden(m,k)) and factor count card(ReplacementIndex(k)). Finite equivalences number hidden names and factors while leaving visible labels fixed."),
            Def("extension", "Complete assignment extension", "extendAssignment",
                "extendAssignment(b,h) assigns every old visible or hidden variable its value in b, and every fresh variable its value in h. Its domain is Fin n plus ReplacementHidden(m,k), and h ranges over every function from Unit plus (Fin k times Bool) to Bool."),
            Def("global-scalar", "The one-pin global scalar", "replacementScale",
                "replacementScale(net,hs)=(1/5) times the product over all original factors j of localScale((net.factor j).table,hs j). It is positive and assignment independent. When k=0 the product is one, so this scalar is exactly 1/5."),
            Def("numbered-embedding", "Embedding into actual numbered output variables", "numberedEmbedding",
                "numberedEmbedding is identity on visible labels. On an original hidden label it first injects into ReplacementHidden and then applies its canonical equivalence to Fin(card ReplacementHidden). It is injective, preserving all original distinctions and all identifications in a scope."),
            Def("numbered-assignment", "Assignments on the actual numbered output", "numberedAssignment",
                "numberedAssignment(b,h) composes extendAssignment(b,h) with inverse hidden numbering. Evaluation at numberedEmbedding(v) is exactly b(v), for every old variable v and every fresh assignment h."),
            Node("network-simulation", "Complete finite-network replacement", "result",
                StatementSource.FromAuthor(NetworkFormula()),
                "For all natural n,m,k, every canonical Network net and proof hs that all original full tables are Strict, the numbered embedding is injective and fixes every visible label. Extended assignment evaluation preserves every old variable. The designated support factor of each old factor has precisely its injected original ordered scope. Every output factor is Restricted and the scalar C=replacementScale(net,hs) is positive. For each fixed full original assignment, summing all fresh assignments of the actual numbered replacement multiplies its old complete product by C. Both partitions are positive; every visible marginal is multiplied by C; the partition is multiplied by C; and the full normalized visible law agrees at every assignment.", DescribeRole.Theorem),
            Paragraph(Text("For a fixed complete original assignment, finite equivalences separate the common pin and the private pairs, then curry the private assignments into one two-bit assignment per old factor. The shared pin kills the entire branch where it is one. On its zero branch, Fintype.prod_sum separates all private hidden sums, giving C times the original product. This computation includes every fresh assignment; excluded assignments have zero weight through actual factors. Summing subsequently over every original hidden assignment gives the marginal identity. The positive original partition and positive C give a positive new partition; division gives identical laws.")),
            Paragraph(Text("With no old factors, the original hidden variables still range over their full Boolean cube and contribute their entire multiplicity. The single additional pin multiplies every original complete assignment weight by 1/5. The proof allows zero visible variables as well as all n at least one, arbitrary original hidden sets, repeated coordinates and completely coincident scopes. It supplies a finite rational replacement, without a size optimality, inference efficiency, causal kernel or sampling interpretation. Source classification and application corollaries are separate results."))
        ), []));

    private static Formula LocalFormula()
    {
        Formula v=F.Id("V"), f=F.Id("f"), hf=F.Id("hf"), b=F.Id("b"), h=F.Id("h"), i=F.Id("i");
        Formula cube=Arrow(v,Named("Bool")), bits=Arrow(Named("Bool"),Named("Bool"));
        Formula ext=Call("localExtension", f,hf,i), scalar=Call("localScale",Call("table",f),hf);
        Formula assign=Call("sumElim",b,Call("sumElim",Call("const",Named("Unit"),Named("false")),h));
        Formula lhs=Sum("h",bits,Prod("i",Named("LocalIndex"),Call("value",ext,assign)));
        return Disp(All("V",Named("Type"),All("f",Call("Factor",v),All("hf",Call("Strict",Call("table",f)),
            And(All("i",Named("LocalIndex"),Call("Restricted",Call("table",ext))),
                And(Pos(scalar),All("b",cube,Eq(lhs,Mul(scalar,Call("value",f,b))))))))));
    }

    private static Formula NetworkFormula()
    {
        Formula n=F.Id("n"),m=F.Id("m"),k=F.Id("k"),net=F.Id("net"),hs=F.Id("hs"),a=F.Id("a"),b=F.Id("b"),h=F.Id("h"),i=F.Id("i"),j=F.Id("j"),v=F.Id("v");
        Formula old=Call("Sum",Call("Fin",n),Call("Fin",m)),fresh=Call("Sum",Named("Unit"),Call("Prod",Call("Fin",k),Named("Bool")));
        Formula cube=Arrow(Call("Fin",n),Named("Bool")),oldCube=Arrow(old,Named("Bool")),freshCube=Arrow(fresh,Named("Bool"));
        Formula rep=Call("replacement",net,hs),c=Call("replacementScale",net,hs),embed=Call("numberedEmbedding",n,m,k),assign=Call("numberedAssignment",b,h);
        Formula count=Call("card",Call("ReplacementIndex",k));
        Formula eval=All("b",oldCube,All("h",freshCube,All("v",old,Eq(Call("apply",assign,Call("apply",embed,v)),Call("apply",b,v)))));
        Formula scope=Call("scope",Call("factor",net,j));
        Formula outIndex=Call("equivFin",Call("ReplacementIndex",k),Call("inr",Call("pair",j,Call("inl",Named("unit")))));
        Formula scopeEq=All("j",Call("Fin",k),Eq(Call("scope",Call("factor",rep,outIndex)),
            Call("triple",Call("apply",embed,Call("fst",scope)),Call("apply",embed,Call("fst",Call("snd",scope))),Call("apply",embed,Call("snd",Call("snd",scope))))));
        Formula fixedEq=All("b",oldCube,Eq(Sum("h",freshCube,Prod("i",Call("Fin",count),Call("value",Call("factor",rep,i),assign))),
            Mul(c,Prod("j",Call("Fin",k),Call("value",Call("factor",net,j),b)))));
        Formula body=And(Call("Injective",embed),And(All("i",Call("Fin",n),Eq(Call("apply",embed,Call("inl",i)),Call("inl",i))),
            And(eval,And(scopeEq,And(All("i",Call("Fin",count),Call("Restricted",Call("table",Call("factor",rep,i)))),
            And(Pos(c),And(fixedEq,And(Pos(Call("partition",net)),And(Pos(Call("partition",rep)),
            And(All("a",cube,Eq(Call("marginal",rep,a),Mul(c,Call("marginal",net,a)))),
            And(Eq(Call("partition",rep),Mul(c,Call("partition",net))),All("a",cube,Eq(Call("law",rep,a),Call("law",net,a))))))))))))));
        return Disp(All("n",Named("Nat"),All("m",Named("Nat"),All("k",Named("Nat"),All("net",Call("Network",n,m,k),
            All("hs",All("j",Call("Fin",k),Call("Strict",Call("table",Call("factor",net,j)))),body))))));
    }

    private static DocumentBlock Def(string id,string title,string name,string prose) => Node(id,title,name,StatementSource.WithoutFormula(),prose,DescribeRole.Definition);
    private static DocumentBlock Node(string id,string title,string name,StatementSource statement,string prose,DescribeRole role) => Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create(Prefix+name),H(title),statement,AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);
    private static Formula Named(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Arrow(Formula a,Formula b) => Seq(Open,a,Close,Sp,To,Sp,b);
    private static Formula All(string x,Formula t,Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(x),t,b);
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Pos(Formula a) => new Formula.Relation(D(0),FormulaRelationOperator.LessThan,a);
    private static Formula Mul(Formula a,Formula b) => Seq(Grp(a),Sp,F.Cdot,Sp,Grp(b));
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Grp(a),FormulaLogicOperator.And,Grp(b));
    private static Formula Sum(string x,Formula t,Formula b) => Seq(F.Sum,Underscore,Grp(F.Id(x),Sp,InMacro,Sp,t),Sp,Grp(b));
    private static Formula Prod(string x,Formula t,Formula b) => Seq(F.Prod,Underscore,Grp(F.Id(x),Sp,InMacro,Sp,t),Sp,Grp(b));
}
