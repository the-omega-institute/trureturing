using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class CssMonicPushoutLdpcDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/CssMonicPushoutLdpc.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/cowtanburton2024csssurgery");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Basis-preserving monic pushouts of length-two binary CSS complexes satisfy explicit row and column weight bounds.",
        H("LDPC bounds for monic CSS pushouts"),
        Blocks(
            Describe.Lean(DescribeId.Create("based-complex"), DeclarationHandle.Create(Prefix + "BasedComplex"),
                H("Based length-two complex"), StatementSource.FromAuthor(BasedComplexFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A based complex has finite bases in degrees zero, one and two, two binary matrix differentials, and their composite is zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("basis-matrix"), DeclarationHandle.Create(Prefix + "basisMatrix"),
                H("Basis matrix"), StatementSource.FromAuthor(BasisMatrixFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The matrix has a one in the row selected by the image of a basis element and zero elsewhere."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bp-chain-map"), DeclarationHandle.Create(Prefix + "BPChainMap"),
                H("Basis-preserving chain map"), StatementSource.FromAuthor(BPChainMapFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A basis-preserving chain map consists of basis functions in all three degrees whose matrices commute with both differentials."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("monic"), DeclarationHandle.Create(Prefix + "Monic"),
                H("Monic basis-preserving map"), StatementSource.FromAuthor(MonicFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Monicity is degreewise injectivity of the induced matrix maps."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("glue"), DeclarationHandle.Create(Prefix + "glue"),
                H("Pushout identification"), StatementSource.FromAuthor(GlueFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The relation identifies the image of one apex basis element in the left foot with its image in the right foot."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pbasis"), DeclarationHandle.Create(Prefix + "PBasis"),
                H("Pushout basis"), StatementSource.FromAuthor(PBasisFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The pushout basis is the quotient of the disjoint union by the identification relation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sum-differentials"), DeclarationHandle.Create(Prefix + "sumD2"),
                H("Degree-two block differential"), StatementSource.FromAuthor(SumDFormula("sumD2", "d2")),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The direct-sum differential is the block diagonal matrix with the two input differentials."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sum-differential-one"), DeclarationHandle.Create(Prefix + "sumD1"),
                H("Degree-one block differential"), StatementSource.FromAuthor(SumDFormula("sumD1", "d1")),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The direct-sum differential is the block diagonal matrix with the two input differentials."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pushout-differential-two"), DeclarationHandle.Create(Prefix + "pushoutD2"),
                H("Degree-two pushout differential"), StatementSource.FromAuthor(PushoutFormula("pushoutD2", "sumD2", 2, 1)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Each output coefficient is the sum of the selected representative coefficients over its quotient class."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pushout-differential-one"), DeclarationHandle.Create(Prefix + "pushoutD1"),
                H("Degree-one pushout differential"), StatementSource.FromAuthor(PushoutFormula("pushoutD1", "sumD1", 1, 0)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Each output coefficient is the sum of the selected representative coefficients over its quotient class."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("max-row-weight"), DeclarationHandle.Create(Prefix + "maxRowWeight"),
                H("Maximum row weight"), StatementSource.FromAuthor(MaxRowFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The maximum row weight is the finite supremum of the cardinalities of nonzero row supports."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("max-column-weight"), DeclarationHandle.Create(Prefix + "maxColWeight"),
                H("Maximum column weight"), StatementSource.FromAuthor(MaxColFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The maximum column weight is the maximum row weight of the transpose."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("is-ldpc"), DeclarationHandle.Create(Prefix + "IsLDPC"),
                H("Uniform LDPC family"), StatementSource.FromAuthor(IsLdpcFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("One natural-number bound controls both row and column weights of both differentials at every family index."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weights-two"), DeclarationHandle.Create(Prefix + "weights2"),
                H("Degree-two weights"), StatementSource.FromAuthor(WeightsFormula("weights2", "d2")),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The pair records maximum row and column weights of the degree-two differential."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weights-one"), DeclarationHandle.Create(Prefix + "weights1"),
                H("Degree-one weights"), StatementSource.FromAuthor(WeightsFormula("weights1", "d1")),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The pair records maximum row and column weights of the degree-one differential."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Cowtan--Burton Conjecture D.1"), StatementSource.FromAuthor(Eq(F.Id("claim"), Parenthesized(ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture D.1 (Appendix D, p. 18): \"Let C• ←f• A• →g• D• be a basis-preserving monic span in Ch(MatF2), and let Q• be the pushout chain complex of this monic span. Further, let the monic span be a representative of a family of monic spans which are parameterised by some n ∈ ℕ, and let A•, C• and D• be the Z-type complexes of quantum LDPC codes. Then (Q•, Q•) is also LDPC.\" The Lean proposition expands the source objects and counts."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The proved LDPC closure"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Monicity makes each quotient fibre contain at most one basis element from either foot. A quotient column is the image of any representative column, and its support has cardinality at most that of the input column, while a row support injects into the disjoint union of one row from each foot. Thus the column bound is the maximum of the two input column weights and the row bound is their sum. Applying these bounds pointwise gives the uniform family bound with constant wC + wD; no bound on the apex is required."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(Id("N")));
    private static Formula Type() => Seq(Operatorname, Grp(Id("Type")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Based() => new Formula.NamedConstant(FormulaIdentifier.Create("BasedComplex"));
    private static Formula Matrix(Formula r, Formula c, Formula k) => Call("Matrix", r, c, k);
    private static Formula Z2() => Call("ZMod", D(2));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Ne(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.NotEqual, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(Parenthesized(l), FormulaLogicOperator.And, Parenthesized(r));
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(Parenthesized(l), FormulaLogicOperator.Implies, Parenthesized(r));
    private static Formula Iff(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Iff, Parenthesized(r));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Arrow(Formula l, Formula r) => new Formula.TypeArrow(l, r);
    private static Formula Lambda(string name, Formula body) => Seq(LambdaLower, Sp, Id(name), Sp, Mapsto, Sp, body);
    private static Formula Lambda2(string first, string second, Formula body) => Lambda(first, Lambda(second, body));
    private static Formula Pair(Formula l, Formula r) => Parenthesized(Seq(l, Comma, Sp, r));
    private static Formula CallOp(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(Id(owner), Dot, Id(name)));
    private static Formula FromBlocks(Formula a, Formula b, Formula c, Formula d) => CallOp("fromBlocks", a, b, c, d);
    private static Formula Univ() => Qualified("Finset", "univ");
    private static Formula Filter(Formula p, Formula s) => CallOp("filter", p, s);
    private static Formula BasedComplexFormula() {
        var dim = Id("dim"); var d2 = Id("d2"); var d1 = Id("d1");
        return Disp(Eq(Based(), Seq(OpenBrace,
            Seq(dim, Colon, Arrow(Fin(D(3)), Nat())), Semi, Sp,
            Seq(d2, Colon, Matrix(Fin(App(dim, D(1))), Fin(App(dim, D(2))), Z2())), Semi, Sp,
            Seq(d1, Colon, Matrix(Fin(App(dim, D(0))), Fin(App(dim, D(1))), Z2())), Semi, Sp,
            Seq(Id("comp"), Colon, Eq(new Formula.Binary(d1, FormulaBinaryOperator.Multiply, d2), D(0))),
            CloseBrace)));
    }
    private static Formula BPChainMapFormula() {
        var A = Id("A"); var C = Id("C"); var i = Id("i"); var f = Id("f");
        Formula mul(Formula l, Formula r) => new Formula.Binary(l, FormulaBinaryOperator.Multiply, r);
        var fields = Seq(OpenBrace,
            Seq(f, Colon, All("i", Fin(D(3)), Arrow(Fin(App(Call("dim", A), i)), Fin(App(Call("dim", C), i))))), Semi, Sp,
            Seq(Id("comm2"), Colon, Eq(mul(Call("d2", C), Call("basisMatrix", App(f, D(2)))),
                mul(Call("basisMatrix", App(f, D(1))), Call("d2", A)))), Semi, Sp,
            Seq(Id("comm1"), Colon, Eq(mul(Call("d1", C), Call("basisMatrix", App(f, D(1)))),
                mul(Call("basisMatrix", App(f, D(0))), Call("d1", A)))), CloseBrace);
        return Disp(All("A", Based(), All("C", Based(), Eq(Call("BPChainMap", A, C), fields))));
    }
    private static Formula BasisMatrixFormula() {
        var m = Id("m"); var n = Id("n"); var phi = Id("phi"); var j = Id("j"); var a = Id("a");
        var body = Eq(Call("basisMatrix", phi), Lambda2("j", "a", Call("ite", Eq(App(phi, a), j), D(1), D(0))));
        return Disp(All("m", Nat(), All("n", Nat(), All("phi", Arrow(Fin(m), Fin(n)), body))));
    }
    private static Formula MonicFormula() {
        var A=Id("A"); var C=Id("C"); var phi=Id("phi"); var i=Id("i");
        var body=Iff(App(Qualified("BPChainMap", "Monic"), phi), All("i",Fin(D(3)), CallOp("Injective", CallOp("mulVec", Call("basisMatrix", Call("f",phi,i))))));
        return Disp(All("A",Based(),All("C",Based(),All("phi",Call("BPChainMap",A,C),body))));
    }
    private static Formula GlueFormula() {
        var A=Id("A"); var C=Id("C"); var Dd=Id("D"); var phi=Id("phi"); var psi=Id("psi"); var i=Id("i"); var x=Id("x"); var y=Id("y"); var a=Id("a");
        var side=Call("Sum",Fin(App(Call("dim",C),i)),Fin(App(Call("dim",Dd),i)));
        var rel=Exists("a",Fin(App(Call("dim",A),i)),And(Eq(x,Call("inl",App(Call("f",phi,i),a))),Eq(y,Call("inr",App(Call("f",psi,i),a)))));
        return Disp(All("A",Based(),All("C",Based(),All("D",Based(),All("phi",Call("BPChainMap",A,C),All("psi",Call("BPChainMap",A,Dd),All("i",Fin(D(3)),All("x",side,All("y",side,Iff(App(Call("glue",phi,psi,i),x,y),rel))))))))));
    }
    private static Formula PBasisFormula() {
        var A=Id("A"); var C=Id("C"); var Dd=Id("D"); var phi=Id("phi"); var psi=Id("psi"); var i=Id("i");
        return Disp(All("A",Based(),All("C",Based(),All("D",Based(),All("phi",Call("BPChainMap",A,C),All("psi",Call("BPChainMap",A,Dd),All("i",Fin(D(3)),Eq(App(Call("PBasis",phi,psi),i),Call("Quot",App(Call("glue",phi,psi),i))))))))));
    }
    private static Formula SumDFormula(string name, string field) {
        var C=Id("C"); var Dd=Id("D");
        return Disp(All("C",Based(),All("D",Based(),Eq(Call(name,C,Dd),FromBlocks(Call(field,C),D(0),D(0),Call(field,Dd))))));
    }
    private static Formula PushoutFormula(string name,string sum,int srcDeg,int tgtDeg) {
        var A=Id("A"); var C=Id("C"); var Dd=Id("D"); var phi=Id("phi"); var psi=Id("psi"); var X=Id("X"); var Y=Id("Y"); var x=Id("x");
        var p=Call("PBasis",phi,psi,D((byte)tgtDeg));
        var q=Call("PBasis",phi,psi,D((byte)srcDeg));
        var rhs=App(Qualified("Finset","sum"),
            Filter(Lambda("x",Eq(App(Qualified("Quot","mk"),Call("glue",phi,psi,D((byte)tgtDeg)),x),X)),Qualified("Finset","univ")),
            Lambda("x",App(Call(sum,C,Dd),x,App(Qualified("Quot","out"),Y))));
        var body=Seq(LambdaLower,Sp,Parenthesized(Seq(X,Colon,p)),Sp,Mapsto,Sp,
            LambdaLower,Sp,Parenthesized(Seq(Y,Colon,q)),Sp,Mapsto,Sp,rhs);
        return Disp(All("A",Based(),All("C",Based(),All("D",Based(),All("phi",Call("BPChainMap",A,C),All("psi",Call("BPChainMap",A,Dd),Eq(Call(name,phi,psi),body)))))));
    }
    private static Formula MaxRowFormula() {
        var i=Id("i"); var j=Id("j"); var M=Id("M");
        var row=Call("card",Filter(Lambda("j",Ne(App(M,i,j),D(0))),Univ()));
        return Disp(All("I",Type(),All("K",Type(),Seq(
            Seq(OpenBracket,Call("Fintype",Id("I")),CloseBracket),Sp,
            Seq(OpenBracket,Call("Fintype",Id("K")),CloseBracket),Sp,
            All("M",Matrix(Id("I"),Id("K"),Z2()),Eq(Call("maxRowWeight",M),CallOp("sup",Univ(),Lambda("i",row))))))));
    }
    private static Formula MaxColFormula() {
        var M=Id("M");
        return Disp(All("I",Type(),All("K",Type(),Seq(
            Seq(OpenBracket,Call("Fintype",Id("I")),CloseBracket),Sp,
            Seq(OpenBracket,Call("Fintype",Id("K")),CloseBracket),Sp,
            All("M",Matrix(Id("I"),Id("K"),Z2()),Eq(Call("maxColWeight",M),Call("maxRowWeight",Call("transpose",M))))))));
    }
    private static Formula IsLdpcFormula() {
        var n=Id("n"); var d2=Id("d2w"); var d1=Id("d1w"); var w=Id("w");
        return Disp(All("d2w",Arrow(Nat(),Call("Prod",Nat(),Nat())),All("d1w",Arrow(Nat(),Call("Prod",Nat(),Nat())),Iff(Call("IsLDPC",d2,d1),Exists("w",Nat(),All("n",Nat(),And(Le(Call("fst",App(d2,n)),w),And(Le(Call("snd",App(d2,n)),w),And(Le(Call("fst",App(d1,n)),w),Le(Call("snd",App(d1,n)),w))))))))));
    }
    private static Formula WeightsFormula(string name,string field) {
        var E=Id("E"); return Disp(All("E",Based(),Eq(Call(name,E),Pair(Call("maxRowWeight",Call(field,E)),Call("maxColWeight",Call(field,E))))));
    }
    private static Formula ClaimBody() {
        var A=Id("A"); var C=Id("C"); var Dd=Id("D"); var phi=Id("phi"); var psi=Id("psi"); var n=Id("n");
        Formula family=Arrow(Nat(),Based());
        Formula maps=All("n",Nat(),Call("BPChainMap",App(A,n),App(C,n)));
        Formula mapsD=All("n",Nat(),Call("BPChainMap",App(A,n),App(Dd,n)));
        Formula mon=All("n",Nat(),App(Qualified("BPChainMap", "Monic"),App(phi,n)));
        Formula monD=All("n",Nat(),App(Qualified("BPChainMap", "Monic"),App(psi,n)));
        Formula weights(Formula E, string f) => Call(f, Lambda("n",Call("weights2",App(E,n))), Lambda("n",Call("weights1",App(E,n))));
        Formula q2 = Call("pushoutD2", App(phi, n), App(psi, n));
        Formula q1 = Call("pushoutD1", App(phi, n), App(psi, n));
        Formula out2 = Call("IsLDPC", Lambda("n", Pair(Call("maxRowWeight", q2), Call("maxColWeight", q2))),
            Lambda("n", Pair(Call("maxRowWeight", q1), Call("maxColWeight", q1))));
        return All("A",family,All("C",family,All("D",family,All("phi",maps,All("psi",mapsD,Imp(mon,Imp(monD,Imp(weights(A,"IsLDPC"),Imp(weights(C,"IsLDPC"),Imp(weights(Dd,"IsLDPC"),out2))))))))));
    }
}
