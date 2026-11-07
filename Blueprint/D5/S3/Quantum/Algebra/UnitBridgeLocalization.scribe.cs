using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class UnitBridgeLocalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original square-compatible relation constructs a nonlinear map on the actual evaluation localization, with the ordinary local scalar ring and real residue, skewness, real homogeneity, dot/area, nested NN and saturated H-kernel translation.",
        H("Square denominators for the same original relation"),
        Blocks(
            Paragraph(Text("Keep Original(T), its actual coefficient algebra A, and Raw(E) from the continuous spin geometry. Assume CS on the same D: multiplying the second input by f^2 through the original central Jordan multiplication multiplies the output by f^2, for every f in A and every pair of original inputs. Skewness gives the corresponding first-slot law. No additivity or general A-linearity of D is used.")),
            Paragraph(Text("Fix t in T. S is exactly the submonoid of f in A with f(t) nonzero. LocalVectors is the native module localization S^(-1)(A^3), so equality allows a saturation factor u in S and does not require A to be a domain. A representative x/s is treated as sx/s^2. For u s' x = u s x', multiplication by u s s' gives (u s')^2 sx=(u s)^2 s'x'. Applying the proved first-slot square law to these equal original inputs gives the numerator congruence. The second slot is treated separately. Native quotient lifting then constructs a total nonlinear map on LocalVectors.")),
            Describe.Lean(
                DescribeId.Create("original-square-localization"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/UnitBridgeLocalization.original_localization"),
                H("The complete nonlinear extension over the actual local ring"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The first clause is the square-denominator rule k(x/s^2,y/r^2)=K(x,y)/(s^2 r^2). The second clause is the inherited original NN relation: nesting the same localized map twice gives H_x(y)/(s^4 r^2), where H_x(y)=(x dot y)x-(x dot x)y. It is proved from the original nested K equality, with the intermediate denominator (sr)^2.")),
                    Paragraph(Text("The third clause is a separate kernel-translation statement. For original coefficient vectors x,y,c sharing a denominator q^2, if H_x(c)/q^6 is zero in the actual localization, equality supplies u in S annihilating H_x(c). Multiplying once more by u gives H_x(u^2 c)=0. The original H-kernel translation applied to u^2 y and u^2 c, followed by CS, gives u^2 K(x,y+c)=u^2 K(x,y). This is exactly a native localized equality after the common denominator is restored.")),
                    Paragraph(Text("Every triple of localized vectors has a common square denominator. LocalScalars is the ordinary ring localization S^(-1)A; its module acts on LocalVectors. Evaluation on A is onto the reals because A contains every real constant. Evaluation extends to fractions by ev(f/s)=f(t)/s(t). The fraction f/s is a unit exactly when f(t) is nonzero, and then s/f is an inverse. The scalar localization is a local ring; the kernel of extended evaluation is its maximal ideal, and its residue field is isomorphic to the reals. These facts reuse pinned mathlib localization and quotient results and allow zero divisors in A. LocalCoordinates takes each module fraction x/s to the vector of scalar fractions x_i/s, so localDot is the ordinary dot product over this local ring. The localized H row is localDot(a,b) a-localDot(a,a) b. The same total nonlinear k is skew, real homogeneous in both slots, orthogonal to both arguments, and has squared length localDot(a,a)localDot(b,b)-localDot(a,b)^2. It satisfies k(a,k(a,b))=localH(a,b), and localH(a,c)=0 implies both k(a,b+c)=k(a,b) and k(b+c,a)=k(b,a). The square and common-denominator formulas connect these intrinsic identities with the original raw laws. No point-fibre descent, original inverse or square-root closure, additivity, continuity, orientation, Jacobi law or classification is assumed or concluded. Source 39.2 and 39.3 remain outside this theorem."))),
                DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => global::StrataLint.Scribe.DefinitionDsl.Call(name,args);
    private static Formula N(int n) => global::StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Eq(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Equal(a,b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),domain,body);
    private static Formula Exists(string name,Formula domain,Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(name),domain,body);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Mul(Formula a,Formula b) => global::StrataLint.Scribe.DefinitionDsl.Multiply(a,b);
    private static Formula Sub(Formula a,Formula b) => global::StrataLint.Scribe.DefinitionDsl.Subtract(a,b);
    private static Formula Iff(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Ne(Formula a,Formula b) => new Formula.Logic(Eq(a,b),FormulaLogicOperator.Implies,I("False"));
    private static Formula Conj(params Formula[] a)
    {
        var result=a[^1];
        for(var i=a.Length-2;i>=0;i--) result=And(a[i],result);
        return result;
    }
    private static Formula V => C("Vectors",I("E"));
    private static Formula S => C("evaluationDenominators",I("E"),I("t"));
    private static Formula Frac(Formula x,Formula s,int power) => C("mk",x,C("pow",s,N(power)));
    private static Formula K(Formula x,Formula y) => C("K",I("R"),x,y);
    private static Formula Hop(Formula x,Formula y) => global::StrataLint.Scribe.DefinitionDsl.Subtract(C("smul",C("dot",x,y),x),C("smul",C("dot",x,x),y));
    private static Formula Apply(Formula x,Formula y) => C("k",x,y);
    private static Formula PairScope(Formula b) => All("x",V,All("y",V,All("s",S,All("r",S,b))));
    private static Formula Statement()
    {
        var x=I("x");var y=I("y");var c=I("c");var s=I("s");var r=I("r");var q=I("q");
        var first=PairScope(Eq(Apply(Frac(x,s,2),Frac(y,r,2)),
            C("mk",K(x,y),global::StrataLint.Scribe.DefinitionDsl.Multiply(C("pow",s,N(2)),C("pow",r,N(2))))));
        var nested=PairScope(Eq(Apply(Frac(x,s,2),Apply(Frac(x,s,2),Frac(y,r,2))),
            C("mk",Hop(x,y),global::StrataLint.Scribe.DefinitionDsl.Multiply(C("pow",s,N(4)),C("pow",r,N(2))))));
        var kernel=All("x",V,All("y",V,All("c",V,All("q",S,
            Imp(Eq(Frac(Hop(x,c),q,6),N(0)),Eq(Apply(Frac(x,q,2),Frac(global::StrataLint.Scribe.DefinitionDsl.Add(y,c),q,2)),
                Apply(Frac(x,q,2),Frac(y,q,2))))))));
        var local=C("LocalVectors",I("E"),I("t"));
        var common=All("a",local,All("b",local,All("c",local,
            Exists("x",V,Exists("y",V,Exists("z",V,Exists("q",S,
                And(Eq(I("a"),Frac(I("x"),q,2)),And(Eq(I("b"),Frac(I("y"),q,2)),
                    Eq(I("c"),Frac(I("z"),q,2)))))))))));
        var scalars=C("LocalScalars",I("E"),I("t"));
        var coeff=C("scalarAlgebra",I("E"));
        var f=I("f");var den=I("s");var aa=I("a");var bb=I("b");var cc=I("c");
        Formula Ev(Formula z) => C("localEvaluation",I("E"),I("t"),z);
        Formula Dot(Formula u,Formula v) => C("localDot",I("t"),u,v);
        Formula Hloc(Formula u,Formula v) => C("localH",I("t"),u,v);
        Formula LocalPair(Formula z) => All("a",local,All("b",local,z));
        var inverseFact=All("hf",Ne(C("eval",f,I("t")),N(0)),
            Eq(Mul(C("scalar_mk",f,den),C("scalar_mk",den,C("subtype",f,I("hf")))),N(1)));
        var fractionFacts=All("f",coeff,All("s",S,Conj(
            Eq(Ev(C("scalar_mk",f,den)),C("divide",C("eval",f,I("t")),C("eval",den,I("t")))),
            Iff(C("IsUnit",C("scalar_mk",f,den)),Ne(C("eval",f,I("t")),N(0))),
            inverseFact)));
        var scalarFacts=Conj(
            C("IsLocalRing",scalars),
            C("Surjective",C("coefficientEvaluation",I("E"),I("t"))),
            C("Surjective",C("localEvaluation",I("E"),I("t"))),
            fractionFacts,
            Eq(C("ker",C("localEvaluation",I("E"),I("t"))),C("maximalIdeal",scalars)),
            C("Nonempty",C("RingEquivalences",C("ResidueField",scalars),I("Real"))));
        var skew=LocalPair(Eq(Apply(aa,bb),C("neg",Apply(bb,aa))));
        var homogeneous=LocalPair(All("r",I("Real"),And(
            Eq(Apply(aa,C("smul",r,bb)),C("smul",r,Apply(aa,bb))),
            Eq(Apply(C("smul",r,aa),bb),C("smul",r,Apply(aa,bb))))));
        var geometry=LocalPair(Conj(Eq(Dot(Apply(aa,bb),aa),N(0)),
            Eq(Dot(Apply(aa,bb),bb),N(0)),
            Eq(Dot(Apply(aa,bb),Apply(aa,bb)),Sub(Mul(Dot(aa,aa),Dot(bb,bb)),C("pow",Dot(aa,bb),N(2))))));
        var totalNN=LocalPair(Eq(Apply(aa,Apply(aa,bb)),Hloc(aa,bb)));
        var totalKernel=LocalPair(All("c",local,Imp(Eq(Hloc(aa,cc),N(0)),And(
            Eq(Apply(aa,global::StrataLint.Scribe.DefinitionDsl.Add(bb,cc)),Apply(aa,bb)),
            Eq(Apply(global::StrataLint.Scribe.DefinitionDsl.Add(bb,cc),aa),Apply(bb,aa))))));
        var body=new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("k"),
            C("TotalBinaryMaps",local),Conj(first,nested,kernel,common,scalarFacts,skew,
                homogeneous,geometry,totalNN,totalKernel));
        return All("T",I("TopologicalSpaces"),All("E",C("Original",I("T")),
            All("R",C("Raw",I("E")),All("cs",C("SquareCompatible",I("R")),All("t",I("T"),body)))));
    }
}
