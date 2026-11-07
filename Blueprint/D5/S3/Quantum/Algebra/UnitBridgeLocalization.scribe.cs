using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class UnitBridgeLocalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original square-compatible relation constructs a nonlinear map on the actual evaluation localization, with inherited nested NN and saturated H-kernel translation.",
        H("Square denominators for the same original relation"),
        Blocks(
            Paragraph(Text("Keep Original(T), its actual coefficient algebra A, and Raw(E) from the continuous spin geometry. Assume CS on the same D: multiplying the second input by f^2 through the original central Jordan multiplication multiplies the output by f^2, for every f in A and every pair of original inputs. Skewness gives the corresponding first-slot law. No additivity or general A-linearity of D is used.")),
            Paragraph(Text("Fix t in T. S is exactly the submonoid of f in A with f(t) nonzero. LocalVectors is the native module localization S^(-1)(A^3), so equality allows a saturation factor u in S and does not require A to be a domain. A representative x/s is treated as sx/s^2. For u s' x = u s x', multiplication by u s s' gives (u s')^2 sx=(u s)^2 s'x'. Applying the proved first-slot square law to these equal original inputs gives the numerator congruence. The second slot is treated separately. Native quotient lifting then constructs a total nonlinear map on LocalVectors.")),
            Describe.Lean(
                DescribeId.Create("original-square-localization"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/UnitBridgeLocalization.original_localization"),
                H("A nonlinear extension with two inherited relations"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The first clause is the square-denominator rule k(x/s^2,y/r^2)=K(x,y)/(s^2 r^2). The second clause is the inherited original NN relation: nesting the same localized map twice gives H_x(y)/(s^4 r^2), where H_x(y)=(x dot y)x-(x dot x)y. It is proved from the original nested K equality, with the intermediate denominator (sr)^2.")),
                    Paragraph(Text("The third clause is a separate kernel-translation statement. For original coefficient vectors x,y,c sharing a denominator q^2, if H_x(c)/q^6 is zero in the actual localization, equality supplies u in S annihilating H_x(c). Multiplying once more by u gives H_x(u^2 c)=0. The original H-kernel translation applied to u^2 y and u^2 c, followed by CS, gives u^2 K(x,y+c)=u^2 K(x,y). This is exactly a native localized equality after the common denominator is restored.")),
                    Paragraph(Text("The stated clauses quantify over all original numerator vectors and all denominators in S. A fourth clause gives a common square denominator for every triple of actual localized vectors, so the kernel clause applies to arbitrary triples after choosing these representatives. The statement does not assert the local-ring unit criterion, residue-field identification, or inherited localized skewness, real homogeneity and dot-area identities. Those additional localization properties, local plane orientation and the full original classification require further statements."))),
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
        var body=new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("k"),
            C("TotalBinaryMaps",local),And(first,And(nested,And(kernel,common))));
        return All("T",I("TopologicalSpaces"),All("E",C("Original",I("T")),
            All("R",C("Raw",I("E")),All("cs",C("SquareCompatible",I("R")),All("t",I("T"),body)))));
    }
}
