using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class RationalSTCutCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/RationalSTCutCertificate.";
    private static Formula Cap => V("capacity");
    private static Formula Src => V("source");
    private static Formula Snk => V("sink");
    private static Formula K => V("certificate");
    private static Formula X => V("side");
    private static Formula I => V("i");
    private static Formula J => V("j");
    private static Formula FIJ => C("internal", K, I, J);
    private static Formula FS => C("fromSource", K, I);
    private static Formula FT => C("toSink", K, I);
    private static Formula CX(Formula side) => C("stCutValue", Cap, Src, Snk, side);
    private static Formula FV => C("flowValue", K);
    private static Formula PositiveInternal => All("i j", And(B(Z,Le,FIJ), B(FIJ,Le,C("capacity",I,J))));
    private static Formula SourceUpper => All("i", B(FS,Le,C("source",I)));
    private static Formula SinkUpper => All("i", B(FT,Le,C("sink",I)));
    private static Formula Conservation => All("i", B(B(FS,Plus,SumF("j",C("internal",K,J,I))),Eq,
        B(FT,Plus,SumF("j",FIJ))));
    private static Formula Valid => C("ValidSTCutCertificate", Cap, Src, Snk, K);
    private static Formula Checked => B(C("checkSTCutCertificate",Cap,Src,Snk,K),Eq,V("true"));
    private static Formula Bit(Formula i) => C("ite",C("apply",X,i),One,Z);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact flow conservation and capacity checks certify a global minimum cut.", H("RationalSTCutCertificate"), Blocks(
            Paragraph(Text("Vertex is an arbitrary finite type. capacity is Vertex to Vertex to Q; source and sink are Vertex to Q; side is Vertex to Bool. All sums cover the entire finite carrier. True labels are on the source side.")),
            Describe.Lean(DescribeId.Create("stCutValue"), DeclarationHandle.Create(Prefix + "stCutValue"),
                H("Directed cut energy"), StatementSource.FromAuthor(Disp(All("Vertex capacity source sink side", B(CX(X),Eq,B(SumF("i",C("ite",C("apply",X,I),C("sink",I),C("source",I))),Plus,SumF("i",SumF("j",C("ite",And(B(C("apply",X,I),Eq,V("true")),B(C("apply",X,J),Eq,V("false"))),C("capacity",I,J),Z)))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source is fixed on the true side and the sink on the false side. All vertex assignments are allowed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("STCutCertificate"), DeclarationHandle.Create(Prefix + "STCutCertificate"),
                H("Untrusted flow and cut data"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fields are internal : Vertex to Vertex to Q; fromSource and toSink : Vertex to Q; side : Vertex to Bool. No proof or claimed optimality field is supplied."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("flowValue"), DeclarationHandle.Create(Prefix + "flowValue"),
                H("Value leaving the source"), StatementSource.FromAuthor(Disp(All("Vertex certificate", B(FV,Eq,SumF("i",FS))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The flow value is recomputed from terminal flows."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ValidSTCutCertificate"), DeclarationHandle.Create(Prefix + "ValidSTCutCertificate"),
                H("Capacity, conservation and equality"), StatementSource.FromAuthor(Disp(All("Vertex capacity source sink certificate", B(Valid,Leftrightarrow,And(PositiveInternal,All("i",And(B(Z,Le,FS),B(FS,Le,C("source",I)))),All("i",And(B(Z,Le,FT),B(FT,Le,C("sink",I)))),Conservation,B(CX(C("side",K)),Eq,FV)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each capacity condition and each conservation equation is checked on the actual finite arrays; the supplied cut must match the flow value."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checkSTCutCertificate"), DeclarationHandle.Create(Prefix + "checkSTCutCertificate"),
                H("Executable exact check"), StatementSource.FromAuthor(Disp(All("Vertex capacity source sink certificate", B(C("checkSTCutCertificate",Cap,Src,Snk,K),Eq,C("decide",Valid))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("No floating acceptance tolerance or exhaustive Boolean search is used by the checker."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("checkSTCutCertificate_eq_true_iff"), DeclarationHandle.Create(Prefix + "checkSTCutCertificate_eq_true_iff"),
                H("Acceptance reflection"), StatementSource.FromAuthor(Disp(All("Vertex capacity source sink certificate", B(Checked,Leftrightarrow,Valid)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Connects Boolean acceptance to the exact finite arithmetic contract."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("flow_cut_accounting"), DeclarationHandle.Create(Prefix + "flow_cut_accounting"),
                H("Conservation across any cut"), StatementSource.FromAuthor(Disp(All("Vertex certificate side", B(Conservation,Rightarrow,B(FV,Eq,B(SumF("i",C("ite",C("apply",X,I),FT,FS)),Plus,SumF("i",SumF("j",B(FIJ,Cdot,B(Bit(I),Minus,Bit(J))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only flow conservation is required by this identity. Opposite directed terms cancel when summing over all vertices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("flowValue_le_every_cut"), DeclarationHandle.Create(Prefix + "flowValue_le_every_cut"),
                H("Global weak flow-cut duality"), StatementSource.FromAuthor(Disp(All("Vertex capacity source sink certificate side", B(And(PositiveInternal,SourceUpper,SinkUpper,Conservation),Rightarrow,B(FV,Le,CX(X)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The lower bound covers every cut, including those never visited by a solver."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("checkSTCutCertificate_sound"), DeclarationHandle.Create(Prefix + "checkSTCutCertificate_sound"),
                H("Attained minimum certificate"), StatementSource.FromAuthor(Disp(All("Vertex capacity source sink certificate", B(Checked,Rightarrow,And(B(CX(C("side",K)),Eq,FV),All("side",B(FV,Le,CX(X)))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A single accepted pair proves that its cut is a global minimum; no optimal flow premise or algorithmic discovery theorem is assumed."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Z => F.D(0);
    private static Formula One => F.D(1);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula B(Formula x, Formula op, Formula y) => Seq(P(x), Sp, op, Sp, P(y));
    private static Formula All(string names, Formula body) => Quantify(Forall, names, body);
    private static Formula ExistsF(string names, Formula body) => Quantify(Exists, names, body);
    private static Formula Lam(string names, Formula body) => Quantify(LambdaLower, names, body);
    private static Formula SumF(string index, Formula body) => Seq(F.Sum, Underscore, Grp(V(index)), Sp, P(body));
    private static Formula Quantify(Formula q, string names, Formula body)
    {
        var a = new List<Formula> { q, Sp };
        foreach (var name in names.Split(' ')) a.AddRange([V(name), Comma, Sp]);
        a.Add(body); return Seq([.. a]);
    }
    private static Formula And(params Formula[] xs)
    {
        var a = new List<Formula>();
        for (var k=0; k<xs.Length; k++) { if (k>0) a.AddRange([Sp,Land,Sp]); a.Add(P(xs[k])); }
        return Seq([.. a]);
    }
    private static Formula C(string name, params Formula[] xs)
    {
        var a = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var k=0; k<xs.Length; k++) { if (k>0) a.AddRange([Comma,Sp]); a.Add(xs[k]); }
        a.Add(Close); return Seq([.. a]);
    }
}
