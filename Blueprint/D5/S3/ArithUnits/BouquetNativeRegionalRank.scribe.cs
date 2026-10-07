using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class BouquetNativeRegionalRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every native four-leg region has rank equal to its hit-loop count plus its padded central rank.",
        H("Native Regional Rank on a Bouquet"),
        Blocks(
            Paragraph(Text("Let k and p be natural numbers with 2 <= k < p and p prime. "
                + "Write K = GaloisField(p,2), I = Fin(k), L = Fin(4), and S = Fin(2). "
                + "D is an arbitrary matrix from I times (I times S) to K. "
                + "The selected region R is an arbitrary finite subset of I times L. "
                + "Every rank below is the K-dimension of the image of the displayed linear map. "
                + "The central and loop coordinates lambda and z both belong to I -> K.")),
            Describe.Lean(DescribeId.Create("bouquet-central-forms"), Handle("centralForm"),
                H("Central forms"), StatementSource.FromAuthor(Disp(Seq(
                    Sub("centralForm", Seq(F.Id("D"),Comma,F.Id("j"),Comma,F.Id("s"))),
                    Open,LambdaLower,Close,Eq,Sum,Sp,Underscore,Grp(F.Id("i"),InMacro,Sp,Fin("k")),
                    C("D",F.Id("i"),Pair(F.Id("j"),F.Id("s"))),Cdot,Sub(LambdaLower,F.Id("i")),
                    Quad,Sp,F.Id("a"),Underscore,Grp(F.Id("j")),Eq,C("centralForm",F.Id("D"),F.Id("j"),D(0)),
                    Comma,Quad,Sp,F.Id("b"),Underscore,Grp(F.Id("j")),Eq,C("centralForm",F.Id("D"),F.Id("j"),D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each loop has two central linear forms, using the two columns indexed by (j,0) and (j,1)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bouquet-hit-loops"), Handle("hitLoops"),
                H("Selected loops"), StatementSource.FromAuthor(Disp(Seq(
                    Sub("R",F.Id("j")),Eq,OpenBrace,Ell,InMacro,Sp,Fin("4"),Mid,Sp,
                    Pair(F.Id("j"),Ell),InMacro,Sp,F.Id("R"),CloseBrace,Comma,Quad,Sp,
                    C("hitLoops",F.Id("R")),Eq,F.Id("J"),Eq,OpenBrace,F.Id("j"),InMacro,Sp,Fin("k"),Mid,Sp,
                    Sub("R",F.Id("j")),Neq,Sp,Emptyset,CloseBrace,Comma,Quad,Sp,
                    Sub("H",F.Id("R")),Eq,Bar,F.Id("J"),Bar))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A loop is hit exactly when at least one of its four actual rows belongs to R."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bouquet-actual-map"), Handle("actualMap"),
                H("Actual selected map"), StatementSource.FromAuthor(Disp(Seq(
                    Sub("F",F.Id("R")),Eq,C("actualMap",F.Id("D"),F.Id("R")),Colon,
                    Pow(F.Id("K"),F.Id("I")),Times,Sp,Pow(F.Id("K"),F.Id("I")),To,Sp,Pow(F.Id("K"),F.Id("R")),
                    Comma,Quad,Sp,Sub("F",F.Id("R")),Open,LambdaLower,Comma,F.Id("z"),Close,Eq,
                    Open,Sub("a",F.Id("j")),Open,LambdaLower,Close,Plus,Sub("z",F.Id("j")),Comma,
                    Sub("a",F.Id("j")),Open,LambdaLower,Close,Minus,Sub("z",F.Id("j")),Comma,
                    Sub("b",F.Id("j")),Open,LambdaLower,Close,Plus,Sub("z",F.Id("j")),Comma,
                    Sub("b",F.Id("j")),Open,LambdaLower,Close,Minus,Sub("z",F.Id("j")),Close,
                    Underscore,Grp(F.Id("j"),InMacro,Sp,F.Id("I")),Bar,Underscore,Grp(F.Id("R"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four entries in each loop are indexed by 0,1,2,3 in that order. "
                    + "The map keeps exactly the coordinates in R; its domain contains both central and loop variables."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bouquet-padded-central-map"), Handle("virtualMap"),
                H("Padded central map"), StatementSource.FromAuthor(Disp(Seq(
                    Sub("V",F.Id("R")),Eq,C("virtualMap",F.Id("D"),F.Id("R")),Colon,
                    Pow(F.Id("K"),F.Id("I")),To,Sp,Pow(F.Id("K"),Seq(F.Id("I"),Times,Sp,F.Id("S"))),Comma,Quad,Sp,
                    Sub("V",F.Id("R")),Open,LambdaLower,Close,Underscore,Grp(F.Id("j")),Eq,
                    Begin,Grp(F.Id("cases")),
                    Pair(D(0),D(0)),Amp,Bar,Sub("R",F.Id("j")),Bar,Le,Sp,D(1),RowBreak,
                    Pair(A,Bzero),Amp,Sub("R",F.Id("j")),Eq,Mask(0,1),RowBreak,
                    Pair(B,Bzero),Amp,Sub("R",F.Id("j")),Eq,Mask(2,3),RowBreak,
                    Pair(Seq(A,Minus,B),Bzero),Amp,Sub("R",F.Id("j")),InMacro,Sp,OpenBrace,Mask(0,2),Comma,Mask(1,3),CloseBrace,RowBreak,
                    Pair(Seq(A,Plus,B),Bzero),Amp,Sub("R",F.Id("j")),InMacro,Sp,OpenBrace,Mask(0,3),Comma,Mask(1,2),CloseBrace,RowBreak,
                    Pair(A,B),Amp,Bar,Sub("R",F.Id("j")),Bar,Ge,Sp,D(3),
                    End,Grp(F.Id("cases"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here a and b in the table denote a_j(lambda) and b_j(lambda). "
                    + "Each block has two slots indexed by S, including the displayed zero padding. "
                    + "The six two-leg masks are handled individually and yield the four central constraints shown in the table."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bouquet-native-regional-rank"), Handle("native_regional_rank"),
                H("Native regional rank identity"), StatementSource.FromAuthor(Disp(Seq(
                    Forall,Sp,F.Id("k"),Comma,F.Id("p"),InMacro,Sp,Mathbb,Grp(F.Id("N")),Comma,Sp,
                    D(2),Le,Sp,F.Id("k"),Lt,F.Id("p"),Land,Sp,C("Prime",F.Id("p")),Implies,Sp,
                    Forall,Sp,F.Id("D"),Colon,C("Matrix",Fin("k"),Seq(Fin("k"),Times,Sp,Fin("2")),C("GaloisField",F.Id("p"),D(2))),Comma,
                    Forall,Sp,F.Id("R"),Colon,C("Finset",Seq(Fin("k"),Times,Sp,Fin("4"))),Comma,Quad,Sp,
                    C("finrank",C("GaloisField",F.Id("p"),D(2)),C("range",C("actualMap",F.Id("D"),F.Id("R")))),Eq,
                    C("card",C("hitLoops",F.Id("R"))),Plus,
                    C("finrank",C("GaloisField",F.Id("p"),D(2)),C("range",C("virtualMap",F.Id("D"),F.Id("R"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An anchor is chosen from each hit loop using only R. "
                    + "Multiplying a row by its sign gives a central signed value plus z_j. "
                    + "Subtracting the anchor central value defines W_R. The kernel of F_R is linearly "
                    + "equivalent to the kernel of W_R times the functions on unhit loops: "
                    + "the forward map keeps lambda and the free loop coordinates, and the inverse "
                    + "sets each hit z_j to minus its signed anchor value. "
                    + "The table gives exactly the same central kernel as W_R, because 2 is nonzero in K. "
                    + "Rank-nullity on K^I times K^I proves the identity.")),
                    Paragraph(Text("The assertion includes zero and dependent D, empty and full R, single rows, "
                    + "and k=2,p=3. It uses no injectivity, prescribed rank, or kernel equality assumption. "
                    + "Support, entropy, virtual-rank saturation, RT equivalence, and converse statements require separate assertions."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create("D5/S3/ArithUnits/BouquetNativeRegionalRank." + name);
    private static Formula C(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [..args]);
    private static Formula Fin(string n) => C("Fin", n == "k" ? F.Id("k") : n == "2" ? D(2) : D(4));
    private static Formula Sub(string name, Formula index) => Sub(F.Id(name),index);
    private static Formula Sub(Formula name, Formula index) => Seq(name,Underscore,Grp(index));
    private static Formula Pair(Formula a, Formula b) => Seq(Open,a,Comma,b,Close);
    private static Formula Pow(Formula a, Formula b) => Seq(a,Caret,Grp(b));
    private static Formula Mask(byte a, byte b) => Seq(OpenBrace,D(a),Comma,D(b),CloseBrace);
    private static Formula A => Seq(Sub("a",F.Id("j")),Open,LambdaLower,Close);
    private static Formula B => Seq(Sub("b",F.Id("j")),Open,LambdaLower,Close);
    private static Formula Bzero => D(0);
}
