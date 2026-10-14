using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class OriginalPiecesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OriginalPieces.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name),type);
    private static Formula All(Formula body, params Formula.BoundVariable[] vars) => new Formula.BindMany(FormulaQuantifier.ForAll,[.. vars],body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] vars) => new Formula.BindMany(FormulaQuantifier.Exists,[.. vars],body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula And(params Formula[] xs)
    {
        var r=xs[^1]; for(var i=xs.Length-2;i>=0;--i) r=new Formula.Logic(xs[i],FormulaLogicOperator.And,r); return r;
    }
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Nat => I("Nat");
    private static Formula Real => I("Real");
    private static Formula List(Formula a) => Call("List",a);
    private static Formula Ap(Formula a, Formula b) => Call("apply",a,b);
    private static Formula Add(Formula a, Formula b) => Call("add",a,b);
    private static Formula Len(Formula a) => Call("length",a);
    private static Formula At(Formula a, Formula p) => Call("getElem",a,p);
    private static Formula Mem(Formula a, Formula s) => Call("member",a,s);
    private static Formula Carrier(Formula piece) => Call("carrier",piece);
    private static Formula Piece(Formula path, Formula p) => Ap(Call("pieces",path),p);
    private static Formula GuardAt(Formula path, Formula p) => Ap(Call("guards",path),p);
    private static Formula PieceFields(Formula lo, Formula hi, Formula s) => And(
        Mem(lo,I("endpoints")),Mem(hi,I("endpoints")),Call("le",lo,hi),Call("InSupport",s,lo),Call("InSupport",s,hi),
        All(Imp(Mem(I("z"),I("endpoints")),Call("not",And(Call("lt",lo,I("z")),Call("lt",I("z"),hi)))),B("z",Real)));
    private static Formula PieceDefinition() => Disp(All(Iff(
        Call("OriginalPieceFields",I("endpoints"),I("s"),I("lo"),I("hi")),PieceFields(I("lo"),I("hi"),I("s"))),
        B("endpoints",Call("Finset",Real)),B("s",I("Guard")),B("lo",Real),B("hi",Real)));
    private static Formula CarrierDefinition() => Disp(All(Iff(Mem(I("z"),Carrier(I("P"))),
        And(Call("le",Call("lo",I("P")),I("z")),Call("le",I("z"),Call("hi",I("P"))))),
        B("endpoints",Call("Finset",Real)),B("s",I("Guard")),B("P",Call("OriginalPiece",I("endpoints"),I("s"))),B("z",Real)));
    private static Formula PathContract(Formula path, Formula a, Formula terminal)
    {
        var p=I("p");var next=Add(p,D(1));var label=At(a,p);
        var root=All(Imp(Mem(I("z"),Carrier(Piece(path,p))),Ex(And(Call("InSupport",GuardAt(path,next),I("y")),
            Equal(I("z"),Call("branch",label,I("y")))),B("y",Real))),B("z",Real));
        var full=All(Imp(Mem(I("y"),Carrier(Piece(path,next))),Mem(Call("branch",label,I("y")),Carrier(Piece(path,p)))),B("y",Real));
        return And(Equal(GuardAt(path,D(0)),I("G0")),Equal(GuardAt(path,Len(a)),I("s")),
            Equal(Carrier(Piece(path,Len(a))),Carrier(terminal)),
            All(Call("hasType",Piece(path,p),Call("OriginalPiece",I("endpoints"),GuardAt(path,p))),B("p",Nat)),
            All(Imp(Call("lt",p,Len(a)),And(Equal(Call("nextGuard",GuardAt(path,p),label),Call("some",GuardAt(path,next))),root,full)),B("p",Nat)));
    }
    private static Formula PathDefinition() => Disp(All(Iff(Call("OriginalPiecePathFields",I("route"),I("endpoints"),I("A"),I("s"),I("P2")),
        PathContract(I("route"),I("A"),I("P2"))),B("endpoints",Call("Finset",Real)),B("A",List(I("Label"))),B("s",I("Guard")),
        B("P2",Call("OriginalPiece",I("endpoints"),I("s"))),B("route",Call("PathRecord"))));
    private static Formula SuffixStatement()
    {
        var p=I("p");var pieces=I("pieces");var a=I("A");
        var edges=All(Imp(And(Call("lt",p,Len(a)),Mem(I("y"),Ap(pieces,Add(p,D(1))))),
            Mem(Call("branch",At(a,p),I("y")),Ap(pieces,p))),B("p",Nat),B("y",Real));
        var result=All(Imp(Call("le",p,Len(a)),Mem(Call("compose",Call("drop",a,p),I("z")),Ap(pieces,p))),B("p",Nat));
        return Disp(All(Imp(And(Mem(I("z"),Ap(pieces,Len(a))),edges),result),B("A",List(I("Label"))),
            B("pieces",Fn(Nat,Call("Set",Real))),B("z",Real)));
    }
    private static Formula TailPath(Formula s, Formula a, Formula x, Formula q)
    {
        var p=I("p");var next=Add(p,D(1));
        return And(Equal(Ap(q,D(0)),s),All(Equal(Call("nextGuard",Ap(q,p),Ap(a,p)),Call("some",Ap(q,next))),B("p",Nat)),
            All(Call("InSupport",Ap(q,p),Ap(x,p)),B("p",Nat)),
            All(Equal(Ap(x,p),Call("branch",Ap(a,p),Ap(x,next))),B("p",Nat)));
    }
    private static Formula A => Call("append",I("Q"),Call("choiceBlocks",Call("constantWordFamily",I("V")),I("zs")));
    private static Formula Cs => Call("append",I("h"),Call("choiceBlocks",I("W"),I("zs")));
    private static Formula T => Call("CompetingT",I("o"),I("theta"),I("s"),I("Q"),I("V"),I("h"),I("W"));
    private static Formula Orbit(Formula z) => All(Mem(Call("iterateApply",Call("composeMap",I("V")),I("n"),z),T),B("n",Nat));
    private static Formula SelectedStatement()
    {
        var p=I("p");var route=Ap(I("paths"),I("zs"));var seam=Add(Len(A),p);
        var input=And(Call("le",D(0),I("theta")),Call("LegalWord",I("G0"),I("s"),I("Q")),Call("LegalWord",I("s"),I("s"),I("V")),
            Equal(Len(I("Q")),Len(I("h"))),All(Equal(Len(I("V")),Len(Ap(I("W"),I("i")))),B("i",I("Bool"))),
            Ex(And(Orbit(I("z")),Mem(I("z"),Carrier(I("P2")))),B("z",Real)),
            All(PathContract(route,A,I("P2")),B("zs",List(I("Bool")))));
        var lifted=Ex(And(TailPath(I("G0"),I("beta"),I("X"),I("q")),
            All(Imp(Call("lt",p,Len(A)),Equal(Ap(I("beta"),p),At(A,p))),B("p",Nat)),
            All(And(Equal(Ap(I("beta"),seam),Ap(I("tail"),p)),Equal(Ap(I("X"),seam),Ap(I("x"),p)),
                Equal(Ap(I("q"),seam),Ap(I("path"),p))),B("p",Nat)),
            All(Imp(Call("le",p,Len(A)),And(Mem(Ap(I("X"),p),Carrier(Piece(route,p))),Equal(Ap(I("q"),p),GuardAt(route,p)))),B("p",Nat)),
            Call("OperationRecord",I("o"),I("theta"),I("closed"),I("beta"),Call("recordWithOmegaTail",I("o"),Cs,I("x")))),
            B("beta",Fn(Nat,I("Label"))),B("X",Fn(Nat,Real)),B("q",Fn(Nat,I("Guard"))));
        var result=Ex(And(TailPath(I("s"),I("tail"),I("x"),I("path")),Mem(Ap(I("x"),D(0)),Carrier(I("P2"))),
            Orbit(Ap(I("x"),D(0))),All(lifted,B("zs",List(I("Bool"))))),B("tail",Fn(Nat,I("Label"))),B("x",Fn(Nat,Real)),B("path",Fn(Nat,I("Guard"))));
        return Disp(All(Imp(input,result),B("o",I("Ownership")),B("theta",Real),B("s",I("Guard")),B("Q",List(I("Label"))),
            B("V",List(I("Label"))),B("h",List(I("Color"))),B("W",Fn(I("Bool"),List(I("Color")))),B("endpoints",Call("Finset",Real)),
            B("P2",Call("OriginalPiece",I("endpoints"),I("s"))),B("paths",Call("DependentPathFamily",I("endpoints"),I("Q"),I("V"),I("s"),I("P2")))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One competing scalar and tail realize every finite history inside the specified original pieces.",H("Original pieces and a fixed competing tail"),Blocks(
        Describe.Lean(DescribeId.Create("fib-original-piece"),DeclarationHandle.Create(Prefix+"OriginalPiece"),H("Typed original closed pieces"),
            StatementSource.FromAuthor(PieceDefinition()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("A piece has ordered endpoints in the same finite endpoint set, both in its actual guard support. No endpoint of that set lies strictly between them. Equal endpoints retain every singleton; unequal endpoints give the entire interval between consecutive endpoints. OriginalPieceFields is exactly the displayed condition on its lo and hi fields."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("fib-original-piece-carrier"),DeclarationHandle.Create(Prefix+"piece_carrier"),H("The entire closed carrier"),
            StatementSource.FromAuthor(CarrierDefinition()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("The carrier includes both endpoints and every intermediate scalar. A singleton is the closed interval with equal endpoints."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("fib-original-piece-path"),DeclarationHandle.Create(Prefix+"OriginalPiecePath"),H("Full original piece paths"),
            StatementSource.FromAuthor(PathDefinition()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("PathRecord has a guard sequence and a piece of that guard at each position. The initial guard is G0; at the prefix length the guard and carrier are the specified terminal piece. Each prefix edge has its actual nextGuard transition, its whole source carrier in the legal branch root domain, and the image of the whole target carrier inside the source carrier. OriginalPiecePathFields expands exactly these requirements. Positions after the terminal index are unused."))),DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("fib-original-piece-suffix-membership"),DeclarationHandle.Create(Prefix+"original_piece_suffix_membership"),H("Joint transport from one terminal scalar"),
            StatementSource.FromAuthor(SuffixStatement()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("Backward transport through full-containing edges puts every suffix coordinate of the same scalar in its corresponding piece. The terminal index is included, and an empty prefix retains the selected scalar without an edge."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("fib-selected-original-piece-tail"),DeclarationHandle.Create(Prefix+"selected_original_piece_tail"),H("A selected actual tail and all original prefixes"),
            StatementSource.FromAuthor(SelectedStatement()),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("K is the set of scalars whose every iterate under compose(V) lies in CompetingT. The nonempty intersection K with the specified P2 selects the scalar once. A lawful tail supplies its literal labels, coordinates and guards, fixed before every finite Boolean history. Both original color words are retained even though V is identical. DependentPathFamily supplies one full original path for each Q followed by the selected copies of V, ending at that same P2 in the same endpoint set.")),
                Paragraph(Text("Each actual source retains every prescribed prefix label. At the seam and every later position its label, coordinate and guard agree with the fixed tail. At every prefix index, including the seam, the coordinate belongs to the whole original carrier and the guard is the specified original guard. BlockSupply supplies bounded actual errors in the observed past; future errors are zero on the same source. This finite path lift assumes the specified original paths and does not construct their endpoint set or infer bilateral auxiliary realizations or a decoder upper bound."))),DescribeRole.Theorem))));
}
