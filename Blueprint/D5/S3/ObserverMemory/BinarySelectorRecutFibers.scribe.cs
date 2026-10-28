using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory;

internal sealed class BinarySelectorRecutFibersDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => DefinitionDsl.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a,b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Not(Formula a) => Seq(Neg,Grp(a));
    private static Formula LeqOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LtOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Call("pair", a, b);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [..args]);
    private static Formula Range(string x, Formula domain, Formula value) =>
        new Formula.SetBuilder(value, V(x), domain);
    private static Formula Card(Formula a) => Call("card", a);
    private static Formula Member(Formula a, Formula b) => Call("Member", a, b);
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula Len(Formula a) => Call("length", a);
    private static Formula Singleton(Formula a) => new Formula.SetLiteral([a]);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Cat(Formula a, Formula b) => Call("concat", a, b);
    private static Formula W(Formula m) => Call("Word", m);
    private static Formula P(Formula m) => Call("Point", m);
    private static Formula C(Formula m) => Call("relation", m);
    private static Formula Q(Formula m, Formula d) => Call("image", C(m), Add(Multiply(Num(2),m),Num(1)), d);
    private static Formula B(Formula m, Formula s) => Call("boundary", C(m), s);
    private static Formula A(Formula m, Formula s) => Call("actual", C(m), s);
    private static Formula R(Formula m, Formula u) => Call("residual", C(m), u);
    private static Formula S(Formula i, Formula j) => Call("predecessor", i, j);
    private static Formula L(Formula m, Formula s) => Call("legal", Add(Multiply(Num(3),m),Num(1)),C(m),s);
    private static Formula N => V("Nat");
    private static Formula Words => Call("List", V("Bool"));
    private static Formula States => Seq(Words, Sp, Times, Sp, Words);
    private static Formula M(Formula m) => Pow(Num(2),m);
    private static Formula Fine(Formula p) => Call("fine",p);
    private static Formula Sel(Formula p) => Call("selected",p);
    private static Formula Rebuild(Formula x, Formula b, Formula y) => Call("rebuild",x,b,y);
    private static Formula Prefix(Formula p) => Call("selectorPrefix",p);
    private static Formula State(Formula p) => Call("state",p);
    private static Formula Derivative(Formula b, Formula language) => Call("derivative",b,language);

    private static Formula ClassificationStatement()
    {
        var m=V("m"); var i=V("i"); var j=V("j"); var b=V("b");
        var u=V("u"); var f=V("f"); var p=V("p"); var x=V("x"); var w=V("w"); var ij=V("ij");
        var anchor=Cat(Val(i),Val(j));
        var originals=All("w",Words,IffOf(Member(w,C(m)),Some("i",W(m),Some("j",W(m),
            Or(Equal(w,Cat(anchor,Call("cons",V("false"),Val(i)))),
               Equal(w,Cat(anchor,Call("cons",V("true"),Val(j)))))))));
        var fixedLength=All("f",Words,Imp(Member(f,C(m)),Equal(Len(f),Add(Multiply(Num(3),m),Num(1)))));
        Formula ActualPrefix(Formula z) => Some("f",Words,Member(Cat(z,f),C(m)));
        var previous=All("u",Words,Imp(Equal(Len(u),Multiply(Num(2),m)),
            IffOf(ActualPrefix(u),Some("i",W(m),Some("j",W(m),Equal(u,anchor))))));
        var current=All("u",Words,Imp(Equal(Len(u),Add(Multiply(Num(2),m),Num(1))),
            IffOf(ActualPrefix(u),Some("p",P(m),Equal(u,Prefix(p))))));
        var branch=All("i",W(m),All("j",W(m),And(Equal(R(m,anchor),S(i,j)),
            All("b",V("Bool"),Equal(Derivative(Call("singleList",b),S(i,j)),
                Singleton(Val(Sel(Pair(Pair(i,j),b)))))))));
        var distinct=Call("Injective",Call("predecessorMap",m));
        var realized=All("p",P(m),And(A(m,State(p)),Equal(R(m,Prefix(p)),Singleton(Val(Sel(p)))),
            Equal(B(m,State(p)),Fine(p))));
        var rsPrevious=Call("residualSet",C(m),Multiply(Num(2),m));
        var rsCurrent=Call("residualSet",C(m),Add(Multiply(Num(2),m),Num(1)));
        var predecessorRange=Range("ij",Seq(W(m),Sp,Times,Sp,W(m)),S(Call("fst",ij),Call("snd",ij)));
        var singletonRange=Range("x",W(m),Singleton(Val(x)));
        return All("m",N,And(originals,Call("Nonempty",C(m)),fixedLength,
            Equal(Card(C(m)),Multiply(Num(2),Pow(M(m),Num(2)))),previous,current,branch,distinct,realized,
            Equal(rsPrevious,predecessorRange),Equal(Card(rsPrevious),Pow(M(m),Num(2))),
            Equal(rsCurrent,singletonRange),
            Equal(Q(m,Num(0)),Range("x",W(m),Pair(Singleton(Val(x)),Call("nil")))),
            Equal(Q(m,Num(1)),Range("p",P(m),Fine(p)))));
    }

    private static Formula WidthStatement()
    {
        var m=V("m"); var x=V("x"); var b=V("b"); var y=V("y"); var z=V("z");
        var s=V("s"); var t=V("t"); var a=V("a"); var g=V("g"); var h=V("h"); var byPair=V("byPair");
        var current=Call("currentFiber",m,x); var fixedBit=Call("fixedBitFiber",m,x,b);
        var fibers=All("x",W(m),And(
            Equal(current,Range("byPair",Seq(V("Bool"),Sp,Times,Sp,W(m)),
                Fine(Rebuild(x,Call("fst",byPair),Call("snd",byPair))))),
            Equal(Card(current),Multiply(Num(2),M(m))),
            All("b",V("Bool"),And(Equal(fixedBit,Range("y",W(m),Fine(Rebuild(x,b,y)))),
                Equal(Card(fixedBit),M(m))))));
        var kernel=All("s",States,All("t",States,Imp(And(A(m,s),A(m,t),
            Equal(Call("publicType",s),Call("publicType",t))),IffOf(Equal(L(m,s),L(m,t)),Equal(B(m,s),B(m,t))))));
        var typed=Call("typedState",C(m),Add(Multiply(Num(2),m),Num(1)),Num(1));
        var represented=Range("s",typed,At(a,s));
        Formula FactorLaw(Formula factor) => And(All("s",typed,Equal(At(factor,At(a,s)),B(m,s))),
            Call("Surjective",factor),LeqOf(Multiply(Num(2),Pow(M(m),Num(2))),Card(represented)));
        var minimum=All("X",V("Type"),All("a",Arrow(States,V("X")),
            Imp(Call("Exact",Add(Multiply(Num(3),m),Num(1)),C(m),a),
                Some("g",Arrow(represented,Q(m,Num(1))),And(FactorLaw(g),
                    All("h",Arrow(represented,Q(m,Num(1))),Imp(FactorLaw(h),Equal(h,g))))))));
        var transitions=All("s",States,All("a",Call("Action",V("Bool")),Imp(A(m,s),Equal(
            Call("mapTypeBoundary",C(m),Call("step",Add(Multiply(Num(3),m),Num(1)),C(m),s,a)),
            Call("boundaryStep",Add(Multiply(Num(3),m),Num(1)),Call("publicType",s),B(m,s),a)))));
        return All("m",N,Imp(LeqOf(Num(1),m),And(Equal(Card(Q(m,Num(0))),M(m)),
            Equal(Card(Q(m,Num(1))),Multiply(Num(2),Pow(M(m),Num(2)))),
            Equal(new Formula.Fraction(Card(Q(m,Num(1))),Card(Q(m,Num(0)))),Multiply(Num(2),M(m))),
            fibers,kernel,minimum,transitions,
            All("X",V("Type"),All("a",Arrow(States,V("X")),
                Imp(Call("Exact",Add(Multiply(Num(3),m),Num(1)),C(m),a),
                    LeqOf(M(m),Card(Range("s",Call("typedState",C(m),Add(Multiply(Num(2),m),Num(1)),Num(0)),At(a,s))))))))));
    }

    private static Formula SupplementsStatement()
    {
        var m=V("m"); var z=V("Z"); var l=V("L"); var r=V("R"); var p=V("p");
        var i=V("i"); var j=V("j"); var ell=V("ell"); var label=Call("label",p);
        Formula Joint(bool bit) => bit ? Pair(Pair(Sel(p),Call("snd",p)),At(l,p)) : Pair(Sel(p),At(l,p));
        Formula Readout(bool bit) => bit ? Seq(W(m),Sp,Times,Sp,V("Bool")) : W(m);
        Formula Lower(bool bit) => All("Z",V("Type"),All("L",Arrow(P(m),z),Imp(Call("Finite",z),
            Imp(Some("R",Arrow(Call("Prod",Readout(bit),z),P(m)),
                All("p",P(m),Equal(At(r,Joint(bit)),p))),LeqOf(bit ? M(m) : Multiply(Num(2),M(m)),Card(z))))));
        var reconstruction=All("p",P(m),And(
            Equal(Rebuild(Sel(p),Call("fst",label),Call("snd",label)),p),
            Equal(Rebuild(Sel(p),Call("snd",p),Call("unused",p)),p),
            Equal(Call("binaryRecover",Sel(p),Call("binaryLabel",p)),p),
            Equal(Fine(Rebuild(Sel(p),Call("fst",label),Call("snd",label))),B(m,State(p)))));
        var attaining=All("i",W(m),All("j",W(m),And(
            Equal(Call("label",Pair(Pair(i,j),V("false"))),Pair(V("false"),j)),
            Equal(Call("label",Pair(Pair(i,j),V("true"))),Pair(V("true"),i)))));
        Formula BinaryBound(bool bit) => All("ell",N,IffOf(
            Some("L",Arrow(P(m),W(ell)),Call("Injective",Call(bit ? "selectedBitJoint" : "selectedJoint",m,l))),
            LeqOf(bit ? m : Add(m,Num(1)),ell)));
        return All("m",N,And(Lower(false),Lower(true),reconstruction,attaining,
            Equal(Card(Seq(V("Bool"),Sp,Times,Sp,W(m))),Multiply(Num(2),M(m))),
            Equal(Card(W(m)),M(m)),BinaryBound(false),BinaryBound(true),
            Equal(Call("clog",Num(2),Multiply(Num(2),M(m))),Add(m,Num(1))),
            Equal(Call("clog",Num(2),M(m)),m)));
    }

    private static Formula SeparatorsStatement()
    {
        var m=V("m"); var p=V("p"); var q=V("q"); var b=V("b"); var x=V("x");
        var s=V("s"); var t=V("t"); var w=V("w"); var e=Call("experiment",p,b,x); var sep=Call("separator",p,q);
        var experiment=All("p",P(m),All("b",V("Bool"),All("x",W(m),IffOf(
            Member(e,L(m,State(p))),Equal(x,Sel(Pair(Call("fst",p),b)))))));
        var explicitSeparator=All("p",P(m),All("q",P(m),Imp(NotEqual(Fine(p),Fine(q)),
            And(LeqOf(Len(sep),Add(m,Num(2))),Member(sep,L(m,State(p))),Not(Member(sep,L(m,State(q))))))));
        var typed=Call("typedState",C(m),Add(Multiply(Num(2),m),Num(1)),Num(1));
        var actualSeparator=All("s",typed,All("t",typed,Imp(NotEqual(B(m,s),B(m,t)),
            Some("w",Call("List",Call("Action",V("Bool"))),And(LeqOf(Len(w),Add(m,Num(2))),
                Member(w,L(m,s)),Not(Member(w,L(m,t))))))));
        return All("m",N,And(experiment,explicitSeparator,actualSeparator));
    }

    private static Formula SharpnessStatement()
    {
        var m=V("m"); var x=V("x"); var j=V("j"); var k=V("K");
        return And(All("m",N,And(Equal(Card(Q(m,Num(1))),Multiply(Num(2),Pow(Card(Q(m,Num(0))),Num(2)))),
            Call("Finite",C(m)))),
            All("m",N,All("x",W(m),And(Call("Injective",Call("fixedFirstPredecessor",m,x)),
                All("j",W(m),Equal(Derivative(Call("singleList",V("false")),S(x,j)),Singleton(Val(x))))))),
            All("K",N,Some("m",N,And(LeqOf(Num(1),m),LtOf(Multiply(k,Card(Q(m,Num(0)))),Card(Q(m,Num(1))))))));
    }
    private static Formula RefutationStatement()
    {
        var m=V("m");
        return Not(All("m",N,Imp(LeqOf(Num(1),m),LeqOf(Card(Q(m,Num(1))),Multiply(Num(2),Card(Q(m,Num(0))))))));
    }
    private static Formula Statement(string name) => Disp(name switch
    {
        "selector_residual_classification" => ClassificationStatement(),
        "selector_widths_and_fibers" => WidthStatement(),
        "selector_optimal_supplements" => SupplementsStatement(),
        "selector_legal_separators" => SeparatorsStatement(),
        "selector_full_branching_sharpness" => SharpnessStatement(),
        "result" => RefutationStatement(),
        _ => throw new ArgumentOutOfRangeException(nameof(name))
    });

    private static DocumentBlock Theorem(string id, string declaration, string title, params string[] prose) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ObserverMemory/BinarySelectorRecutFibers." + declaration),
            H(title), StatementSource.FromAuthor(Statement(declaration)), AssessedProvenance.FromRepo(),
            Blocks(prose.Select(p => Paragraph(Text(p))).ToArray()), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary selector relation has exact nonlinear recut fibers, attaining reconstruction labels and supplied-action separators of length at most m+2.",
        H("Binary Selector Recut Fibers"),
        Blocks(
            Theorem("selector-residual-classification", "selector_residual_classification", "Original relation and complete residual classification",
                "For each natural m, Word(m) consists of binary lists of length m. A parameter p=((i,j),b) indexes the word ij0i when b=false and ij1j when b=true. The relation is exactly the union of those two families. Every word has length 3m+1, the relation is nonempty and finite, and its cardinality is 2 times M squared, where M=2 to the power m. The results include m=0; the nonlinear recut comparison below assumes m at least one.",
                "In the displayed formulas val is the underlying list of a fixed-length word, false and true denote 0 and 1, pair and Prod denote the indicated ordered pair and product type, concat is ordered list concatenation, cons adds a first symbol, singleList(b) is [b], and nil is the empty list. card is Nat.card, and the displayed ratio is rational. derivative(t,S) is the language of f for which concatenating t with f belongs to S. predecessorMap(m) sends (i,j) to S(i,j).",
                "At cut 2m every actual prefix is ij, and at cut 2m+1 every actual prefix is ijb. Conversely all these prefixes are actual. Ordered concatenation and the prescribed component lengths uniquely recover i, j and b. These are controlled prefixes with a completion in this same relation; the state carries no immutable full-word tag.",
                "The predecessor residual S(i,j) is exactly the two-word language containing 0i and 1j. Its derivatives at 0 and 1 are the singleton languages containing i and j. Equality of predecessor residuals therefore recovers both components. The predecessor residual image consists of exactly M squared different S(i,j), while the current residual image consists of exactly the M singleton languages containing x as x ranges over all m-bit words.",
                "The original StrictAnchoredBoundary state for ijb with one deletion credit is (ij,[b]), and its boundary is fine(p)=(S(i,j),[b]). The zero-credit image is exactly the pairs (singleton(x),empty); the one-credit image is exactly the range of fine. These equalities describe actual joint images, with no free-product assumption."),
            Theorem("selector-widths-and-fibers", "selector_widths_and_fibers", "Actual widths, fibers and behavioral minimum",
                "For m at least one and selector cut k=2m+1, the actual zero-credit boundary image has M points and the one-credit image has 2 times M squared points. Their rational ratio is 2M. A current fiber is the subset of the latter image whose derivative through its one-symbol tail is singleton(x). A fixed-bit fiber also prescribes that tail as [b].",
                "For each x, the current fiber is in bijection with pairs (b,y), where y is the unused m-bit component. rebuild(x,0,y)=((x,y),0) and rebuild(x,1,y)=((y,x),1). Its fine images are exactly the two disjoint families (S(x,j),[0]) and (S(i,x),[1]), of total cardinality 2M. At each separately supplied b the cardinality is M. No empty or unrepresented fiber contributes to these counts.",
                "The strict anchored specialization applies directly with alphabet Bool, source length 3m+1, relation C and admissible type (2m+1,1). On actual states, equality of legal supplied-action languages is equivalent to equality of boundaries. Its strict Option transition equation gives the original moving-anchor append and fixed-anchor delete updates, including missing edges. Every exact representation maps uniquely and onto this actual boundary image; its actual one-credit image therefore has at least 2 times M squared points, and the boundary attains that minimum.",
                "The zero-credit actual image of any exact representation has at least M points by the same strict anchored specialization at type (2m+1,0). In the displayed factor equations, subtype arguments denote their underlying states and labels are inserted into their canonical actual ranges. mapTypeBoundary maps a successful state to its public type and boundary and preserves a missing transition.",
                "Only labels at a supplied public type are counted. The cardinalities assign no cost to the relation description, a transition table, intermediate computation, initialization, a physical device or a retained archive. An accessible source record must be included in the joint representation before a width claim is made."),
            Theorem("selector-optimal-supplements", "selector_optimal_supplements", "Sharp supplements and attaining encodings",
                "For any finite label type Z and any label map L on the actual one-credit points, reconstruction from the current selected component and L requires at least 2M labels. If the selector bit is also supplied, reconstruction requires at least M. The selected component is equivalent to the singleton current residual, and the point parameters are in bijection with the original actual boundary image, so these are lower bounds on the original fibers.",
                "The minimum rollback alphabet theorem is applied to the selected-component map and to the selected-component-plus-bit map. Their maximum fibers are 2M and M, respectively. Exact rollback is converted to joint-record injectivity by the frozen injectivity criterion, with a nonempty actual carrier.",
                "The attaining label is L(ij0)=(0,j) and L(ij1)=(1,i). Given x and (b,y), rebuild returns the actual boundary parameter and therefore the original anchored boundary. With b separately supplied, only y is retained. binaryLabel concatenates b with the m supplied bits of y, and binaryRecover uses its head and tail to reconstruct p. Thus these maps attain m+1 and m binary bits.",
                "The displayed selectedJoint(m,L) is the map p to (selected(p),L(p)); selectedBitJoint(m,L) is p to ((selected(p),p's selector),L(p)). These joint records use the selected word itself, equivalent to its singleton current residual.",
                "For every proposed fixed binary length ell, an injective joint record using ell-bit labels exists exactly when ell is at least m+1, or at least m when the bit is given. The ceiling logarithms of the sharp label cardinalities are correspondingly m+1 and m. The theorem quantifies over arbitrary finite Z, rather than presupposing the optimal alphabet."),
            Theorem("selector-legal-separators", "selector_legal_separators", "Short lawful supplied-action experiments",
                "experiment(p,c,x) requests deletion of p's current selector b and then appends c followed by all m bits of x. Under the original StrictAnchoredBoundary.step and legal definitions for this same C, the full experiment is legal exactly when x is i for c=0 or j for c=1. The proof checks actual extendability at every append and exact full-length membership at its endpoint. After deletion the controlled prefix is ij, so supplying a new selector chooses a different branch of the same relation.",
                "For unequal fine boundaries, if the bits differ separator requests the deletion of the first bit, which exists exactly on the first side. If the bits agree and the i-components differ, it uses experiment with c=0 and the first i. Otherwise the j-components differ and it uses c=1 and the first j. Each branch experiment has one delete and m+1 appends, hence length m+2. The first state has every requested edge; the other misses an edge. A separating experiment is supplied explicitly, with no enabled-action query, failure output, hidden-symbol read or credit replenishment.",
                "Complete actual-prefix classification transports these separators to every pair of actual states of type (2m+1,1) with unequal original boundaries. The final clause gives an action word of length at most m+2 legal on exactly the first side, and the earlier clauses give its concrete construction."),
            Theorem("selector-full-branching-sharpness", "selector_full_branching_sharpness", "Full branching and the missing predecessor relation",
                "The family attains the full-branching formula N1=2 times N0 squared with N0=M. For a known selector 0, all S(x,j) differentiate to the same singleton(x), while the original predecessor residual varies injectively with j. This is the missing predecessor relation: the current residual and fixed bit retain no record of which j was paired with x.",
                "The displayed fixedFirstPredecessor(m,x) is the map j to S(x,j), with x fixed and j ranging over every m-bit word.",
                "For every natural K there is an m at least one such that the one-credit actual width exceeds K times the zero-credit width. The parameter and relation vary in this claim. Every individual C remains finite, with the exact cardinality above. The value alphabet stays Bool and the common action names stay append 0, append 1, delete 0 and delete 1."),
            Theorem("alphabet-only-factor-two-refutation", "result", "Failure of an alphabet-only same-cut bound",
                "AlphabetOnlyTwoBound asserts the same-cut inequality N1 at most 2 times N0 for every m at least one. At m=1, the exact widths are eight and two, so that assertion is false. This refutation concerns the same selector cut, and does not contradict a comparison of peaks taken over all cuts.",
                "The forward right-language interpretation is the standard one for finite prefix automata, as in Daciuk, Mihov, Watson and Watson, Incremental construction of minimal acyclic finite state automata, sections 2 and 3, Computational Linguistics 26(1), 2000. That source supplies the forward meaning only; it does not supply deletion credit or the recut fiber counts. The nonlinear selector classification and lawful separators here are mathematical consequences of the stated binary relation and strict supplied actions.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ObserverMemory/StrictAnchoredBoundary")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/History/Coding/MinimumRollbackAlphabet")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion"))]));
}
