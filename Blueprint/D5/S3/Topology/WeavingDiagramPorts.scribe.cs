using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class WeavingDiagramPortsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Topology/WeavingDiagramPorts";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Topology/mishraraundal2021weaving");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual finite closed-braid port quotient has an explicit interval-and-outer-strand classification in either uniform smoothing.",
        H("Uniform circles of the finite closed weaving braid"),
        Blocks(
            Paragraph(Text("A parameter P consists of integers n at least 2 and m at least 3. There are n generators, indexed from zero, acting at strand positions i and i+1. Crossings in one period occur in increasing generator order. Time is ZMod(m), so the period seam is part of the finite carrier. A dart is (t,i,a), where a is one of tl,tr,bl,br. These are positions outside the crossing disk, irrespective of over-crossing sign.")),
            Paragraph(Text("At position 0 only generator 0 occurs, and at position n only generator n-1 occurs. An internal position j meets generator j-1 on the right and then generator j on the left in each period. Consequently bl(t,0) joins tl(t+1,0); bl(t,i), for i positive, joins tr(t+1,i-1); br(t,i), for i+1 less than n, joins tl(t,i+1); br(t,n-1) joins tr(t+1,n-1). Reverse rules define the same matching on the top inputs.")),
            Entry("external-involution", "external_involutive", "A total external perfect matching",
                AllP(Call("Involutive",Call("external",P))),
                "Applying the external matching twice returns every actual dart, including the internal left outputs and both outer seams. The matching is a function, so a port has exactly one external neighbour."),
            Entry("external-no-fixed-point", "external_ne_self", "No external fixed port",
                AllP(All("x",Call("Dart",P),Ne(Call("external",P,X),X))),
                "Each external arc connects a top input to a bottom output. In particular no arc has a single endpoint port."),
            Paragraph(Text("Here is the chronological derivation of the external matching. Before cyclic reduction, an occurrence is (q,i), with natural period q and generator 0 <= i < n. Define (q,i) < (s,j) to mean q < s or q=s and i < j. The left output bl has spatial position i, and the right output br has position i+1; a top port tl at generator j has position j, while tr has position j+1. An occurrence at generator j is incident to position a exactly when j=a or j+1=a. Thus at an internal position a, the only incident generators are a-1 and a, in that order in each period; position 0 has only generator 0 and position n only generator n-1.")),
            Paragraph(Text("For br at (q,i) with i+1<n, the next incident occurrence is (q,i+1), entered at tl. Its position is i+1, it is strictly later in the defined order, and no incident occurrence lies strictly between: the only two incident generators are i and i+1, consecutive in this period. For br at i=n-1, position n has only generator i, so its next occurrence is (q+1,i), entered at tr at position i+1=n. No incident occurrence lies between consecutive periods of this sole generator.")),
            Paragraph(Text("For bl at (q,i) with i>0, the next incident occurrence is (q+1,i-1), entered at tr at position (i-1)+1=i. Generator i-1 has already occurred earlier in period q and generator i is the current occurrence. In the next period i-1 precedes i. Hence this successor is strictly later and there is no incident (s,j) with (q,i)<(s,j)<(q+1,i-1). For bl at i=0, position 0 has only generator 0, so the next occurrence is (q+1,0), entered at tl, again with no intervening incident occurrence. These four cases establish a top input at the same spatial position, strict chronological order and the quantified exclusion of every intervening incident occurrence.")),
            Paragraph(Text("Now reduce the natural periods modulo m. Writing t for q in ZMod(m), q+1 becomes t+1. The four successors are precisely the four bottom-output clauses of external above. At q=m-1 this reduction identifies the next period with time zero, including both outer wires and the internal bl wires that cross the closing seam. The top-input clauses reverse these same wires, as external_involutive checks. This derives the positional matching from the repeated braid sequence; crossing signs do not change its wires. The chronological order is on natural occurrences before reduction, with no linear order imposed on cyclic time.")),
            Paragraph(Text("The smoothing parity p is 0 or 1. Cup(p,i) means i mod 2 equals p. Thus p=0 selects printed odd generators and p=1 selects printed even generators. Cup-cap pairs tl with tr and bl with br; vertical pairs tl with bl and tr with br. Reach is the equivalence closure of these local arcs and the external matching. Circle(P,p) is the actual quotient of darts by Reach.")),
            Paragraph(Text("The code of the interval at generator i and time t is (i+1,t). At a cup-cap crossing, both top ports have code (i+1,t-1) and both bottom ports have code (i+1,t). At an internal vertical crossing the left ports have code (i,t) and the right ports code (i+2,t-1). An unpaired left outer strand has code (0,0); an unpaired right outer strand has code (n+1,0). These outer codes occur only when the corresponding boundary generator is vertical.")),
            Entry("component-classification", "reach_iff_code", "Codes classify the actual connected components",
                WithParity(All("x",Call("Dart",P),All("y",Call("Dart",P),
                    Iff(Call("Reach",P,Parity,X,Y),Eq(Call("code",P,Parity,X),Call("code",P,Parity,Y)))))),
                "Every generating arc preserves the code. Conversely, a cup-cap top reaches the preceding bottom cap via the intervening vertical crossing, with the left seam handled separately. A vertical left port reaches the preceding generator's bottom cap at the same time; a vertical right port reaches the next generator's bottom cap at time t-1. Local smoothing arcs handle the other ports. Outer vertical strands advance one time step by a local arc followed by an external arc; induction on a natural representative of cyclic time connects each to time zero. Therefore equal codes give actual paths. No enumeration of smoothing states occurs."),
            Entry("quotient-bijection", "circleEquiv", "An explicit quotient bijection",
                WithParity(Call("Equiv",Call("Circle",P,Parity),Call("Label",P,Parity))),
                "Label is the disjoint union of a paired generator with its cyclic time and a Boolean outer-side label restricted to sides whose boundary crossing is vertical. The quotient map sends a dart to its label; its inverse sends an interval to the bottom-left cap port and an outer side to the time-zero top port. The path theorem proves both inverse identities."),
            Entry("odd-count", "odd_circle_count", "Printed odd cup-caps",
                AllP(Eq(Card(Call("Circle",P,F.D(0))),Sub(Add(Mul(Add(R,D),M),F.D(1)),D))),
                "Put d=n mod 2 and r=(n-d)/2. There are r+d paired generators, each contributing m interval circles, and 1-d unpaired outer strands. The equivalence circleEquiv has inverse taking an interval label to its bottom-left port and an outer label to its time-zero top port."),
            Entry("even-count", "even_circle_count", "Printed even cup-caps",
                AllP(Eq(Card(Call("Circle",P,F.D(1))),Add(Add(Mul(R,M),F.D(1)),D))),
                "There are r paired generators and 1+d unpaired outer strands. The same quotient equivalence applies. These formulas include n=2,m=3 and do not require any coprimality or knot-component condition."),
            Paragraph(Text("Write C(t,i) for the actual quotient class of (t,i,bl), L for the class of (0,0,tl), and R for the class of (0,n-1,tr). At a cup-cap crossing the crossing edge uses the tl and bl classes; at a vertical crossing it uses the tl and tr classes. These choices select one endpoint from each local smoothing arc.")),
            Entry("cup-incidence", "cup_edge", "The two interval endpoints",
                WithParity(AllTI(Imp(Call("cup",Parity,I),Eq(E,Pair(C(Sub(T,F.D(1)),I),C(T,I)))))),
                "The cup-cap edge joins C(t-1,i) to C(t,i), with subtraction in cyclic time."),
            Entry("internal-incidence", "internal_edge", "The internal vertical endpoints",
                WithParity(AllTI(Imp(And(Not(Call("cup",Parity,I)),Ne(I,F.D(0)),Lt(Add(I,F.D(1)),N)),
                    Eq(E,Pair(C(T,Sub(I,F.D(1))),C(Sub(T,F.D(1)),Add(I,F.D(1)))))))),
                "An internal vertical crossing joins the left interval at time t and the right interval at time t-1. Both labels are actually present because adjacent generator parities alternate."),
            Entry("left-incidence", "left_edge", "The left outer endpoint",
                WithParity(All("t",Call("ZMod",M),Imp(Not(Call("cup",Parity,F.D(0))),
                    Eq(Call("edgeEnds",P,Parity,T,F.D(0)),Pair(Id("L"),C(Sub(T,F.D(1)),F.D(1))))))),
                "When generator zero is vertical, its left endpoint is the actual unpaired left circle and its right endpoint is the interval at generator one."),
            Entry("right-incidence", "right_edge", "The right outer endpoint",
                WithParity(All("t",Call("ZMod",M),Imp(Not(Call("cup",Parity,Sub(N,F.D(1)))),
                    Eq(Call("edgeEnds",P,Parity,T,Sub(N,F.D(1))),Pair(C(T,Sub(N,F.D(2))),Id("R")))))),
                "When the last generator is vertical, its right endpoint is the actual unpaired right circle and its left endpoint is the preceding interval."),
            Entry("endpoint-distinctness", "edge_endpoints_distinct", "Every crossing has distinct circle endpoints",
                WithParity(AllTI(Ne(Call("fst",E),Call("snd",E)))),
                "For a cup-cap crossing, equality would force 1=0 in ZMod(m), which is impossible for m at least 3. For a vertical crossing the interval or outer codes have different first coordinates. This is looplessness at the actual quotient, without deleting loops by definition."),
            Paragraph(Text("This finite geometry is auxiliary to Mishra and Raundal, Hecke algebra trace algorithm and some conjectures on weaving knots, arXiv:1908.04152v3, Conjecture 5.2. It does not establish that conjecture. The target remains every fixed n at least 2 and k at least 1, for all sufficiently large integer m, including multi-component links: T_k(W(n+1,m))=((r+d)^k+r^k)m^k/k!+O_(n,k)(m^(k-1)). No original-problem or uniqueness claim follows from the circle classification; the scope of the related JIMS publication remains unresolved.")),
            Paragraph(Text("Still required are uniqueness of crossing edge incidences as unordered endpoint pairs, graph connectedness, the actual finite diagram-to-state-sum rank identity for arbitrary smoothing states, connected planar checkerboard realizations and signed planar duality, and transfer to coefficients of the actual normalized integral Jones invariant. The raw Kauffman bracket needs its monomial factor, exponent substitution and writhe normalization before comparison with a signed graph polynomial. The two endpoint magnitudes must each be counted once. Uniform asymptotics require the varying graph family, rather than a fixed graph with a free auxiliary m. Complex Perron paths or Artin traces alone supply none of these geometric and integral coefficient identifications. This module introduces no polynomial under the name Jones and contains no assumed certificate of those unpaid conclusions.")))));

    private static DocumentBlock Entry(string id,string name,string title,Formula statement,string prose) =>
        Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create(Module+"."+name),H(title),
            StatementSource.FromAuthor(F.Disp(statement)),AssessedProvenance.FromRepo(Source),Blocks(Paragraph(Text(prose))));
    private static Formula P => Id("P"); private static Formula Parity => Id("p");
    private static Formula X => Id("x"); private static Formula Y => Id("y");
    private static Formula I => Id("i"); private static Formula T => Id("t");
    private static Formula N => Call("n",P); private static Formula M => Call("m",P);
    private static Formula R => Id("r"); private static Formula D => Id("d");
    private static Formula E => Call("edgeEnds",P,Parity,T,I);
    private static Formula C(Formula t,Formula i) => Call("C",t,i);
    private static Formula Id(string s)=>F.Id(s);
    private static Formula Call(string s,params Formula[] xs)=>new Formula.Apply(Id(s),[..xs]);
    private static Formula All(string s,Formula type,Formula body)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),type,body);
    private static Formula AllP(Formula body)=>All("P",Id("Parameters"),body);
    private static Formula WithParity(Formula body)=>AllP(All("p",Id("Nat"),Imp(Lt(Parity,F.D(2)),body)));
    private static Formula AllTI(Formula body)=>All("t",Call("ZMod",M),All("i",Call("Fin",N),body));
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a,Formula b)=>F.Seq(a,F.Sp,F.Neq,F.Sp,b);
    private static Formula Lt(Formula a,Formula b)=>F.Seq(a,F.Sp,F.Lt,F.Sp,b);
    private static Formula Iff(Formula a,Formula b)=>F.Seq(a,F.Sp,F.Iff,F.Sp,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Not(Formula a)=>F.Seq(F.Neg,F.Sp,a);
    private static Formula And(params Formula[] xs){var r=xs[^1];for(var i=xs.Length-2;i>=0;i--)r=new Formula.Logic(xs[i],FormulaLogicOperator.And,r);return r;}
    private static Formula Add(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a,Formula b)=>new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Pair(Formula a,Formula b)=>Call("pair",a,b);
    private static Formula Card(Formula a)=>Call("card",a);
}
