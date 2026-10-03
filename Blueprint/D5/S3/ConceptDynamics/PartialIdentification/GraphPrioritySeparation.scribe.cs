using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class GraphPrioritySeparationDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        Seq(Par(premise), Sp, Implies, Sp, Par(conclusion));
    private static Formula And(Formula left, Formula right) =>
        Seq(Par(left), Sp, Land, Sp, Par(right));
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Pow(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For arbitrary finite directed constraints, including loops, an alphabet containing "
            + "neutral and separate incoming/outgoing symbols and normalized rational product "
            + "site laws with every symbol mass at least a common positive rho give a positive "
            + "legal normalizer, exact effective-signature classification of priority teachers, "
            + "and conditioned disagreement at least rho^(dout+din+3) under uniform degree caps.",
        H("Priority Teacher Separation on Arbitrary Directed Constraint Graphs"),
        Blocks(
            Paragraph(Text("Fix a finite linearly ordered vertex type V and a finite alphabet "
                + "Symbol. The formula is quantified over all data on these fixed carriers; "
                + "V may be empty and no teacher triple need exist. first and last map Symbol "
                + "to Bool. The distinguished symbols zero, high and low have respective "
                + "(first,last) values (false,false), (false,true) and (true,false). "
                + "Other symbols and their endpoint values are unrestricted. G is any directed "
                + "relation on V, with loops allowed and no requirement that its arcs follow "
                + "the vertex order. outgoing(G,i) and incoming(G,j) are its finite neighbor "
                + "sets, bounded in cardinality by dout and din respectively.")),
            Paragraph(Text("An input x maps V to Symbol. Legal(G,first,last,x) forbids "
                + "last(x(i)) and first(x(j)) from both being true on every G arc (i,j). "
                + "Roles(V) contains strict triples p<q<r. teacher(first,last,t,x) returns "
                + "1 if the p-to-q endpoint gate is on, otherwise 2 if the q-to-r gate is on, "
                + "and 0 otherwise. The first gate has priority even when both gates are on. "
                + "edge(G,i,j) is None on a G arc and Some(i,j) otherwise; signature(G,t) "
                + "is the ordered pair of those two effective edges.")),
            Paragraph(Text("FiniteResponseLaw(Symbol) is a rational, nonnegative mass function "
                + "with total mass one. laws supplies one such law per vertex. The original "
                + "independentSourceLaw(laws) gives each full input the product of its site "
                + "masses. legalNormalizer(G,first,last,laws) sums that original product over "
                + "exactly the Legal inputs. conditionedDisagreement(G,first,last,laws,t,u) "
                + "divides the product mass of Legal inputs with different teacher outputs by "
                + "the same normalizer. Conditioning is global, across all graph constraints "
                + "at once; conditional coordinates may be dependent. The common lower bound "
                + "rho>0 holds for every vertex and every alphabet symbol.")),
            Describe.Lean(DescribeId.Create("graph-priority-teacher-separation"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/PartialIdentification/GraphPrioritySeparation.result"),
                H("Positive normalizer, exact teacher classification and degree-controlled separation"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The all-zero-symbol configuration is legal, so its positive "
                        + "product mass proves normalizer positivity independently of whether "
                        + "Roles(V) is inhabited. A non-forbidden target pair (i,j) is forced by "
                        + "high at i and low at j, with endpoint assignments taking precedence. "
                        + "Neutral symbols at every other supported outgoing(G,i) and "
                        + "incoming(G,j) vertex remove new conflicts; endpoint loops are safe "
                        + "because high has first bit false and low has last bit false. At most one "
                        + "additional neutral endpoint blocks a different competing gate. "
                        + "The support has at most dout+din+3 vertices, counting overlaps once. "
                        + "This fixed assignment preserves every previously legal exterior "
                        + "completion. When first signatures differ, the forced first gate "
                        + "produces 1 versus 0 or 2. When first signatures agree but second "
                        + "signatures differ, the forced second source has first bit false, "
                        + "which closes the common first gate and produces 2 versus 0. "
                        + "This also constructs the witness for the pointwise equivalence.")),
                    Paragraph(Text("The proof directly reuses independentSource_mass_split "
                        + "from FiniteIndependentSourceGrouping to split the same original "
                        + "product mass into the chosen support and its complement. For each "
                        + "completable exterior, the fixed internal assignment has product mass "
                        + "at least rho^(dout+din+3); its mass times the legal fiber mass is "
                        + "bounded by the disagreement fiber mass. Summing nonnegative exterior "
                        + "weights and dividing by the positive normalizer gives the bound.")),
                    Paragraph(Text("A non-path application is the Widom-Rowlinson model on "
                        + "any finite simple undirected graph of maximum degree Delta. Replace "
                        + "each edge by both arcs and use the symbols empty,A,B with endpoint "
                        + "values (false,false),(false,true),(true,false). Legal configurations "
                        + "forbid adjacent A and B. For positive rational lambda, site masses "
                        + "are 1/(1+2lambda), lambda/(1+2lambda), lambda/(1+2lambda). Global "
                        + "legal conditioning yields precisely the law proportional to "
                        + "lambda^(number of A plus number of B), as defined in Section 1 of "
                        + "Cohen, Perkins and Tetali, On the Widom-Rowlinson Occupancy Fraction "
                        + "in Regular Graphs, arXiv:1512.06398v2. Taking "
                        + "rho=min(1,lambda)/(1+2lambda) gives the bound rho^(2Delta+3) "
                        + "for different effective teacher signatures. The graph can be a "
                        + "tree, grid or another bounded-degree graph; teacher gates can test "
                        + "non-neighboring positions.")),
                    Paragraph(Text("The exponent has no optimality claim. Positive site "
                        + "marginals alone cannot replace the original product-law condition: "
                        + "the uniform mixture of the three constant empty,A,B configurations "
                        + "has all three marginal masses 1/3 while every A-to-B gate is off. "
                        + "The theorem supplies neither a learning algorithm nor a sample "
                        + "complexity, noise-tolerance or arbitrary correlated-source bound."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var vertex = V("V");
        var symbol = V("Symbol");
        var graph = V("G");
        var first = V("first");
        var last = V("last");
        var zero = V("zero");
        var high = V("high");
        var low = V("low");
        var dout = V("dout");
        var din = V("din");
        var laws = V("laws");
        var rho = V("rho");
        var i = V("i");
        var j = V("j");
        var a = V("a");
        var x = V("x");
        var t = V("t");
        var u = V("u");
        var boolean = V("Bool");
        var natural = Seq(Mathbb, Grp(V("N")));
        var rational = Seq(Mathbb, Grp(V("Q")));
        var input = Seq(vertex, Sp, To, Sp, symbol);
        var lawType = Seq(vertex, Sp, To, Sp, Call("FiniteResponseLaw", symbol));
        var graphType = Seq(vertex, Sp, To, Sp, vertex, Sp, To, Sp, V("Prop"));
        var readoutType = Seq(symbol, Sp, To, Sp, boolean);
        var zeroBits = And(Equal(Call("first", zero), V("false")),
            Equal(Call("last", zero), V("false")));
        var highBits = And(Equal(Call("first", high), V("false")),
            Equal(Call("last", high), V("true")));
        var lowBits = And(Equal(Call("first", low), V("true")),
            Equal(Call("last", low), V("false")));
        var outBound = All(i, vertex,
            Seq(Call("card", Call("outgoing", graph, i)), Sp, Le, Sp, dout));
        var inBound = All(j, vertex,
            Seq(Call("card", Call("incoming", graph, j)), Sp, Le, Sp, din));
        var lawAt = new Formula.Apply(laws, [i]);
        var lower = All(i, vertex, All(a, symbol,
            Seq(rho, Sp, Le, Sp, Call("mass", lawAt, a))));
        var equalTeachers = All(x, input, Imp(Call("Legal", graph, first, last, x),
            Equal(Call("teacher", first, last, t, x), Call("teacher", first, last, u, x))));
        var equalSignatures = Equal(Call("signature", graph, t), Call("signature", graph, u));
        var classification = Seq(Par(equalTeachers), Sp, Iff, Sp, Par(equalSignatures));
        var different = Seq(Call("signature", graph, t), Sp, Neq, Sp, Call("signature", graph, u));
        var exponent = Seq(dout, Sp, Plus, Sp, din, Sp, Plus, Sp, D(3));
        var lowerDisagreement = Seq(Pow(rho, exponent), Sp, Le, Sp,
            Call("conditionedDisagreement", graph, first, last, laws, t, u));
        var teacherClaim = All(t, Call("Roles", vertex), All(u, Call("Roles", vertex),
            And(classification, Imp(different, lowerDisagreement))));
        var result = And(Seq(D(0), Sp, Lt, Sp,
            Call("legalNormalizer", graph, first, last, laws)), teacherClaim);
        var lawClaim = All(laws, lawType, All(rho, rational,
            Imp(Seq(D(0), Sp, Lt, Sp, rho), Imp(lower, result))));
        var degreeClaim = All(dout, natural, All(din, natural,
            Imp(outBound, Imp(inBound, lawClaim))));
        var symbolClaim = All(zero, symbol, All(high, symbol, All(low, symbol,
            Imp(zeroBits, Imp(highBits, Imp(lowBits, degreeClaim))))));
        return All(graph, graphType, All(first, readoutType, All(last, readoutType, symbolClaim)));
    }
}
