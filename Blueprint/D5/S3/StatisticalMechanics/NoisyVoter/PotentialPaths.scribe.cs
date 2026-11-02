using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.NoisyVoter;

internal sealed class PotentialPathsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unstopped potential copy paths identify native survival, the first fresh source and the original-law variance chain.",
        H("Unstopped potential copy paths"),
        Blocks(
            Paragraph(Text("Let G be a simple graph on an arbitrary vertex type V and x a native coordinate assignment on a sample type O. The choice at v belongs to the actual neighbour set of v. Set Z(n,u,z,0)=u and Z(n,u,z,k+1)=J(n-k,Z(n,u,z,k)). The potential path never tests a refresh to decide whether to continue. Only its offsets zero through d are used when n=i+d. Define A(x,i,d,u,z) independently as: for every k<d, R(i+d-k,Z(i+d,u,z,k)) is false. Its inspected times range from i+d down to i+1; the refresh at its time-i endpoint is excluded.")),
            Node("correspondence", "potential_path_source_correspondence", "The complete native potential-path correspondence", PathStatement(),
                "All i,d are natural, all u are vertices and z is any sample. No probability, cardinality, stationarity or terminal-correctness premise is used. The freshLabel(n,v) in the formula is the disjoint positive-time fresh label; k<d proves its positive birth time. EarlierFalse(k) means every j<k has R(i+d-j,Z_j)=false. A first refresh exists whenever A fails, including offsets zero and d-1. The path continues after that refresh, while the native source stops there. Source collision implies A; the converse is not asserted."),
            Paragraph(Text("For the probability statement, OriginalLaw(G,P,epsilon,x) abbreviates the following explicit hypotheses: G is connected and locally finite, every actual neighbour set is nonempty, P is a probability measure on an arbitrary measurable sample space O, zero<epsilon<one, and the family indexed by initial coordinates and strictly positive-time fresh, refresh and choice coordinates is measurable and mutually independent with the native coordinateLaw marginals. Initial and fresh opinions are independent fair Bernoulli coins, refresh controls have Bernoulli(epsilon) law, and choices are uniform on the actual finite neighbour sets. No measurability, marginal law or independence is required of any fresh, refresh or choice slot at time zero. Native opinions X and disjoint sources S retain their original synchronous recursions.")),
            Node("original-bounds", "original_potential_path_bounds", "Probability and variance on the original positive-time law", BoundsStatement(),
                "The formula uses Aevent(i)={z:A(x,i,d,u,z)}, q=1-epsilon, E(i)=E_i={z:S_i(u,z)=S_(i+d)(u,z)}, N(i)=N_i its complement, and sumNoncollision=sum over i=1 through t of P(N_i). W is exactly the native sum of opinion-equality indicators over the same observation pairs. Every natural d,t is admitted, hence in particular every positive lag and t=0. The observation horizon is t+d. Probabilities are on the original P throughout."),
            Paragraph(Text("For the proof, construct the full-coordinate comparison product Q using the same graph, noise and actual neighbour marginals. The full Model assumptions hold only on Q. Restrict its coordinates and the original x to the positive-coordinate subtype, and apply history_law_of_positive_coordinate_laws at the same root and horizon. The joint opinion-and-source history laws agree. Connectivity and local finiteness give countability through the original vertices_countable supplier; finite histories therefore admit measurable scalar and event readouts. The original history is measurable by finite_history_factorization and the original decode_measurable supplier. Transfer the source-birth event to obtain P(A)=q^d from survival_probability. Transfer each collision event and the actual W variance, then apply native_variance_lower on Q. The complement identity and a finite sum give the second inequality. Time-zero auxiliary slots of x are never included in these laws or measurability hypotheses.")),
            Paragraph(Text("When t=0 the sum and W are zero. At d=0 the potential-path event is the empty conjunction; this extra boundary does not replace the positive-lag statement. The path construction and its prefix-source induction are the mathematical content; existing native source, survival, probability and variance results are reused. The raw control-field conditional laws, character-moment variance identity, equality criterion, K2 optimality and improved coefficients are outside these two statements."))), []));

    private static DocumentBlock Node(string id, string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("voter-potential-" + id),
            DeclarationHandle.Create("D5/S3/StatisticalMechanics/NoisyVoter/PotentialPaths." + name),
            H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/StatisticalMechanics/benjaminihelmantovzhukovskii2023noisyvoter")),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula X(string s) => s switch {
        "i+d" => Seq(F.Id("i"), Plus, F.Id("d")),
        "i+d-k" => Seq(F.Id("i"), Plus, F.Id("d"), Minus, F.Id("k")),
        "k+1" => Seq(F.Id("k"), Plus, D(1)),
        "E_i" => C("E", F.Id("i")),
        "N_i" => C("N", F.Id("i")),
        _ => F.Id(s) };
    private static Formula Named(string s) => Seq(Operatorname, Grp(X(s)));
    private static Formula C(string s, params Formula[] a) => new Formula.Apply(Named(s), [.. a]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Z(Formula k) => C("Z", X("i+d"), X("u"), X("z"), k);
    private static Formula A() => C("A", X("x"), X("i"), X("d"), X("u"), X("z"));
    private static Formula Source(string n, Formula v) => C("S", X(n), v, X("z"));
    private static Formula PathStatement()
    {
        var old = Source("i+d", X("u"));
        var earlier = C("EarlierFalse", X("k"));
        var refresh = Eqn(C("R", X("i+d-k"), Z(X("k"))), Named("true"));
        var first = All("k", Nat(), Imp(Lt(X("k"), X("d")), Imp(earlier, Imp(refresh,
            And(Eqn(old, C("freshLabel", X("i+d-k"), Z(X("k")))), Lt(X("i"), C("birth", old)))))));
        var exists = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("k"), Nat(),
            And(Lt(X("k"), X("d")), And(earlier, refresh)));
        var result = And(Eqn(Z(D(0)), X("u")),
            And(All("k", Nat(), Imp(Lt(X("k"), X("d")), Eqn(Z(X("k+1")), C("J", X("i+d-k"), Z(X("k")))))),
            And(Iffn(A(), Eqn(C("survives", X("x"), X("i"), X("d"), X("u"), X("z")), Named("true"))),
            And(Iffn(A(), Le(C("birth", old), X("i"))),
            And(Imp(A(), Eqn(old, Source("i", Z(X("d"))))),
            And(first, And(Imp(new Formula.Not(A()), exists), Imp(Eqn(Source("i", X("u")), old), A()))))))));
        return Disp(All("V", Named("Type"), All("O", Named("Type"), All("G", C("SimpleGraph", X("V")),
            All("x", C("Coordinates", X("G"), X("O")), All("i", Nat(), All("d", Nat(),
            All("u", X("V"), All("z", X("O"), result)))))))));
    }
    private static Formula BoundsStatement()
    {
        var qd = new Formula.Power(X("q"), X("d"));
        var oneMinus = Seq(D(1), Minus, qd);
        var aevent = C("Aevent", X("i"));
        var eventBounds = All("i", Nat(), And(C("MeasurableSet", aevent),
            And(Eqn(C("P", aevent), qd), And(C("subset", X("E_i"), aevent),
            And(Le(C("P", X("E_i")), qd), Le(oneMinus, C("P", X("N_i"))))))));
        var sum = C("sumNoncollision", X("P"), X("x"), X("u"), X("d"), X("t"));
        var quarter = new Formula.Fraction(D(1), D(4));
        var chain = And(Le(Seq(quarter, Times, sum), C("Var", C("W", X("x"), X("u"), X("d"), X("t")), X("P"))),
            Le(new Formula.Fraction(Seq(X("t"), Times, Grp(oneMinus)), D(4)), Seq(quarter, Times, sum)));
        return Disp(All("V", Named("Type"), All("O", Named("Type"),
            All("m", C("MeasurableSpace", X("O")), All("G", C("SimpleGraph", X("V")),
            All("P", C("Measure", X("O")), All("epsilon", Named("UnitInterval"),
            All("x", C("Coordinates", X("G"), X("O")),
            Imp(C("OriginalLaw", X("G"), X("P"), X("epsilon"), X("x")),
                All("u", X("V"), All("d", Nat(), All("t", Nat(), And(eventBounds, chain)))))))))))));
    }
}
