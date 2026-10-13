using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Records;

internal sealed class MovingAverageRecordBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/godrecheluck2020records");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The record probability of two successive iid summands is at most 3/(2n) for every atomless real probability law and n at least 3.",
        H("Records of a two-term moving average"),
        Blocks(
            Node("recordProb", "The record probability", RecordFormula(),
                "Section 1, p. 2: \"In the present work we investigate the statistics of records for sequences made of sums of p successive iid positive random variables, defined as follows. For p = 2,\" Equation (1.4) is Y₂=X₁+X₂, Y₃=X₂+X₃, …, Yₙ=Xₙ₋₁+Xₙ, …. Equation (1.7) is Qₙ=Prob(Yₙ>Lₙ₋₁). Page 3 specifies \"where records are counted from the first complete sum Y₂ onwards.\" Thus Qₙ is the strict record probability of the terminal moving sum. In the displayed real-coordinate expression, x(i) is X_(i+1), and i runs from 1 through n−2. Measure.pi is the finite iid product measure. The anonymous dot in its lambda denotes an unused index. Fin.mk displays the value field of each finite index; proof fields are suppressed. The two index inequalities imply n≥3 and all constructor bounds. Subtraction in the index values is natural-number truncated subtraction. ENNReal.toReal gives a real probability for probability measures.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source), SourceRecordFormula()),
            Node("claim", "The density upper-bound statement", ClaimFormula(),
                "Section 6.6, p. 31, after equation (6.33): \"Finally, the data shown in figure 1 suggest that (6.33) provides an absolute upper bound for Qₙ.\" Equation (6.33) on p. 30 gives Qₙ=3/(2n) for n≥3 in the exponentially broad limit. Here `Continuous f` is the density restriction fixed by preregistration #15864; the public atomless theorem covers the paper's broader domain. The moving sums and record event are those of equations (1.4), (1.7) and the first-complete-sum sentence on p. 3. The displayed cast of n to the real numbers makes real division explicit.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("movingAverage_record_bound", "The atomless-law bound", GeneralFormula(),
                "For n≥3, two distinct cyclic edge sums have a coordinate appearing in only one edge, so atomlessness makes their equality a null event. Rotation of the iid coordinates preserves their product measure and assigns probability 1/n to each position of the unique cyclic maximum. The record event splits, outside the null tie set, into a maximum at edge n−2 and a runner-up at edge n−2 below the maximum at edge n−1. Reversal fixes edge n−1 and exchanges edge n−2 with edge 0. These two runner-up events have equal probability and are disjoint within a maximum event of probability 1/n. Consequently the runner-up contribution is at most 1/(2n), giving 3/(2n). NoAtoms means every singleton has measure zero. Positivity and a density are unnecessary for this theorem.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The density statement follows", Disp(F.Id("claim")),
                "A law obtained from Lebesgue measure by withDensity is atomless. Applying the atomless-law bound therefore proves claim. The continuity, nonnegativity and positive-support assumptions express the source's setting; the atomless estimate needs only the probability law.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), null,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("godreche-luck-2020-moving-average-record-bound"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance, Formula? sourceFormula = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("moving-average-" + (declaration switch
            { "recordProb" => "record-prob", "movingAverage_record_bound" => "atomless-bound", _ => declaration })),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance,
            sourceFormula is null ? Blocks(Paragraph(Text(prose))) :
                Blocks(Paragraph(Text(prose)), Paragraph(Text("In the source notation, "), Math(sourceFormula), Text("."))), role,
            resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Measure() => QCall("MeasureTheory", "Measure", Reals());
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Index(Formula value, Formula n) => Cast(QCall("Fin", "mk", value), FinOf(n));
    private static Formula Bound(Formula mu, Formula n) =>
        AtMost(Call("recordProb", mu, n), new Formula.Fraction(D(3), Mul(D(2), Cast(n, Reals()))));

    private static Formula SourceRecordFormula()
    {
        Formula n=F.Id("n"), y=F.Id("Y");
        Formula largest=App(Max, new Formula.Subscript(y,D(2)), Seq(Dot,Dot,Dot),
            new Formula.Subscript(y,Subtract(n,D(1))));
        return Equal(new Formula.Subscript(F.Id("Q"),n),
            App(Named("Pr"), new Formula.Relation(new Formula.Subscript(y,n),
                FormulaRelationOperator.GreaterThan, largest)));
    }

    private static Formula RecordFormula()
    {
        Formula mu=F.Id("mu"), n=F.Id("n"), x=F.Id("x"), i=F.Id("i");
        Formula val=Call("val", i);
        Formula eventBody=All("i", FinOf(n), Implies(AtMost(D(1), val),
            Implies(AtMost(Add(val, D(2)), n),
                Less(Add(App(x, Index(Subtract(val, D(1)), n)), App(x, i)),
                    Add(App(x, Index(Subtract(n, D(2)), n)), App(x, Index(Subtract(n, D(1)), n)))))));
        Formula eventSet=Seq(OpenBrace, x, Colon, new Formula.TypeArrow(FinOf(n), Reals()), Sp, Mid, Sp, eventBody, CloseBrace);
        Formula family=Seq(LambdaLower, Sp, Parenthesized(Seq(Dot, Colon, FinOf(n))), Sp, Mapsto, Sp, mu);
        Formula product=QCall("Measure", "pi", family);
        Formula value=QCall("ENNReal", "toReal", App(product, eventSet));
        return Disp(All("mu", Measure(), All("n", Naturals(), Equal(Call("recordProb", mu, n), value))));
    }

    private static Formula ClaimFormula()
    {
        Formula f=F.Id("f"), x=F.Id("x"), mu=F.Id("mu"), n=F.Id("n");
        Formula density=Seq(LambdaLower, Sp, Parenthesized(Seq(x, Colon, Reals())), Sp, Mapsto, Sp,
            QCall("ENNReal", "ofReal", App(f, x)));
        Formula law=App(Seq(Qualified("MeasureTheory", "volume"), Dot, Named("withDensity")), density);
        Formula estimate=All("n", Naturals(), Implies(AtMost(D(3),n), Bound(mu,n)));
        Formula positive=Implies(Equal(App(mu, QCall("Set", "Iic", Cast(D(0),Reals()))), D(0)), estimate);
        Formula probability=Implies(QCall("MeasureTheory", "IsProbabilityMeasure", mu), positive);
        Formula measures=All("mu", Measure(), Implies(Equal(mu, law), probability));
        Formula nonnegative=Implies(All("x", Reals(), AtMost(D(0), App(f,x))), measures);
        Formula body=All("f", new Formula.TypeArrow(Reals(), Reals()),
            Implies(Call("Continuous", f), nonnegative));
        return Disp(Equal(F.Id("claim"), body));
    }

    private static Formula GeneralFormula()
    {
        Formula mu=F.Id("mu"), n=F.Id("n");
        Formula body=Seq(OpenBracket, QCall("MeasureTheory", "IsProbabilityMeasure", mu), CloseBracket, Sp,
            Implies(QCall("MeasureTheory", "NoAtoms", mu),
                All("n", Naturals(), Implies(AtMost(D(3),n), Bound(mu,n)))));
        return Disp(All("mu", Measure(), body));
    }
}
