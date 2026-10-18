using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class ThreeLabelCoalescentPerturbationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/ThreeLabelCoalescentPerturbation.";
    private static Formula Q(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Q(name), Open, Join(args), Close);
    private static Formula Join(Formula[] args) => args.Length switch
    {
        0 => Seq(),
        1 => args[0],
        _ => Seq(args[0], Comma, Join(args[1..]))
    };
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, To, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Open stability of both simple association crossings under seven-rate perturbations.",
        H("Seven-rate stability of three-label coalescence"),
        Blocks(
            Paragraph(Text("Rates retain the same seven directed transitions, in the order "
                + "alpha,beta,gamma,zeta,d,e,f. TwoSimpleCrossings(f) means that there are "
                + "0<a<b with f(a)=f(b)=0, nonzero derivatives at both roots, and strict signs "
                + "positive on (0,a), negative on (a,b), and positive on (b,infinity). "
                + "These signs also exclude every other positive zero. GeneralForwardLaw "
                + "keeps the initial state, generator equations, nonnegativity and normalization "
                + "independent of the explicit resonant solution.")),
            Describe.Lean(
                DescribeId.Create("three-label-seven-rate-crossing-stability"),
                DeclarationHandle.Create(Prefix + "seven_rate_two_crossings_stable"),
                H("An open rate neighborhood preserves exactly two simple zeros"),
                StatementSource.FromAuthor(Disp(StabilityFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite forward operator is a continuous linear map "
                    + "depending linearly on the seven rates. Its exponential applied to the initial "
                    + "vector solves the equations. Gronwall uniqueness identifies every supplied "
                    + "probability solution with this model on nonnegative time. Analyticity of the "
                    + "operator exponential makes the model and its association derivative jointly "
                    + "continuous in rates and time.")),
                    Paragraph(Text("Choose disjoint closed intervals around the two simple base roots. "
                    + "A compact tube argument preserves nonzero derivative on each interval; "
                    + "the endpoint signs give a zero by the intermediate value theorem, and Rolle's "
                    + "theorem excludes a second zero in either interval. On the remaining compact "
                    + "time set, another tube argument preserves the sign of the base association. "
                    + "The uniform near-zero and tail bounds of ThreeLabelCoalescentTail exclude "
                    + "all other times. Intersect these neighborhoods with the positive-rate cone. "
                    + "The resulting open neighborhood therefore preserves the exact root count, "
                    + "simplicity and all three signs.")),
                    Paragraph(Text("The unique_fold_classification theorem supplies TwoCrossings(h) "
                    + "for every 0<h<hc. This proves the stated seven-rate stability throughout that "
                    + "range. No stability of the double zero at hc is asserted. The theorem applies "
                    + "to every probability solution of the perturbed generator; the auxiliary "
                    + "operator model is not assumed to be a probability law."))),
                DescribeRole.Theorem)
        )));

    private static Formula StabilityFormula()
    {
        Formula h = F.Id("h"), u = F.Id("U"), r = F.Id("r");
        Formula p = F.Id("p"), i = F.Id("i"), t = F.Id("t");
        Formula rates = Arrow(Call("Fin", D(7)), R);
        Formula mass = Arrow(Call("Fin", D(5)), R);
        Formula trajectory = Arrow(R, mass);
        Formula positive = All("r", rates, Imp(Member(r, u),
            All("i", Call("Fin", D(7)), Lt(D(0), Seq(r, Open, i, Close)))));
        Formula crossings = Call("TwoSimpleCrossings",
            Seq(Open, t, Colon, R, Sp, Mapsto, Sp, Call("delta", Seq(p, Open, t, Close)), Close));
        Formula stable = All("r", rates, Imp(Member(r, u), All("p", trajectory,
            Imp(Call("GeneralForwardLaw", r, p), crossings))));
        Formula neighborhood = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("U"), Call("Set", rates),
            And(Call("IsOpen", u), And(Member(Call("baseRates", h), u), And(positive, stable))));
        return All("h", R, Imp(Lt(D(0), h), Imp(Call("TwoCrossings", h), neighborhood)));
    }
}
