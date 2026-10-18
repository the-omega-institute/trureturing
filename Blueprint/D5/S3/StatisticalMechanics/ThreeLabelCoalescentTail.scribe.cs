using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class ThreeLabelCoalescentTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/ThreeLabelCoalescentTail.";
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
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, To, b);
    private static Formula Mass => Arrow(Call("Fin", D(5)), R);
    private static Formula Trajectory => Arrow(R, Mass);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common positive association tail for an open region of seven-rate generators.",
        H("Uniform tail stability for three-label coalescence"),
        Blocks(
            Paragraph(Text("Use the seven-rate generator and GeneralForwardLaw of ThreeLabelCoalescent. "
                + "Write M(r)=min(d,L)+min(e,L)-L, with L=alpha+beta+gamma+zeta. "
                + "The rate region requires every rate positive, max(alpha,beta,gamma)<4, "
                + "min(L,d,e,f)>1/8 and M(r)>1/8. These are strict continuous inequalities, "
                + "so the region is open. Every baseRates(h), h>0, belongs to it.")),
            Describe.Lean(
                DescribeId.Create("three-label-uniform-positive-tail"),
                DeclarationHandle.Create(Prefix + "uniform_positive_tail"),
                H("One finite time works for every rate in the open region"),
                StatementSource.FromAuthor(Disp(TailFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let E(t)=exp(-t/8). The branch certificates bound pN by E, "
                    + "each of pA,pB,pC by 4tE, and pA*pB/pN by 16t squared E. "
                    + "The common envelope E+12tE+16t squared E tends to zero. Beyond one finite T "
                    + "it is less than one, so normalization gives pT>pA*pB/pN. "
                    + "Multiplication by the strictly positive pN gives delta>0. "
                    + "This proves uniform exclusion of late roots under perturbation. Exact preservation "
                    + "of two roots also needs control near zero and on a bounded time interval; "
                    + "those conclusions are not asserted here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-label-uniform-positive-near-zero"),
                DeclarationHandle.Create(Prefix + "uniform_positive_near_zero"),
                H("A common positive initial interval around every base vector"),
                StatementSource.FromAuthor(Disp(NearFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix h>0. Choose R=ell(h)+4 and a=h/2, and restrict all rates "
                    + "to (0,R) with zeta>a. This open region contains baseRates(h). For "
                    + "0<t<min(1/(8R),a/(8R squared)), the N mass is at least 1/2, the T mass "
                    + "is at least at/2, and both pA and pB are at most Rt. Thus "
                    + "delta is at least at/4-R squared t squared and is strictly positive. "
                    + "Together with the tail theorem, this controls both unbounded ends of time. "
                    + "The remaining root-stability obligation is uniform continuity of the solution "
                    + "and its association derivative in the seven rates on a compact time interval, "
                    + "followed by persistence and uniqueness near the two simple base roots."))),
                DescribeRole.Theorem)
        )));

    private static Formula TailFormula()
    {
        Formula u = F.Id("U"), tbound = F.Id("T"), h = F.Id("h");
        Formula r = F.Id("r"), p = F.Id("p"), t = F.Id("t");
        Formula rates = Arrow(Call("Fin", D(7)), R);
        Formula member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
        Formula baseMember = All("h", R, Imp(Lt(D(0), h), member(Call("baseRates", h), u)));
        Formula positive = All("r", rates, Imp(member(r, u), All("p", Trajectory,
            Imp(Call("GeneralForwardLaw", r, p), All("t", R,
                Imp(Le(tbound, t), Lt(D(0), Call("delta", Seq(p, Open, t, Close)))))))));
        Formula time = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("T"), R,
            And(Le(D(0), tbound), positive));
        return new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("U"), Call("Set", rates),
            And(Call("IsOpen", u), And(baseMember, time)));
    }
    private static Formula NearFormula()
    {
        Formula u = F.Id("U"), e = F.Id("e"), h = F.Id("h");
        Formula r = F.Id("r"), p = F.Id("p"), t = F.Id("t");
        Formula rates = Arrow(Call("Fin", D(7)), R);
        Formula member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
        Formula positive = All("r", rates, Imp(member(r, u), All("p", Trajectory,
            Imp(Call("GeneralForwardLaw", r, p), All("t", R, Imp(Lt(D(0), t),
                Imp(Lt(t, e), Lt(D(0), Call("delta", Seq(p, Open, t, Close))))))))));
        Formula interval = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("e"), R,
            And(Lt(D(0), e), positive));
        Formula neighborhood = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("U"), Call("Set", rates),
            And(Call("IsOpen", u), And(member(Call("baseRates", h), u), interval)));
        return All("h", R, Imp(Lt(D(0), h), neighborhood));
    }

}
