using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class SpectrumCountPerturbationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Oscillation/SpectrumCountPerturbation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separated intervals preserve the order and bound threshold crossings of a spectrum.",
        H("Spectral Perturbations That Preserve Counting"),
        Blocks(
            Paragraph(Text(
                "A spectrum S has positive distinct ordinates γ(j), positive integer multiplicities "
                + "m(j), and finitely many ordinates at or below each real threshold. The function N(T) "
                + "sums the multiplicities at ordinates at most T. Write J for the index type.")),
            Paragraph(Text(
                "Separated(r) means γ(i)+r(i)<γ(j)−r(j) whenever γ(i)<γ(j). "
                + "Relocation(h,r) gives a spectrum S' and a bijection e from J to its index type. "
                + "The ordinate and multiplicity at e(j) are h(j) and m(j), respectively. "
                + "The order h(i)<h(j) is equivalent to γ(i)<γ(j). At each real T either "
                + "N'(T)=N(T), or some j satisfies γ(j)−r(j)≤T<γ(j)+r(j) and "
                + "N'(T)+m(j)=N(T) or N(T)+m(j)=N'(T).")),
            Describe.Lean(
                DescribeId.Create("exists-ordered-count-perturbations"),
                DeclarationHandle.Create(Owner + ".exists_ordered_count_perturbations"),
                H("Order preservation and a single possible crossing per threshold"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each coordinate take the minimum of one, its positive ordinate, "
                        + "and the positive gaps to the other ordinates up to one above it. "
                        + "The cutoff is finite. One third of the minimum is a positive radius. "
                        + "Every pair of distinct ordinates has each radius at most one third "
                        + "of their gap, so the closed intervals are strictly ordered. "
                        + "The uniform radius bound also yields locally finite sublevel sets "
                        + "for any selected ordinates.")),
                    Paragraph(Text(
                        "At a fixed threshold T, membership can change only at a coordinate whose "
                        + "closed interval contains T strictly below its right endpoint. These "
                        + "intervals are pairwise disjoint. A change thus adds or removes exactly "
                        + "that coordinate's multiplicity. For unit multiplicities the absolute "
                        + "counting difference is at most one, so a bounded error in a two-term "
                        + "counting law stays bounded.")),
                    Paragraph(Text(
                        "The counting functions both use a closed cutoff. At the left endpoint "
                        + "one choice may enter it, and at the right endpoint all choices are "
                        + "already counted. Different cutoffs can have different crossing coordinates."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Bound()
    {
        var j = F.Id("j");
        var h = F.Id("h");
        var index = F.Id("J");
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var realFamily = Seq(index, Sp, To, Sp, reals);
        var rj = Call("r", j);
        var upper = new Formula.Fraction(D(1), D(3));
        var radiusBound = Seq(D(0), Lt, rj, Leq, upper);
        var positiveLowerEndpoint = new Formula.Relation(rj, FormulaRelationOperator.LessThan, Call("gamma", j));
        var rad = Bind(FormulaQuantifier.ForAll, "j", index,
            new Formula.Logic(radiusBound, FormulaLogicOperator.And, positiveLowerEndpoint));
        var near = Bind(FormulaQuantifier.ForAll, "j", index,
            AtMost(new Formula.Absolute(Seq(Call("h", j), Minus, Call("gamma", j))), rj));
        var law = Bind(FormulaQuantifier.ForAll, "h", realFamily,
            new Formula.Logic(near, FormulaLogicOperator.Implies, Call("Relocation", h, F.Id("r"))));
        var separated = Call("Separated", F.Id("r"));
        return Disp(Bind(FormulaQuantifier.Exists, "r", realFamily,
            new Formula.Logic(rad, FormulaLogicOperator.And,
                new Formula.Logic(separated, FormulaLogicOperator.And, law))));
    }
}
