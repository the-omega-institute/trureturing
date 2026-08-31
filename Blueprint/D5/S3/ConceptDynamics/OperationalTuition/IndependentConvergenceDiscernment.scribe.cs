using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.OperationalTuition;

internal sealed class IndependentConvergenceDiscernmentDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/OperationalTuition/IndependentConvergenceDiscernment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite independent views have monotone convergence discernment, while same-family "
            + "same-input views contribute zero independent evidence.",
        H("Independent Convergence Discernment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("independent-discernment-is-monotone"),
                DeclarationHandle.Create(Prefix + "independent_discernment_mono"),
                H("Independent convergence discernment is monotone"),
                StatementSource.FromAuthor(MonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite view records its visible input set, model family, and Boolean "
                            + "readout. Independence is the conjunction of disjoint visible inputs "
                            + "and distinct model families.")),
                    Paragraph(Text(
                        "The evidence set contains exactly the visible inputs on which the two "
                            + "readouts disagree. A refinement adds visible inputs and preserves the "
                            + "old readout, so the evidence set is a Finset subset and its cardinality "
                            + "cannot decrease."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("same-family-same-input-discernment-zero"),
                DeclarationHandle.Create(Prefix + "same_family_same_input_discernment_zero"),
                H("Same-family same-input discernment is zero"),
                StatementSource.FromAuthor(DegenerationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The independent evidence value is guarded by the independence predicate. "
                        + "Equal model families (together with equal visible inputs) therefore "
                        + "select the zero branch of the finite value."))),
                DescribeRole.Theorem))));

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);

    private static Formula View(Formula input, Formula family) =>
        Call("FiniteView", input, family);

    private static Formula MonotonicityFormula()
    {
        Formula input = F.Id("I");
        Formula family = F.Id("F");
        Formula coarse = F.Id("coarse");
        Formula fine = F.Id("fine");
        Formula right = F.Id("right");
        Formula hypotheses = Seq(
            Call("ViewRefinement", coarse, fine), Sp, Rightarrow, Sp,
            Call("Independent", coarse, right), Sp, Rightarrow, Sp,
            Call("Independent", fine, right));
        Formula conclusion = Seq(
            Call("discernmentPower", coarse, right), Sp, Le, Sp,
            Call("discernmentPower", fine, right));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, input, Comma, Sp, family, Colon, Sp, F.Id("Type"), Comma),
            Seq(Grp(), Typeclass("DecidableEq", input), Comma,
                Sp, Typeclass("DecidableEq", family), Comma),
            Seq(coarse, Comma, Sp, fine, Comma, Sp, right, Colon, Sp,
                View(input, family), Comma),
            Seq(hypotheses, Sp, Rightarrow, Sp, conclusion, Dot),
        ]));
    }

    private static Formula DegenerationFormula()
    {
        Formula input = F.Id("I");
        Formula family = F.Id("F");
        Formula left = F.Id("left");
        Formula right = F.Id("right");
        Formula hypotheses = Call("SameFamilySameInput", left, right);
        Formula conclusion = Seq(
            Call("discernmentPower", left, right), Sp, Eq, Sp, D(0));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, input, Comma, Sp, family, Colon, Sp, F.Id("Type"), Comma),
            Seq(Grp(), Typeclass("DecidableEq", input), Comma,
                Sp, Typeclass("DecidableEq", family), Comma),
            Seq(left, Comma, Sp, right, Colon, Sp, View(input, family), Comma),
            Seq(hypotheses, Sp, Rightarrow, Sp, conclusion, Dot),
        ]));
    }
}
