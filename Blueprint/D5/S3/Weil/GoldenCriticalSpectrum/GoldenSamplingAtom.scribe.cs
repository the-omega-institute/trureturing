using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GoldenCriticalSpectrum;

internal sealed class GoldenSamplingAtomDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/GoldenCriticalSpectrum/GoldenSamplingAtom.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden negative-time sampling gives damped complex atoms inside the unit disk, with the birth boundary exactly on the unit circle.",
        H("Golden Sampling Atom"),
        Blocks(
            Theorem("golden-sampling-atom-modulus-and-location",
                "golden_sampling_atom_modulus_and_location",
                "Golden Sampling Locates Damped Modes in the Unit Disk", MainFormula(),
                "The sampled atom has exact radius phi raised to minus twice its height, independently of its phase frequency.",
                "Its radius is one exactly at height zero, while every positive height gives strict unit-disk membership."),
            Theorem("golden-sampling-atom-inside-witness",
                "golden_sampling_atom_inside_witness",
                "Height One Gives a Strict Interior Atom", InsideWitnessFormula(),
                "At frequency zero and height one, the atom has exact radius phi to the power minus two.",
                "The same calculation proves that this concrete radius is strictly less than one."),
            Theorem("golden-sampling-atom-boundary-counterexample",
                "golden_sampling_atom_boundary_counterexample",
                "Height Zero Refutes the Strict Interior Conclusion", BoundaryFormula(),
                "At frequency zero and height zero, the atom has norm exactly one.",
                "This concrete boundary value violates the positive-height premise and makes the strict unit-disk conclusion false."))));

    private static DocumentBlock.Describe Theorem(string id, string declaration,
        string heading, Formula formula, string firstParagraph, string secondParagraph) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(firstParagraph)), Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

    private static Formula MainFormula()
    {
        Formula gamma = F.Id("gamma");
        Formula height = F.Id("h");
        Formula norm = Norm(Atom(gamma, height));
        Formula exactRadius = Seq(norm, Sp, Eq, Sp, GoldenPower(height));
        Formula boundary = Equivalence(
            Seq(norm, Sp, Eq, Sp, D(1)),
            Seq(height, Sp, Eq, Sp, D(0)));
        Formula interior = Implication(
            Seq(D(0), Sp, Lt, Sp, height),
            Seq(norm, Sp, Lt, Sp, D(1)));
        return Statement([Typed(gamma, Reals()), Typed(height, Reals())],
            Conjunction(exactRadius, Conjunction(boundary, interior)));
    }

    private static Formula InsideWitnessFormula()
    {
        Formula norm = Norm(Atom(D(0), D(1)));
        Formula exactRadius = Seq(norm, Sp, Eq, Sp, GoldenPower(D(1)));
        Formula interior = Seq(norm, Sp, Lt, Sp, D(1));
        return Statement([], Conjunction(exactRadius, interior));
    }

    private static Formula BoundaryFormula()
    {
        Formula norm = Norm(Atom(D(0), D(0)));
        Formula unit = Seq(norm, Sp, Eq, Sp, D(1));
        Formula notInterior = new Formula.Not(Seq(norm, Sp, Lt, Sp, D(1)));
        return Statement([], Conjunction(unit, notInterior));
    }

    private static Formula Atom(Formula gamma, Formula height) =>
        Call("goldenSamplingAtom", gamma, height);

    private static Formula Norm(Formula value) => new Formula.Norm(value);

    private static Formula GoldenPower(Formula height) => Seq(
        F.Id("Real"), Dot, F.Id("goldenRatio"), Caret,
        Grp(Seq(Minus, D(2), Sp, Times, Sp, height)));

    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Open, premise, Close, Sp, Rightarrow, Sp, Open, conclusion, Close);

    private static Formula Equivalence(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Leftrightarrow, Sp, Open, right, Close);

    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Land, Sp, Open, right, Close);

    private static Formula Statement(Formula[] binders, Formula conclusion)
    {
        List<Formula> items = [];
        if (binders.Length > 0)
        {
            items.Add(Forall); items.Add(Sp);
            for (int index = 0; index < binders.Length; index++)
            {
                if (index > 0) { items.Add(Comma); items.Add(Sp); }
                items.Add(binders[index]);
            }
            items.Add(Comma); items.Add(RowBreak); items.Add(Grp());
        }
        items.Add(Seq(Open, conclusion, Close)); items.Add(Dot);
        return Disp(Seq([.. items]));
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
