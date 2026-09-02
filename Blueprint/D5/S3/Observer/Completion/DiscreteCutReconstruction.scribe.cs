using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class DiscreteCutReconstructionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/DiscreteCutReconstruction."
            + "discrete_cut_reconstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All rational binary cuts reconstruct a real parameter, while every finite selection "
            + "leaves a distinct compatible parameter.",
        H("Discrete Cut Reconstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("discrete-cut-reconstruction"),
            DeclarationHandle.Create(Declaration),
            H("The complete rational cut profile reconstructs its real parameter"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a real x and rational q, the binary name is the decidable truth value "
                        + "of q < x. The supremum clause uses exactly the rational casts whose "
                        + "binary names are true, so the reconstruction is attached to the "
                        + "source threshold semantics rather than to an abstract code.")),
                Paragraph(Text(
                    "A single cutoff cannot identify x. More generally, for any finite set of "
                        + "cutoffs, the proof constructs a distinct y below x with all selected "
                        + "readouts unchanged. If some selected cutoff lies below x, y is chosen "
                        + "between x and the largest such cutoff; otherwise x minus one works.")),
                Paragraph(Text(
                    "The final two implications state compatibility with rational order: a true "
                        + "readout propagates to every lower cutoff, and a false readout propagates "
                        + "to every higher cutoff. Pinned Mathlib supplies rational density and "
                        + "the conditional-completeness supremum bridge, but no whole theorem."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula MemberOf(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula DecideLess(Formula left, Formula right) =>
        Call("decide", LessThan(left, right));

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula rational = Seq(Mathbb, Grp(F.Id("Q")));
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula cuts = F.Id("cuts");
        Formula trueValue = F.Id("true");
        Formula falseValue = F.Id("false");

        Formula rationalCast = Seq(Open, q, Sp, Colon, Sp, real, Close);
        Formula trueCutSet = Seq(
            Left, OpenBrace, rationalCast, Sp, Mid, Sp,
            q, Sp, InMacro, Sp, rational, Comma, Sp,
            Equal(DecideLess(q, x), trueValue),
            Right, CloseBrace);
        Formula reconstruction = Equal(Call("sSup", trueCutSet), x);

        Formula singleCut = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("q", rational)],
            new Formula.BindMany(
                FormulaQuantifier.Exists,
                [Bound("y", real)],
                And(
                    NotEqual(y, x),
                    Equal(DecideLess(q, x), DecideLess(q, y)))));

        Formula selectedAgreement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("q", rational)],
            Implies(
                MemberOf(q, cuts),
                Equal(DecideLess(q, x), DecideLess(q, y))));
        Formula finiteCuts = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("cuts", Call("Finset", rational))],
            new Formula.BindMany(
                FormulaQuantifier.Exists,
                [Bound("y", real)],
                And(NotEqual(y, x), selectedAgreement)));

        Formula trueDownward = Implies(
            Equal(DecideLess(q, x), trueValue),
            Equal(DecideLess(p, x), trueValue));
        Formula falseUpward = Implies(
            Equal(DecideLess(p, x), falseValue),
            Equal(DecideLess(q, x), falseValue));
        Formula compatibility = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("p", rational), Bound("q", rational)],
            Implies(
                LessThanOrEqual(p, q),
                And(trueDownward, falseUpward)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", real)],
            And(
                reconstruction,
                And(singleCut, And(finiteCuts, compatibility)))));
    }
}
