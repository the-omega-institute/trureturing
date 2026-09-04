using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class CanonicalStrongestSeparatingObserverDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/CanonicalStrongestSeparatingObserver."
            + "canonical_strongest_separating_observer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized orthogonal residual is the canonical strongest separating observer.",
        H("Canonical Strongest Separating Observer"),
        Blocks(Describe.Lean(
            DescribeId.Create("canonical-strongest-separating-observer"),
            DeclarationHandle.Create(Declaration),
            H("Optimal residual readout and its exact maximizers"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let M be a closed subspace of a real Hilbert space, let x be a target, "
                        + "and let r be the orthogonal projection of x onto the orthogonal "
                        + "complement of M. Assume r is nonzero.")),
                Paragraph(Text(
                    "The supremum of the absolute readout over observers in the orthogonal "
                        + "unit ball is the norm of r, and both signs of the normalized residual "
                        + "attain it.")),
                Paragraph(Text(
                    "These are the only absolute-value maximizers. After requiring positive "
                        + "alignment, the normalized residual is the unique maximizer. This "
                        + "corrects the source's false uniqueness claim for an absolute objective."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula EqualFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula TheoremFormula()
    {
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula hilbert = F.Id("H");
        Formula subspace = F.Id("M");
        Formula target = F.Id("x");
        Formula observer = F.Id("g");
        Formula residual = Call("proj", Call("orthogonalComplement", subspace), target);
        Formula residualNorm = new Formula.Norm(residual);
        Formula normalized = Seq(residual, Sp, Slash, Sp, residualNorm);
        Formula readout = Call("inner", observer, target);
        Formula feasible = And(
            Seq(observer, InMacro, Sp, Call("orthogonalComplement", subspace)),
            Seq(new Formula.Norm(observer), Sp, Leq, Sp, D(1)));
        Formula supremum = Seq(
            Operatorname, Grp(F.Id("sup")), Underscore,
            Grp(observer, Colon, Sp, feasible), Sp,
            Grp(Seq(Vert, readout, Vert)));
        Formula absoluteMaximizers = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("g", hilbert)],
            Implies(
                feasible,
                new Formula.Logic(
                    EqualFormula(Seq(Vert, readout, Vert), residualNorm),
                    FormulaLogicOperator.Iff,
                    new Formula.Logic(
                        EqualFormula(observer, normalized),
                        FormulaLogicOperator.Or,
                        EqualFormula(observer, Seq(Minus, normalized))))));
        Formula positiveUnique = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("g", hilbert)],
            Implies(
                And(feasible, EqualFormula(readout, residualNorm)),
                EqualFormula(observer, normalized)));
        Formula conclusion = And(
            EqualFormula(supremum, residualNorm),
            And(absoluteMaximizers, positiveUnique));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("H", Call("RealHilbertSpace")),
                Bound("M", Call("ClosedSubspace", hilbert)),
                Bound("x", hilbert),
            ],
            Implies(
                Seq(residual, Sp, Neq, Sp, D(0)),
                conclusion)));
    }
}
