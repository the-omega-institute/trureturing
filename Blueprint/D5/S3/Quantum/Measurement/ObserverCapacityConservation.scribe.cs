using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class ObserverCapacityConservationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/ObserverCapacityConservation."
            + "observer_capacity_conservation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional quantum observer capacity and invisible residual conserve the "
            + "traceless Hermitian dimension under information refinement.",
        H("Quantum Observer Capacity Conservation"),
        Blocks(Describe.Lean(
            DescribeId.Create("quantum-observer-capacity-conservation"),
            DeclarationHandle.Create(Declaration),
            H("Capacity and residual conserve dimension under refinement"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "An observer effect family generates the real span of the identity and "
                        + "its effects inside the canonical Hermitian matrix carrier. Capacity "
                        + "is that visible dimension minus the identity direction, and the "
                        + "residual is the orthogonal-complement dimension.")),
                Paragraph(Text(
                    "The Hermitian carrier has real dimension d squared. Orthogonal dimension "
                        + "splitting and the visible identity line therefore give capacity plus "
                        + "residual equal to d squared minus one.")),
                Paragraph(Text(
                    "Including one effect family in another includes their visible spans. "
                        + "Finite-dimensional rank is monotone under that inclusion, while "
                        + "orthogonal complementation reverses it, proving both progress "
                        + "inequalities."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula TheoremFormula()
    {
        Formula natural = F.Id("Nat");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula d = F.Id("d");
        Formula effects = F.Id("E");
        Formula coarse = F.Id("E1");
        Formula fine = F.Id("E2");
        Formula carrier = Call("HermitianSpace", d);
        Formula effectSet = Call("Set", carrier);
        Formula identity = Call("identityHermitian", d);
        Formula dimension = Seq(d, Sp, Caret, Grp(D(2)), Sp, Minus, Sp, D(1));
        Formula Visible(Formula family) =>
            Call("span", real, Call("insert", identity, family));
        Formula Capacity(Formula family) => Seq(
            Call("finrank", real, Visible(family)), Sp, Minus, Sp, D(1));
        Formula Residual(Formula family) =>
            Call("finrank", real, Call("orthogonal", Visible(family)));
        Formula conservation = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("E"),
            effectSet,
            Equal(
                Seq(Capacity(effects), Sp, Plus, Sp, Residual(effects)),
                dimension));
        Formula refinement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("E1"), effectSet),
                new Formula.BoundVariable(FormulaIdentifier.Create("E2"), effectSet),
            ],
            Implies(
                Seq(coarse, Sp, Subseteq, Sp, fine),
                And(
                    LessEqual(Capacity(coarse), Capacity(fine)),
                    LessEqual(Residual(fine), Residual(coarse)))));
        Formula clauses = And(conservation, refinement);

        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            natural,
            Implies(
                new Formula.Relation(d, FormulaRelationOperator.NotEqual, D(0)),
                clauses)));
    }
}
