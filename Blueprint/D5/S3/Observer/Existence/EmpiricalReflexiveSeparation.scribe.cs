using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Existence;

internal sealed class EmpiricalReflexiveSeparationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Existence/EmpiricalReflexiveSeparation."
            + "empirical_complete_reflexive_incomplete";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete quantum-state readout does not make internal self-evaluation exhaustive.",
        H("Empirical and Reflexive Completeness Separate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("empirical-completeness-does-not-imply-reflexive-completeness"),
                DeclarationHandle.Create(Declaration),
                H("Empirical completeness coexists with reflexive incompleteness"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is a three-context rank-one qubit observer whose projector-trace "
                            + "readout is injective on the canonical carrier of positive, trace-one "
                            + "qubit density states. This is the public current-state reconstruction "
                            + "clause.")),
                    Paragraph(Text(
                        "For every Boolean evaluation table indexed twice by that same density-state "
                            + "carrier, the function obtained by negating the table on its diagonal "
                            + "is outside the table's range. This is exactly the public internal "
                            + "self-evaluation non-capture clause.")),
                    Paragraph(Text(
                        "The concrete witness uses the three standard mutually unbiased qubit bases. "
                            + "The proof then applies the repository's complete-context tomography "
                            + "and fixed-point-free Lawvere escape theorems."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula two = D(2);
        Formula three = D(3);
        Formula boolType = F.Id("Bool");
        Formula qubitIndex = Call("Fin", two);
        Formula densityState = Call("DensityState", qubitIndex);
        Formula context = F.Id("context");
        Formula evaluation = F.Id("evaluation");
        Formula state = F.Id("state");
        Formula rho = F.Id("rho");
        Formula readout = Seq(
            Open, rho, Colon, Sp, densityState, Sp, Mapsto, Sp,
            Call("contextReadout", context, Call("matrix", rho)), Close);
        Formula diagonal = Seq(
            Open, state, Sp, Mapsto, Sp,
            Call("not", Call("evaluation", state, state)), Close);
        Formula nonCapture = new Formula.Not(new Formula.Relation(
            diagonal,
            FormulaRelationOperator.MemberOf,
            Call("range", evaluation)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("context", Arrow(Call("Fin", three), Call("RankOneContext", two)))],
            And(
                Call("Injective", readout),
                new Formula.BindMany(
                    FormulaQuantifier.ForAll,
                    [Bound("evaluation",
                        Arrow(densityState, Arrow(densityState, boolType)))],
                    nonCapture))));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
