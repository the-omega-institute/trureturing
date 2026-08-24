using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Disclosure;

internal sealed class SensitiveLeakageMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joining a fixed sensitive readout preserves concept refinement.",
        H("Sensitive Leakage Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("sensitive-leakage-is-monotone-under-refinement"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Disclosure/SensitiveLeakageMonotonicity."
                    + "sensitive_leakage_monotone"),
            H("Sensitive leakage is monotone under refinement"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The current, refined, and sensitive readouts are independent public "
                        + "parameters. The premise says that the current readout factors "
                        + "through the refined one.")),
                Paragraph(Text(
                    "Both leakage objects are constructed with the canonical joint readout. "
                        + "The frozen augmentation law preserves the refinement while carrying "
                        + "the same sensitive coordinate on both sides."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula currentType = F.Id("A");
        Formula refinedType = F.Id("B");
        Formula sensitiveType = F.Id("K");
        Formula current = F.Id("C");
        Formula refined = F.Id("D");
        Formula sensitive = F.Id("S");
        Formula universe = Seq(Operatorname, Grp(F.Id("Type")));
        Formula currentJoin = Call("conceptJoin", current, sensitive);
        Formula refinedJoin = Call("conceptJoin", refined, sensitive);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", universe),
                Bound("A", universe),
                Bound("B", universe),
                Bound("K", universe),
                Bound("C", new Formula.TypeArrow(state, currentType)),
                Bound("D", new Formula.TypeArrow(state, refinedType)),
                Bound("S", new Formula.TypeArrow(state, sensitiveType)),
            ],
            new Formula.Logic(
                Call("Refines", current, refined),
                FormulaLogicOperator.Implies,
                Call("Refines", currentJoin, refinedJoin))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
