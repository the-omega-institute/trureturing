using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class ContinuousLocalFactorGluingDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible continuous local factors glue uniquely and factor the target globally.",
        H("Continuous Local Factor Gluing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("continuous-local-factors-glue-uniquely"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Gluing/ContinuousLocalFactorGluing."
                        + "continuous_local_factors_glue_uniquely"),
                H("Continuous local factors glue uniquely"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The local factors are continuous maps on the exact cover subtypes. "
                            + "Surjectivity and the shared target factorization invoke the frozen "
                            + "overlap theorem, giving equality on every pairwise intersection.")),
                    Paragraph(Text(
                        "The domains are publicly open and cover the base. Mathlib's canonical "
                            + "continuous-map lift therefore glues the local maps, and its "
                            + "computation rule states that the global map restricts to each "
                            + "local factor.")),
                    Paragraph(Text(
                        "Cover membership proves uniqueness pointwise. Applying the same local "
                            + "computation rule at q(x), together with the supplied local "
                            + "factorization equation, proves the public identity T = f composed "
                            + "with q."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula baseType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        Formula domain = F.Id("U");
        Formula local = F.Id("f");
        Formula global = F.Id("g");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula x = F.Id("x");
        Formula b = F.Id("b");
        Formula proposition = Call("Prop");
        Formula domainType = Arrow(baseType, proposition);
        Formula localDomain = Call("Subtype", Apply(domain, i));
        Formula localFamilyType = Seq(
            Forall, Sp, i, Colon, Sp, indexType, Comma, Sp,
            Call("ContinuousMap", localDomain, targetType));
        Formula topologies = And(
            Call("TopologicalSpace", baseType),
            Call("TopologicalSpace", targetType));
        Formula openDomains = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            Call("IsOpen", Apply(domain, i)));
        Formula covers = EqualTo(Call("iUnion", domain), Call("univ", baseType));
        Formula factors = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("x", stateType)],
            Implies(
                Call("mem", Apply(readout, x), Apply(domain, i)),
                EqualTo(
                    Apply(target, x),
                    Call("localApply", local, i, Apply(readout, x)))));
        Formula premises = And(
            topologies,
            And(
                openDomains,
                And(
                    covers,
                    And(Call("Surjective", readout), factors))));
        Formula overlap = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("j", indexType), Bound("b", baseType)],
            Implies(
                And(
                    Call("mem", b, Apply(domain, i)),
                    Call("mem", b, Apply(domain, j))),
                EqualTo(
                    Call("localApply", local, i, b),
                    Call("localApply", local, j, b))));
        Formula restrictions = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("b", baseType)],
            Implies(
                Call("mem", b, Apply(domain, i)),
                EqualTo(Apply(global, b), Call("localApply", local, i, b))));
        Formula globalProperty = And(
            restrictions,
            EqualTo(target, Call("compose", global, readout)));
        Formula uniqueGlue = Seq(
            Exists, Bang, Sp, global, Colon, Sp,
            Call("ContinuousMap", baseType, targetType), Comma, Sp,
            globalProperty);
        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", type), Bound("X", type), Bound("B", type), Bound("Y", type),
                Bound("q", Arrow(stateType, baseType)),
                Bound("T", Arrow(stateType, targetType)),
                Bound("U", Arrow(indexType, domainType)),
                Bound("f", localFamilyType),
            ],
            Implies(premises, And(overlap, uniqueGlue)));

        return Disp(theorem);
    }
}
