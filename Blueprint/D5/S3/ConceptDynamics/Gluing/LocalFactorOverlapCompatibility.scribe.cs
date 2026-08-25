using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class LocalFactorOverlapCompatibilityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Gluing/LocalFactorOverlapCompatibility."
            + "local_factor_overlap_compatibility";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local factors of one target through a surjective readout agree on every "
            + "overlap of their exact local domains.",
        H("Local Factor Overlap Compatibility"),
        Blocks(Describe.Lean(
            DescribeId.Create("local-factor-overlap-compatibility"),
            DeclarationHandle.Create(Declaration),
            H("Local factors automatically agree on overlaps"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each local factor is defined on the subtype of base points belonging "
                        + "to its own domain, matching the source carrier rather than extending "
                        + "the function arbitrarily to the whole base.")),
                Paragraph(Text(
                    "For an overlap point b, surjectivity supplies x with q(x)=b. Both local "
                        + "factorization equations then identify their respective values at b "
                        + "with the same target value T(x).")),
                Paragraph(Text(
                    "Openness, cover-totality, and continuity are not used by this algebraic "
                        + "compatibility step; they belong to subsequent topological gluing. "
                        + "Repository and pinned-library searches found no exact theorem on "
                        + "the dependent local-domain carrier."))),
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
        Formula domain = F.Id("U");
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        Formula local = F.Id("f");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula x = F.Id("x");
        Formula b = F.Id("b");
        Formula proposition = Call("Prop");
        Formula domainType = Arrow(baseType, proposition);
        Formula localDomainType = Call("Subtype", Apply(domain, i));
        Formula localFamilyType = Seq(
            Forall, Sp, i, Colon, Sp, indexType, Comma, Sp,
            localDomainType, Sp, To, Sp, targetType);

        Formula localFactorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("x", stateType)],
            Implies(
                Call("mem", Apply(readout, x), Apply(domain, i)),
                EqualTo(Apply(target, x),
                    Call("localApply", local, i, Apply(readout, x)))));
        Formula hypotheses = And(Call("Surjective", readout), localFactorization);
        Formula overlapCompatibility = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("j", indexType), Bound("b", baseType)],
            Implies(
                And(Call("mem", b, Apply(domain, i)),
                    Call("mem", b, Apply(domain, j))),
                EqualTo(Call("localApply", local, i, b),
                    Call("localApply", local, j, b))));
        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", type), Bound("X", type), Bound("B", type), Bound("Y", type),
                Bound("q", Arrow(stateType, baseType)),
                Bound("T", Arrow(stateType, targetType)),
                Bound("U", Arrow(indexType, domainType)),
                Bound("f", localFamilyType),
            ],
            Implies(hypotheses, overlapCompatibility));

        return Disp(theorem);
    }
}
