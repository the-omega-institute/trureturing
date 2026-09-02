using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class UniversalNormalizedSaturationCellDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/Pick/UniversalNormalizedSaturationCell."
            + "universal_normalized_saturation_cell";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every normalized unit-phase contact gives one universal two-point Pick cell.",
        H("Universal Normalized Saturation Cell"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("universal-normalized-saturation-cell"),
                DeclarationHandle.Create(Declaration),
                H("The normalized cell is independent of its source data"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The candidate and contact-point families are indexed by zero height, "
                            + "offline distance, multiplicity, completed function, and unit "
                            + "contact phase. This makes every stated independence parameter "
                            + "visible in the theorem.")),
                    Paragraph(Text(
                        "For every index tuple, the candidate is zero at the origin and takes "
                            + "the selected phase at its selected interior point. The displayed "
                            + "Pick kernel and two-point relation are the source constructions.")),
                    Paragraph(Text(
                        "The relation is always the matrix with rows (1,1) and (1,0), and it is "
                            + "not positive semidefinite."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula natural = Call("Nat");
        Formula complex = Call("Complex");
        Formula circle = Call("Circle");
        Formula disk = Call("UnitDisc");
        Formula complexFunction = Arrow(complex, complex);
        Formula schurFamily = Arrow(
            real,
            Arrow(real, Arrow(natural,
                Arrow(complexFunction, Arrow(circle, complexFunction)))));
        Formula pointFamily = Arrow(
            real,
            Arrow(real, Arrow(natural,
                Arrow(complexFunction, Arrow(circle, disk)))));

        Formula candidate = F.Id("S");
        Formula contactPoint = F.Id("A");
        Formula zeroHeight = F.Id("h");
        Formula offlineDistance = F.Id("d");
        Formula multiplicity = F.Id("m");
        Formula completion = F.Id("Xi");
        Formula phase = F.Id("u");
        Formula schur = F.Id("s");
        Formula point = F.Id("a");
        Formula z = F.Id("z");
        Formula w = F.Id("w");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula kernel = F.Id("K");
        Formula points = F.Id("p");
        Formula relation = F.Id("R");

        Formula.BoundVariable[] sourceVariables =
        [
            Bound("h", real),
            Bound("d", real),
            Bound("m", natural),
            Bound("Xi", complexFunction),
            Bound("u", circle),
        ];

        Formula CandidateAt(params Formula[] tail) => Apply(
            candidate,
            zeroHeight,
            offlineDistance,
            multiplicity,
            completion,
            phase,
            tail[0]);
        Formula PointAt() => Apply(
            contactPoint,
            zeroHeight,
            offlineDistance,
            multiplicity,
            completion,
            phase);

        Formula zeroLaw = ForAll(
            sourceVariables,
            Equal(CandidateAt(D(0)), D(0)));
        Formula contactLaw = ForAll(
            sourceVariables,
            Equal(CandidateAt(PointAt()), phase));

        Formula kernelBody = new Formula.Fraction(
            Seq(D(1), Sp, Minus, Sp,
                Apply(schur, z), Sp, Times, Sp, Conjugate(Apply(schur, w))),
            Seq(D(1), Sp, Minus, Sp, z, Sp, Times, Sp, Conjugate(w)));
        Formula kernelDefinition = Seq(
            Open, z, Comma, Sp, w, Sp, Mapsto, Sp, kernelBody, Close);
        Formula relationDefinition = Seq(
            Open, i, Comma, Sp, j, Sp, Mapsto, Sp,
            Call("K", Call("p", i), Call("p", j)), Close);
        Formula result = And(
            Equal(relation, Call("matrix", D(1), D(1), D(1), D(0))),
            new Formula.Not(Call("PosSemidef", relation)));
        Formula sourceConclusion = Seq(
            Operatorname, Grp(F.Id("let")), Open,
            schur, Sp, Colon, Eq, Sp,
            Apply(candidate, zeroHeight, offlineDistance, multiplicity, completion, phase),
            Comma, Sp,
            point, Sp, Colon, Eq, Sp, PointAt(), Comma, Sp,
            kernel, Sp, Colon, Eq, Sp, kernelDefinition, Comma, Sp,
            points, Sp, Colon, Eq, Sp, Call("vector", D(0), point), Comma, Sp,
            relation, Sp, Colon, Eq, Sp, relationDefinition,
            Close, SemiSpace, result);

        return Disp(ForAll(
            [Bound("S", schurFamily), Bound("A", pointFamily)],
            Implies(
                And(zeroLaw, contactLaw),
                ForAll(sourceVariables, sourceConclusion))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Conjugate(Formula value) => Seq(Overline, Grp(value));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
